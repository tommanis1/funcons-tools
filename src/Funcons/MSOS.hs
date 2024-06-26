{-# LANGUAGE LambdaCase, OverloadedStrings, Rank2Types, TupleSections   
             , FlexibleInstances, ScopedTypeVariables #-}

module Funcons.MSOS (
  liftInnerAndOuterRewrite,rewritten', concatInside, all_randomRemove,
    -- * Making steps
    MSOS(..), Rewrite(..), liftRewrite, rewrite_rethrow, rewrite_throw, eval_catch, msos_throw, 
        EvalFunction(..), Strictness(..), StrictFuncon, PartiallyStrictFuncon, 
            NonStrictFuncon, ValueOp, NullaryFuncon, RewriteState(..),
            StepRes, toStepRes,
        -- ** Entity-types
        Output, readOuts, 
        Mutable, 
        Inherited, giveINH, 
        Control, singleCTRL, giveCTRL, 
        Input,
            -- ** IMSOS helpers
            applyFuncon, rewritten, rewriteTo, rewriteSeqTo, stepTo, stepSeqTo,rewrittens,rewriteTo',
                compstep,
                norule, exception, sortErr, partialOp, internal, buildStep, sidecond,
            -- *** Congruence rules
            premiseStepApp, premiseStep, premiseEval,
        -- ** Pattern Matching
        SeqSortOp(..),
                        rewriteRules, stepRules, evalRules, MSOSState(..), emptyMSOSState, emptyRewriteState, MSOSReader(..),RewriteReader(..),showIException, MSOSWriter(..), RewriteWriterr(..),
    -- * Evaluation funcons TODO internal usage only (by Funcons.Tools)
        Rewritten(..), rewriteFuncons, rewriteFunconsWcount, evalFuncons
          , stepTrans, stepAndOutput, rewritesToValue, rewritesToValues, rewritesToType
          , emptyDCTRL, emptyINH, Interactive(..), SimIO(..)
          , rewriteToValErr, count_delegation, optRefocus
          , evalStrictSequence, rewriteStrictSequence, evalSequence, evalSequence',evalStrictSequence'
          , maybe_randomSelect, maybe_randomRemove, convertMSOS, convert,
    -- * Values
        showTypes, showSorts, showValues, showValuesSeq, showFuncons, showFunconsSeq,traceLib,
    -- * Funcon libraries
    FunconLibrary, libUnions, libOverrides, libEmpty, libUnion, libOverride, Funcons.MSOS.libFromList,
    evalctxt2exception, ctxt2exception, fromNullaryValOp, fromAbsValOp, fromValOp, fromSeqValOp,
    -- * Counters
    displayCounters, counterKeys, ppCounters,
    )where


import Funcons.Types
import Funcons.RunOptions
import Funcons.Printer
import Funcons.Exceptions
import Funcons.Simulation
import qualified Funcons.Operations as VAL

import Control.Applicative
import Control.Arrow ((***))
import Control.Monad.Writer hiding ((<>))
import Control.Monad.Fail
import Data.Function (on)
import Data.Maybe (isJust, isNothing, fromJust)
import Data.List (foldl', intercalate, partition, sortBy)
import Data.Text (unpack)
import Data.Semigroup

import qualified Data.Map as M

import System.Random
import System.IO.Unsafe

--trace p b = unsafePerformIO (putStrLn p >> return b) 
trace p b = b
traceLib :: FunconLibrary -> FunconLibrary
traceLib lib = unsafePerformIO 
  (putStrLn (unlines (map unpack (M.keys lib))) >> return lib)


---------------------------------------------------------------------
-- | A funcon library maps funcon names to their evaluation functions.
type FunconLibrary = M.Map Name EvalFunction

fromValOp = fromAbsValOp False
fromSeqValOp = fromAbsValOp True
fromAbsValOp :: Bool -> ([Funcons] -> Funcons) -> ([OpExpr Funcons] -> OpExpr Funcons) -> EvalFunction
fromAbsValOp seqRes cons mkExpr = ValueOp (\x -> convert $ op x )
 where op vs = report f seqRes (VAL.eval (mkExpr (map ValExpr vs))) 
        where f = cons (map FValue vs)
fromNullaryValOp :: ([Funcons] -> Funcons) -> ([OpExpr Funcons] -> OpExpr Funcons) -> EvalFunction
fromNullaryValOp cons mkExpr = NullaryFuncon (convert $ op)
  where op = report (cons []) False (VAL.eval (mkExpr []))

convert :: Rewrite [Rewrite a] ->  Rewrite a
convert (Rewrite l) = Rewrite ( \ctxt st ->  

    let (e_a1,st1,cs1) = l ctxt st
    in case e_a1 of 
        Left err  -> (Left err, st1, cs1)
        Right a1 -> do 
          let gen       = random_gen st
              (i, gen') = next gen
              index     = i `mod` (length a1)
          let (Rewrite env) = (a1 !! index)
          env ctxt st
    ) 

report :: Funcons -> Bool -> EvalResult Funcons -> Rewrite [Rewrite Rewritten] 
report f seqRes res = case res of
  Error _ dres                -> reportResult dres
  Success (FValue (ADTVal "null" _)) -> rewrittens []
  Success (FValue v)          -> rewritten' v
  Success t                   -> rewriteFuncons t
  EvalResults ress            -> maybe_randomSelect NDValueOperations ress >>= 
                                  report f seqRes 
  where rewritten' v | seqRes, ValSeq fs <- v, 
                        let mvs = map project fs, all isJust mvs
                        = rewrittens (map fromJust mvs)
                     | otherwise = rewritten v
        reportResult dres = case dres of 
          (VAL.SortErr str)   -> sortErr f str
          (DomErr str)        -> rewrittens [] 
          (ArityErr str)      -> sortErr f str
          (ProjErr str)       -> sortErr f str
          (Normal (FValue v)) -> rewritten' v
          (Normal t)          -> rewriteFuncons t
          (Nondeterministic ress) -> case ress of 
            []    -> sortErr f "nondeterminism: empty"
            _     -> randomSelect ress >>= reportResult

-- |
-- Evaluation functions capture the operational behaviour of a funcon.
-- Evaluation functions come in multiple flavours, each with a different
-- treatment of the arguments of the funcon.
-- Before the application of an evaluation funcon, any argument may be
-- evaluated, depending on the 'Strictness' of the argument.
data EvalFunction   = 
                    -- | Funcons for which arguments are /not/ evaluated.
                      NonStrictFuncon NonStrictFuncon 
                    -- | Strict funcons whose arguments are evaluated.
                    | StrictFuncon StrictFuncon
                    -- | Funcons for which /some/ arguments are evaluated.
                    | PartiallyStrictFuncon [Strictness] Strictness NonStrictFuncon
                    -- | Synonym for 'StrictFuncon', for value operations.
                    | ValueOp ValueOp
                    -- | Funcons without any arguments.
                    | NullaryFuncon NullaryFuncon
-- | Type synonym for the evaluation function of strict funcons.
-- The evaluation function of a 'StrictFuncon' receives fully evaluated arguments.
type StrictFuncon           = [Values] -> Rewrite Rewritten
-- | Type synonym for the evaluation function of fully non-strict funcons.
type NonStrictFuncon        = [Funcons] -> Rewrite Rewritten
-- | Type synonym for the evaluation function of non-strict funcons.
type PartiallyStrictFuncon  = NonStrictFuncon 
-- | Type synonym for value operations.
type ValueOp                = StrictFuncon
-- | Type synonym for the evaluation functions of nullary funcons.
type NullaryFuncon          = Rewrite Rewritten
-- | Denotes whether an argument of a funcon should be evaluated or not.
data Strictness             = Strict | NonStrict

-- | After a term is fully rewritten it is either a value or a 
-- term that requires a computational step to proceed.
-- This types forms the interface between syntactic rewrites and 
-- computational steps.
data Rewritten = 
    -- | Fully rewritten to a value.
    ValTerm [Values]
    -- | Fully rewritten to a term and the step required to continue evaluation.
    | CompTerm Funcons (MSOS StepRes)

-- | A single step on a funcon term produces either a funcon term 
-- or a (possibly empty or unary) sequence of values
type StepRes = Either Funcons [Values]

instance Show Rewritten where
    show (ValTerm vs) = showValuesSeq vs
    show (CompTerm _ _) = "<step>"

-- | Creates an empty 'FunconLibrary'.
libEmpty :: FunconLibrary
libEmpty = M.empty 

-- | Unites two 'FunconLibrary's.
libUnion :: FunconLibrary -> FunconLibrary -> FunconLibrary
libUnion = M.unionWithKey op
 where op k x _ = error ("duplicate funcon name: " ++ unpack k)

-- | Right-based union of 'FunconLibrary's
libOverride :: FunconLibrary -> FunconLibrary -> FunconLibrary 
libOverride = flip M.union 

-- | Unites a list of 'FunconLibrary's.
libUnions :: [FunconLibrary] -> FunconLibrary
libUnions = foldl' libUnion libEmpty
 where op _ _ = error ("duplicate funcon name")

-- | Right-based union of list of 'FunconLibrary's
libOverrides :: [FunconLibrary] -> FunconLibrary
libOverrides = M.unions . reverse

-- | Creates a 'FunconLibrary' from a list.
libFromList :: [(Name, EvalFunction)] -> FunconLibrary
libFromList = M.fromList

lookupFuncon :: Name -> Rewrite [Rewrite EvalFunction]
lookupFuncon key = Rewrite $ \ctxt st -> 
    (case M.lookup key (funconlib ctxt) of
        Just f -> Right [return f]
        _ -> case M.lookup key (builtin_funcons (run_opts ctxt)) of
               Just f ->  do
                -- TODO, do something with _?
                let (a, _, _) = runRewrite (rewriteTo' f) ctxt st
                -- rewrites <- rewriteTo f
                Right (map (\x -> return $ NullaryFuncon x) (fromRight a ) )
                -- >>= (\l -> map NullaryFuncon l))

                -- Right (map (\rewrite -> NullaryFuncon rewrite) (rewrites))
               _ -> Left (evalctxt2exception (Internal ("unknown funcon: "++ unpack key)) ctxt)
    , st, mempty)

---------------------------------------------------------------------------
data RewriteReader = RewriteReader  
                    { funconlib  :: FunconLibrary    
                    , ty_env     :: TypeRelation, run_opts :: RunOptions
                    , global_fct :: Funcons, local_fct :: Funcons }
data RewriteState = RewriteState { random_gen :: StdGen }
emptyRewriteState = RewriteState (mkStdGen 0)
data RewriteWriterr = RewriteWriterr { counters :: Counters }

-- | Monadic type for the implicit propagation of meta-information on
-- the evaluation of funcon terms (no semantic entities). 
-- It is separated from 'MSOS' to ensure
-- that side-effects (access or modification of semantic entities) can not
-- occur during syntactic rewrites.
newtype Rewrite a= Rewrite {runRewrite :: (RewriteReader -> RewriteState -> 
                    (Either IException a, RewriteState, RewriteWriterr))}

instance Applicative Rewrite where
  pure = return
  (<*>) = ap

instance Functor Rewrite where
  fmap = liftM

instance Monad Rewrite  where
  return a = Rewrite (\_ st -> (Right a, st, mempty))

  (Rewrite f) >>= k = Rewrite (\ctxt st ->
                    let res1@(e_a1,st1,cs1) = f ctxt st
                     in case e_a1 of 
                          Left err  -> (Left err, st1, cs1)
                          Right a1  -> let (Rewrite h) = k a1
                                           (a2,st2,cs2) = h ctxt st1
                                        in (a2,st2,cs1 <> cs2))

instance Semigroup RewriteWriterr where
  (<>) = mappend

instance Monoid RewriteWriterr where
    mempty = RewriteWriterr mempty
    (RewriteWriterr cs1) `mappend` (RewriteWriterr cs2) = RewriteWriterr (cs1 `mappend` cs2)

liftRewrite :: Rewrite a -> MSOS a
liftRewrite ev = MSOS $ \ctxt mut -> 
                let (e_a, est, ewr) = runRewrite ev (ereader ctxt) (estate mut)
                in return (e_a, mut {estate = est}, mempty { ewriter = ewr })

liftInnerAndOuterRewrite :: Rewrite [Rewrite a] -> MSOS [MSOS a]
liftInnerAndOuterRewrite ev = MSOS $ \ctxt mut -> do 
                let (e_a, est, ewr) = runRewrite ev (ereader ctxt) (estate mut)

                -- TODO full pattern match instead of fromRight
                return ((Right $ map liftRewrite $ fromRight e_a), mut {estate = est}, mempty { ewriter = ewr })

fromRight :: Either a b -> b
fromRight (Right a) = a
fromRight _         = error "MSOSfromRight: Left"

eval_catch :: Rewrite a -> Rewrite (Either IException a)
eval_catch eval = Rewrite $ \ctxt st -> 
    let (eval_res, st', eval_cs) = runRewrite eval ctxt st
    in (Right eval_res, st', eval_cs) 

-- TODO rm
-- eval_catch_list :: Rewrite [Rewrite a] -> Rewrite (Either IException [Rewrite a])
-- eval_catch_list eval = Rewrite $ \ctxt st -> 
--     let (eval_res, st', eval_cs) = runRewrite eval ctxt st
--     in (Right eval_res, st', eval_cs) 

eval_else :: (IE -> Bool) -> [Rewrite a] -> Rewrite a -> Rewrite a
eval_else prop [] def = def
eval_else prop (ev:evs) def = eval_catch ev >>= \case
    Right a -> return a
    Left (gf,lf,ie) | prop ie   -> eval_else prop evs def
                    | otherwise -> rewrite_rethrow (gf,lf,ie)

rewrite_rethrow :: IException -> Rewrite a
rewrite_rethrow ie = Rewrite $ \ctxt st -> (Left ie, st, mempty)

rewrite_throw :: IE -> Rewrite a
rewrite_throw ie = Rewrite $ \ctxt st -> (Left (evalctxt2exception ie ctxt), st, mempty)

evalctxt2exception :: IE -> RewriteReader -> IException
evalctxt2exception ie ctxt = (global_fct ctxt, local_fct ctxt, ie)

ctxt2exception :: IE -> MSOSReader m -> IException
ctxt2exception ie ctxt = 
    (global_fct (ereader ctxt), local_fct (ereader ctxt), ie)

rewriteRules = rewriteRules' []
rewriteRules' :: [IException] -> [Rewrite Rewritten] -> Rewrite Rewritten
rewriteRules' errs [] = rewrite_throw (NoMoreBranches errs)
rewriteRules' errs (t1:ts) = Rewrite $ \ctxt st ->  
    let (rw_res, st', rw_cs) = runRewrite t1 ctxt st
    in case rw_res of
        Left ie| failsRule ie -> -- resets state 
                                 trace (showIException ie) $ runRewrite (do
                                  count_backtrack_in
                                  addToRCounter (counters rw_cs)
                                  rewriteRules' (ie:errs) ts) ctxt st 
        _                     -> (rw_res, st', rw_cs)

---------------------------------------------------------------------------
data MSOSReader m = MSOSReader{ ereader :: RewriteReader 
                              , inh_entities :: Inherited
                              , dctrl_entities :: DownControl
                              , def_fread :: Name -> m Funcons}
data MSOSWriter = MSOSWriter { ctrl_entities :: Control, out_entities :: Output
                             , ewriter :: RewriteWriterr }
data MSOSState m = MSOSState { inp_es :: Input m, mut_entities :: Mutable
                             , estate :: RewriteState }
emptyMSOSState :: Int -> MSOSState m
emptyMSOSState seed = 
  MSOSState M.empty M.empty (emptyRewriteState { random_gen = mkStdGen seed })

-- | Monadic type for the propagation of semantic entities and meta-information
-- on the evaluation of funcons. The meta-information includes a library 
-- of funcons (see 'FunconLibrary'), a typing environment (see 'TypeRelation'), 
-- runtime options, etc.
--
-- The semantic entities are divided into five classes:
--
-- * inherited entities, propagated similar to values of a reader monad.
--
-- * mutable entities, propagated similar to values of a state monad.
--
-- * output entities, propagation similar to values of a write monad.
--
-- * control entities, similar to output entities except only a single control /signal/
--      can be emitted at once (signals do not form a monoid).
--
-- * input entities, propagated like values of a state monad, but access like
--  value of a reader monad. This package provides simulated input/outout 
--  and real interaction via the 'IO' monad. See "Funcons.Tools".
--
-- For each entity class a map is propagated, mapping entity names to values.
-- This enables modular access to the entities.
newtype MSOS a = MSOS { runMSOS :: 
                        forall m. Interactive m => 
                        (MSOSReader m -> MSOSState m 
                        -> m (Either IException a, MSOSState m, MSOSWriter)) }

instance Applicative MSOS where
  pure = return
  (<*>) = ap

instance Functor MSOS where
  fmap = liftM

instance Monad MSOS  where
  return a = MSOS (\_ mut -> return (Right a,mut,mempty))

  (MSOS f) >>= k = MSOS (\ctxt mut -> do
                    res1@(e_a1,mut1,wr1) <- f ctxt mut 
                    case e_a1 of 
                      Left err  -> return (Left err, mut1, wr1)
                      Right a1  -> do   
                            let (MSOS h) = k a1
                            (a2,mut2,wr2) <- h ctxt mut1
                            return (a2,mut2,wr1 <> wr2))

instance MonadFail MSOS where
  fail = liftRewrite . internal 

instance Semigroup MSOSWriter where
  (<>) = mappend

instance Monoid MSOSWriter where
    mempty = MSOSWriter mempty mempty mempty
    (MSOSWriter x1 x2 x3) `mappend` (MSOSWriter y1 y2 y3) = 
        MSOSWriter (x1 `unionCTRL` y1) (x2 `unionOUT` y2) (x3 `mappend` y3) 

-- | A map storing the values of /mutable/ entities.
type Mutable      = M.Map Name [Values]

stepRules = stepARules NoMoreBranches count_backtrack_in

stepARules :: ([IException] -> IE) -> Rewrite () -> [IException] -> [MSOS StepRes] -> MSOS StepRes
stepARules fexc _ errs [] = msos_throw (fexc errs)
stepARules fexc counter errs ts = 
 liftRewrite (maybe_randomRemove NDRuleSelection ts) >>= 
  \(t1,ts) -> MSOS $ \ctxt mut -> do 
    (e_ie_a, mut', wr) <- runMSOS t1 ctxt mut 
    case e_ie_a of
        Left ie | failsRule ie -> -- resets input & read/write entities
                                  trace (showIException ie) $ runMSOS (do
                                    liftRewrite counter
                                    addToCounter (counters (ewriter wr))
                                    stepARules fexc counter (errs++[ie]) ts) ctxt mut
        _                      -> return (e_ie_a, mut', wr)

-- | Function 'evalRules' implements a backtracking procedure.
-- It receives two lists of alternatives as arguments, the first
-- containing all rewrite rules of a funcon and the second all step rules.
-- The first successful rule is the only rule fully executed.
-- A rule is /unsuccessful/ if it throws an exception. Some of these
-- exceptions (partial operation, sort error or pattern-match failure)
-- cause the next alternative to be tried. Other exceptions 
-- (different forms of internal errors) will be propagated further.
-- All side-effects of attempting a rule are discarded when a rule turns
-- out not to be applicable.
-- 
-- First all rewrite rules are attempted, therefore avoiding performing
-- a step until it is absolutely necessary. This is a valid strategy
-- as valid (I)MSOS rules can be considered in any order.
--
-- When no rules are successfully executed to completetion a 
-- 'no rule exception' is thrown.
evalRules = evalRules' []
evalRules' :: [IException] -> [Rewrite Rewritten] -> [MSOS StepRes] -> Rewrite Rewritten
evalRules' errs [] msoss = buildStep (stepARules NoRule count_backtrack_out errs msoss)
evalRules' errs rules msoss = 
 maybe_randomRemove NDRuleSelection rules >>= \((Rewrite rw_rules),rest) -> 
  Rewrite $ \ctxt st -> 
    let (rw_res, st', wo) = rw_rules ctxt st
    in case rw_res of
        Left ie | failsRule ie  -> --resets counters and state 
                                   trace (showIException ie) $ runRewrite (do
                                      count_backtrack_out
                                      addToRCounter (counters wo)
                                      evalRules' (ie:errs) rest msoss) ctxt st
        _                       -> (rw_res, st', wo)

msos_throw :: IE -> MSOS b
msos_throw = liftRewrite . rewrite_throw 

---

giveOpts :: Rewrite RunOptions 
giveOpts = Rewrite $ \ctxt mut -> (Right (run_opts ctxt), mut, mempty)

giveINH :: MSOS Inherited
giveINH = MSOS $ \ctxt mut -> return (Right (inh_entities ctxt), mut, mempty)

giveCTRL :: MSOS DownControl 
giveCTRL = MSOS $ \ctxt mut -> return (Right (dctrl_entities ctxt), mut, mempty)

doRefocus :: MSOS Bool
doRefocus = MSOS $ \ctxt mut -> 
    return (Right $ do_refocus (run_opts (ereader ctxt)), mut, mempty)

modifyRewriteCTXT :: (RewriteReader -> RewriteReader) -> Rewrite a -> Rewrite a
modifyRewriteCTXT mod (Rewrite f) = Rewrite (f . mod)

modifyRewriteReader :: (RewriteReader -> RewriteReader) -> MSOS a -> MSOS a
modifyRewriteReader mod (MSOS f) = MSOS (f . mod')
  where mod' ctxt = ctxt { ereader = mod (ereader ctxt) }

maybe_randomRemove :: SourceOfND -> [a] -> Rewrite (a, [a])
maybe_randomRemove _ [] = randomRemove []
maybe_randomRemove src xs@(x:xs') = do
  opts <- giveOpts
  if src `elem` get_nd_sources opts then randomRemove xs
                                    else return (x, xs')

all_randomRemove :: SourceOfND -> [a] -> Rewrite [Rewrite (a, [a])]
all_randomRemove _ [] = return [randomRemove []]
all_randomRemove src xs@(x:xs') = do
  ops <- giveOpts
  if src `elem` get_nd_sources ops then return [ Rewrite $ \_ mut ->  (Right (xs !! i , take i xs ++ drop (i + 1) xs ), mut {random_gen = random_gen mut }, mempty ) | i <- [0 .. length xs - 1]]
                                    else return [return (x, xs')]

-- | Uses the random number generator of Rewrite to randomly select
-- an element of a given list. The element is returned, together
-- with the list from which the element has been removed
-- Raises an internal exception if given an empty list
randomRemove :: [a] -> Rewrite (a, [a])
randomRemove [] = internal "randomRemove: empty list"
randomRemove [x]= return (x, [])
randomRemove xs = Rewrite $ \_ mut -> 
  let gen       = random_gen mut 
      (i, gen') = next gen
      index     = i `mod` (length xs)
      elem      = xs !! index 
      rest      = take index xs ++ drop (index + 1) xs 
  in (Right (elem, rest), mut {random_gen = gen'}, mempty )

maybe_randomSelect src xs = fst <$> maybe_randomRemove src xs
randomSelect xs = fst <$> randomRemove xs

{-
randomSelect :: [a] -> Rewrite a
randomSelect xs = Rewrite $ \_ mut -> 
  let gen       = random_gen mut 
      (_, top)  = genRange gen
      unit      = fromIntegral top / fromIntegral (length xs)
      (i, gen') = next gen
      index     = round (fromIntegral i / unit)
  in (Right (xs !! index), mut {random_gen = gen'}, mempty )
-}

-----------------
-- | a map storing the values of /inherited/ entities.
type Inherited       = M.Map Name [Values]

emptyINH :: Inherited
emptyINH = M.empty 

      
----------
-- | a map storing the values of /control/ entities.
type Control = M.Map Name (Maybe Values)
type DownControl = M.Map Name (Maybe Values)

emptyDCTRL :: DownControl
emptyDCTRL = M.empty

emptyCTRL :: Control
emptyCTRL = M.empty

singleCTRL :: Name -> Values -> Control
singleCTRL k = M.singleton k . Just

unionCTRL = M.unionWithKey (error . err)
 where err key = "Two " ++ unpack key ++ " signals converging!"

-----------
-- | a map storing the values of /output/ entities.
type Output      = M.Map Name [Values]

unionOUT :: Output -> Output -> Output
unionOUT = M.unionWith (++)

emptyOUT :: Output 
emptyOUT = M.empty 

readOuts :: MSOS a -> MSOS (a, Output)
readOuts (MSOS f) = MSOS $ (\ctxt mut -> do 
    (e_a, mut1, wr1) <- f ctxt mut
    case e_a of 
        Left err -> return (Left err, mut1, wr1)
        Right a  -> return (Right (a,(out_entities wr1))
                            , mut1, wr1 { out_entities = mempty}))
-----------
-- | A map storing the values of /input/ entities.
type Input m = M.Map Name ([[Values]], Maybe (m Funcons))

-----------
-- steps, rewrites, restarts, refocus, delegations, backtracking (outer/inner)
data Counters = Counters !Int !Int !Int !Int !Int !Int !Int !Int 

instance Semigroup Counters where
  (<>) = mappend

instance Monoid Counters where
    mempty = Counters 0 0 0 0 0 0 0 0
    (Counters x1 x2 x3 x4 x5 x6 x7 x8) `mappend` (Counters y1 y2 y3 y4 y5 y6 y7 y8) = 
        Counters (x1+y1) (x2+y2) (x3+y3) (x4+y4) (x5+y5) (x6+y6) (x7+y7) (x8+y8)

emptyCounters x1 x2 x3 x4 x5 x6 x7 x8 = 
    mempty { ewriter = mempty {counters = Counters x1 x2 x3 x4 x5 x6 x7 x8}}

addToCounter :: Counters -> MSOS ()
addToCounter cs = MSOS $ \_ mut -> return (Right(), mut, mempty { ewriter = mempty { counters = cs } })

addToRCounter :: Counters -> Rewrite () 
addToRCounter cs = Rewrite $ \_ mut -> (Right(), mut, mempty { counters = cs })

count_step :: MSOS ()
count_step = MSOS $ \_ mut -> return (Right (), mut, emptyCounters 1 0 0 0 0 0 0 0)

count_delegation :: MSOS ()
count_delegation = MSOS $ \_ mut -> return (Right (), mut, emptyCounters 0 0 0 0 0 1 0 0)

count_refocus = MSOS $ \_ mut -> return (Right (), mut, emptyCounters 0 0 0 0 1 0 0 0)

count_restart :: MSOS ()
count_restart = MSOS $ \_ mut -> return (Right (), mut, emptyCounters 0 0 0 1 0 0 0 0)

count_rewrite :: Rewrite ()
count_rewrite = Rewrite $ \_ st -> (Right (), st, mempty { counters = Counters 0 1 0 0 0 0 0 0})

count_rewrite_attempt :: Rewrite ()
count_rewrite_attempt = Rewrite $ \_ st -> (Right (), st, mempty { counters = Counters 0 0 1 0 0 0 0 0})

count_backtrack_out :: Rewrite ()
count_backtrack_out = Rewrite $ \_ st -> (Right (), st, mempty { counters = Counters 0 0 0 0 0 0 1 0 })

count_backtrack_in :: Rewrite ()
count_backtrack_in = Rewrite $ \_ st -> (Right (), st, mempty { counters = Counters 0 0 0 0 0 0 0 1 })

ppCounters cs =
 "number of (" ++ counterKeys ++ "): (" ++ displayCounters cs ++ ")"

counterKeys = "restarts,rewrites,(attempts),steps,refocus,premises,backtracking(outer),backtracking(inner)"
displayCounters (Counters steps rewrites rattempts restarts refocus delegations bout bin) = 
  intercalate "," $ 
    map show [restarts, rewrites, rattempts, steps, refocus, delegations, bout, bin]

-- | Yields an error signaling that no rule is applicable.
-- The funcon term argument may be used to provide a useful error message.
norule :: Funcons -> Rewrite a
norule f = rewrite_throw (NoRule [])

-- | Yields an error signaling that a sort error was encountered.
-- These errors render a rule /inapplicable/ and a next rule is attempted
-- when a backtracking procedure like 'evalRules' is applied.
-- The funcon term argument may be used to provide a useful error message.
sortErr :: Funcons -> String -> Rewrite a
sortErr f str = rewrite_throw (SortErr str)

-- | Yields an error signaling that a partial operation was applied
-- to a value outside of its domain (e.g. division by zero). 
-- These errors render a rule /inapplicable/ and a next rule is attempted
-- when a backtracking procedure like 'evalRules' is applied.
-- The funcon term argument may be used to provide a useful error message.
partialOp :: Funcons -> String -> Rewrite a
partialOp f str = rewrite_throw (PartialOp str) 

exception :: Funcons -> String -> Rewrite a
exception f str = rewrite_throw (Err str)

internal :: String -> Rewrite a
internal str = rewrite_throw (Internal str)

sidecond :: String -> Rewrite a
sidecond str = rewrite_throw (SideCondFail str)

buildStep :: MSOS StepRes -> Rewrite Rewritten 
buildStep = buildStepCounter (return ()) -- does not count

buildStepCount :: MSOS StepRes -> Rewrite Rewritten
buildStepCount = buildStepCounter count_delegation

buildStepCounter :: MSOS () -> MSOS StepRes -> Rewrite Rewritten 
buildStepCounter counter mf = compstep (counter >> mf)

optRefocus :: MSOS StepRes -> MSOS StepRes
optRefocus stepper = doRefocus >>= \case
                        True    -> stepper -- refocus stepper 
                        False   -> stepper 

-- refocus :: MSOS StepRes -> MSOS StepRes
-- refocus stepper -- stop refocussing when a signal has been raised
--                 = count_refocus >> if_violates_refocus stepper return continue
--     where continue = \case
--             Right vs  -> return (Right vs)
--             Left f    -> 
--               liftRewrite (rewriteFuncons f) >>= \case
--                 ValTerm [v] -> return (Right [v])
--                 ValTerm vs  -> return (Left f) -- undo rewrites and accept last step
--                 res         -> refocus $ stepRewritten res

stepRewritten :: Rewritten -> MSOS StepRes 
stepRewritten (ValTerm vs) = return (Right vs)
stepRewritten (CompTerm f step) = modifyRewriteReader mod (count_step >> step)
  where mod ctxt = ctxt {local_fct = f}

-- | Returns a value as a fully rewritten term. 
rewritten :: Values -> Rewrite [Rewrite Rewritten]
rewritten  vs =  return $ [return $ ValTerm [vs]]

rewritten' :: Values ->  Rewrite Rewritten
rewritten'  vs =  return $ ValTerm [vs]

rewrittens :: [Values] -> Rewrite [Rewrite Rewritten]
rewrittens vs =  return $ [return $ ValTerm vs]

-- | Yield a funcon term as the result of a syntactic rewrite.
-- This function must be used instead of @return@.
-- The given term is fully rewritten.
rewriteTo' :: Funcons -> Rewrite [Rewrite Rewritten] -- only rewrites, no possible signal
-- TODO count in inner Rewrite instead
rewriteTo' f = count_rewrite >> rewriteFuncons f

rewriteTo f = convert $ rewriteTo' f
-- | Yield a sequence of funcon terms as the result of a rewrite.
-- This is only valid when all terms rewrite to a value
rewriteSeqTo :: [Funcons] -> Rewrite [Rewrite Rewritten]
rewriteSeqTo fs = do
    rewrites <- rewriteStrictSequence fs
    -- count_rewrite >> vals
    return $ map (\rewrite -> do
        count_rewrite >> rewrite
        val <- rewrite
        return $  ValTerm val) rewrites
        -- ValTerm) vals

  -- count_rewrite >> (ValTerm <$> rewriteStrictSequence fs)

-- | Yield a funcon term as the result of an 'MSOS' computation.
-- This function must be used instead of @return@. 
stepTo :: Funcons -> MSOS StepRes 
stepTo = return . Left

-- | Yield a sequence of funcon terms as the result of a computation.
-- This is only valid when all terms rewrite to a value
stepSeqTo :: [Funcons] -> MSOS [ MSOS StepRes]
stepSeqTo fs = do
  rewrites <- liftRewrite $ rewriteStrictSequence fs
  return $ map (\r ->  Right <$> liftRewrite r ) rewrites
  -- Right <$> liftRewrite (rewriteStrictSequence fs)

-- if_abruptly_terminates :: Bool -> MSOS[MSOS StepRes] -> (StepRes -> MSOS[MSOS StepRes])
--                             -> (StepRes ->MSOS[MSOS StepRes]) -> MSOS[MSOS StepRes]
-- if_abruptly_terminates care (MSOS fstep) abr no_abr = MSOS $ \ctxt mut ->
--     fstep ctxt mut >>= \case
--         (Right f', mut', wr') ->
--             let failed     = any isJust (ctrl_entities wr')
--                 MSOS fstep | failed && care = abr f'
--                            | otherwise      = no_abr f'
--             in do (e_f'', mut'', wr'') <- fstep ctxt mut'
--                   return (e_f'', mut'', wr' <> wr'')
--         norule_res -> return norule_res

-- TODO is input test accurate? 
-- TODO We should also find changes to mutable entities
if_violates_refocus :: MSOS StepRes -> (StepRes -> MSOS StepRes)
                            -> (StepRes -> MSOS StepRes) -> MSOS StepRes
if_violates_refocus (MSOS fstep) viol no_viol = MSOS $ \ctxt mut ->
    fstep ctxt mut >>= \case
        (Right f', mut', wr') ->
            let violates = any isJust (ctrl_entities wr')
                            || any (not . null) (out_entities wr')
                            || any (isNothing . snd) (inp_es mut')
--                            || any isJust (dctrl_entities ctxt)
                MSOS fstep | violates    = viol f'
                           | otherwise   = no_viol f'
            in do (e_f'', mut'', wr'') <- fstep ctxt mut'
                  return (e_f'', mut'', wr' <> wr'')
        norule_res -> return norule_res

-- | Execute a premise as either a rewrite or a step.
-- Depending on whether only rewrites are necessary to yield a value,
-- or whether a computational step is necessary,
-- a different continuation is applied (first and second argument).
-- Example usage:
--
-- @
-- stepScope :: NonStrictFuncon --strict in first argument
-- stepScope [FValue (Map e1), x] = premiseEval x rule1 step1 
--  where   rule1 v  = rewritten v
--          step1 stepX = do   
--              Map e0  <- getInh "environment"
--              x'      <- withInh "environment" (Map (union e1 e0)) stepX
--              stepTo (scope_ [FValue e1, x'])
-- @
premiseEval :: ([Values] -> Rewrite [Rewrite Rewritten]) -> (MSOS StepRes -> MSOS StepRes) -> 
                    Funcons -> Rewrite [Rewrite Rewritten]
premiseEval vapp fapp f = rewriteFuncons f >>= (\x -> concatInside$ sequence $ map (\y -> do
    v <- y
    case v of 
      ValTerm vs      -> vapp vs
      CompTerm _ step -> return [buildStepCount (optRefocus (fapp step))])x)

-- | Execute a computational step as a /premise/.
-- The result of the step is the returned funcon term. 
premiseStepApp :: (StepRes -> StepRes) -> Funcons -> MSOS [MSOS StepRes]
premiseStepApp app f = do
    rewrites <- liftRewrite $ rewriteFuncons f
    -- TODO this is probably not right...
    return $ map(\r -> do 
        rewritten <- liftRewrite r
        case rewritten of 
          ValTerm vs      -> msos_throw (StepOnValue vs)
          CompTerm _ step -> app <$> (count_delegation >> optRefocus step)
     ) rewrites
  
  -- liftRewrite (rewriteFuncons f) >>= \case
    -- ValTerm vs      -> msos_throw (StepOnValue vs)
    -- CompTerm _ step -> app <$> (count_delegation >> optRefocus step)

premiseStep :: Funcons -> MSOS [MSOS StepRes]
premiseStep = premiseStepApp id 

----- main `step` function
evalFuncons :: Funcons -> MSOS [MSOS StepRes]
evalFuncons f = do
  -- TODO redo with bind 
  rewrites <- liftInnerAndOuterRewrite ( rewriteFuncons f)

  return $ map (\rewrite -> do 
    rewritten <- rewrite 
    stepRewritten rewritten) rewrites

rewritesToType :: Funcons -> Rewrite [Rewrite Types]
rewritesToType f = do
  -- TODO >>= 
    rewrites <- rewriteFunconsWcount f
    return $ map (\rewrite -> do 
      rewritten <- rewrite 
      case rewritten of 
        ValTerm [v@(ComputationType _)] -> return (downcastValueType v)
        _                               -> rewriteToValErr)
       rewrites

  -- rewriteFunconsWcount f >>= (\case
  --   ValTerm [v@(ComputationType _)] -> return (downcastValueType v)
  --   _                               -> rewriteToValErr)

-- rewritesToValue :: Funcons ->  [Rewrite Values]
-- rewritesToValue f = do
--   rewriteFunconsWcount f >>= \case
--                     ValTerm [v]   -> return v
--                     _             -> rewriteToValErr

rewritesToValue :: Funcons -> Rewrite [Values]
rewritesToValue f = do
  rewriteFunconsWcount f >>= (\x -> sequence $ map (\y -> do
                  v <- y
                  case v of 
                    ValTerm [v]   -> return v
                    _             -> rewriteToValErr)x)

rewritesToValues :: Funcons -> Rewrite [Values]
rewritesToValues f = do
  rewriteFunconsWcount f >>= (\x -> concatInside$ sequence $ map (\y -> do
                  v <- y
                  case v of 
                    ValTerm vs  -> return vs
                    _           -> rewriteToValErr)x)

rewriteToValErr = rewrite_throw $ 
  SideCondFail "side-condition/entity-value/annotation evaluation requires step"

rewriteFunconsWcount :: Funcons -> Rewrite [Rewrite Rewritten]
-- TODO count inner instead
rewriteFunconsWcount f = count_rewrite_attempt >> rewriteFuncons f

rewriteFuncons :: Funcons -> Rewrite [Rewrite Rewritten]
rewriteFuncons f = modifyRewriteCTXT (\ctxt -> ctxt{local_fct = f}) (rewriteFuncons' f)
 where
    rewriteFuncons' :: Funcons -> Rewrite [Rewrite Rewritten]
    rewriteFuncons' (FValue v)   = return [return (ValTerm [v])]
{-    rewriteFuncons' (FTuple fs)  = 
      let fmops = tupleTypeTemplate fs 
      in if any (isJust . snd) fmops
          -- sequence contains a sequence-operator, thus is a sequence of sorts  
          then rewritten . typeVal =<< evalTupleType fmops
          -- regular sequence 
          else evalStrictSequence fs (rewritten . safe_tuple_val) FTuple
-}
    -- rewriteFuncons' (FList fs)   = evalStrictSequence fs (rewritten . List) FList
    rewriteFuncons' (FSet fs)    = evalStrictSequence' fs (rewritten' . setval_) FSet
    rewriteFuncons' (FMap fs)    = evalStrictSequence' fs (rewritten' . mapval_) FMap
    rewriteFuncons' f@(FBinding fk fv) = evalStrictSequence' (fk:fv) (rewritten' . tuple) mkBinding 
      where mkBinding (k:fvs) = FBinding k fvs
            mkBinding _       = error "invalid binding-notation"
    rewriteFuncons' f@(FSortPower s1 fn) = case (s1,fn) of 
      (FValue mty@(ComputationType _), FValue v) 
        | Nat n <- upcastNaturals v -> 
                  rewrittens (replicate (fromInteger n) (ComputationType (Type (downcastValueType mty))))
      (FValue mty, _) -> rewriteFuncons fn >>= (\x -> concatInside$ sequence $ map (\y -> do
                  v <- y
                  case v of 
                    ValTerm [v] -> rewriteFuncons $ FSortPower s1 (FValue v)
                    ValTerm _   -> sortErr f "second operand of ^ cannot compute a sequence"
                    CompTerm _ mf -> return [flattenApplyWithExc ie (FSortPower s1) mf]
                  ) x )
                where ie = SortErr "^_ multiadic argument" 
      _ -> rewriteFuncons s1 >>= (\x -> concatInside$ sequence $ map (\y -> do
                  v <- y
                  case v of 
                    ValTerm [v] -> rewriteFuncons $ FSortPower (FValue v) fn
                    ValTerm _   -> sortErr f "first operand of ^ cannot compute a sequence"
                    CompTerm _ mf -> return [flattenApplyWithExc ie (flip FSortPower fn) mf]
                  )x)
              where ie = SortErr "_^ multiadic argument"
    rewriteFuncons' f@(FSortSeq s1 op)     = case s1 of 
      (FValue (ComputationType (Type ty))) -> rewritten $ ComputationType $ Type $ AnnotatedType ty op
      (FValue _) -> sortErr (FSortSeq s1 op) "sort-sequence operator not on type"
      _ -> rewriteFuncons s1 >>= (\x -> concatInside$ sequence $ map (\y -> do
                  v <- y
                  case v of 
                    ValTerm [v1] -> rewriteFuncons $ FSortSeq (FValue v1) op
                    ValTerm vs   -> sortErr (FSortSeq s1 op) "operand of sort-sequence operator cannot compute a sequence"
                    CompTerm _ mf ->  return [flattenApplyWithExc ie (flip FSortSeq op) mf]
                  ) x ) 
              where ie = SortErr "sort-sequence operator, multiadic argument"
    rewriteFuncons' (FSortComputes f1) = case f1 of
        (FValue (ComputationType (Type ty))) -> rewritten $ ComputationType $ ComputesType ty
        (FValue _) -> sortErr (FSortComputes f1) "=> not applied to a type"
        _ -> rewriteFuncons f1 >>= (\x -> concatInside$ sequence $ map (\y -> do
                  v <- y
                  case v of 
                    ValTerm [v1] -> rewriteFuncons $ FSortComputes (FValue v1)
                    ValTerm vs   -> sortErr (FSortComputes f1) "operand of => cannot compute a sequence"
                    CompTerm _ mf    ->  return [flattenApplyWithExc ie FSortComputes mf]
                  ) x )
                  where ie = SortErr "=>_ multiadic argument"
    rewriteFuncons' (FSortComputesFrom f1 f2) = case (f1,f2) of
        (FValue (ComputationType (Type ty1)),FValue (ComputationType (Type ty2))) 
            -> rewritten $ ComputationType (ComputesFromType ty1 ty2)
        (FValue _, FValue _) -> sortErr (FSortComputesFrom f1 f2) "=> not applied to types"
        (FValue (ComputationType (Type ty1)),_) 
            -> rewriteFuncons f2 >>= (\x -> concatInside$ sequence $ map (\y -> do
                  v <- y
                  case v of 
                    ValTerm [v2] -> rewriteFuncons $ FSortComputesFrom f1 (FValue v2)
                    ValTerm _ -> sortErr (FSortComputesFrom f1 f2) "second operand of => cannot compute a sequence"
                    CompTerm _ mf    ->  return [flattenApplyWithExc ie (FSortComputesFrom f1) mf]
                  ) x )
                  where ie = SortErr "_=>_ multiadic operand (2)"
        (_,_) 
            -> rewriteFuncons f1 >>= (\x -> concatInside$ sequence $ map (\y -> do
                  v <- y
                  case v of 
                    ValTerm [v1] -> rewriteFuncons $ FSortComputesFrom (FValue v1) f2
                    ValTerm _ -> sortErr (FSortComputesFrom f1 f2) "_=>_ multiadic operand (1)"
                    CompTerm _ mf    ->  return [flattenApplyWithExc ie (flip FSortComputesFrom f2) mf]
                  ) x )
                  where ie = SortErr "_=>_ multiadic operand (1)"
    rewriteFuncons' (FSortUnion s1 s2)   = case (s1, s2) of
        (FValue (ComputationType (Type t1))
            , FValue (ComputationType (Type t2))) -> rewritten $ typeVal $ Union t1 t2
        (FValue _, FValue _) -> sortErr (FSortUnion s1 s2) "sort-union not applied to two sorts"
        (FValue v1, _) -> rewriteFuncons s2 >>= (\x -> concatInside$ sequence $ map (\y -> do
                  v <- y
                  case v of 
                    ValTerm [v2] -> rewriteFuncons $ FSortUnion s1 (FValue v2)
                    ValTerm _ -> sortErr (FSortUnion s1 s2) "sort-union multiadic argument (2)"
                    CompTerm _ mf -> return [flattenApplyWithExc ie (FSortUnion s1) mf]
                  ) x )
              where ie = SortErr "sort-union multiadic argument (2)"
        _ -> rewriteFuncons s1 >>= (\x -> concatInside$ sequence $ map (\y -> do
                  v <- y
                  case v of 
                    ValTerm [v] -> rewriteFuncons $ FSortUnion (FValue v) s2
                    ValTerm _ -> sortErr (FSortUnion s1 s2) "sort-union multiadic argument (1)"
                    CompTerm _ mf   -> return [flattenApplyWithExc ie (flip FSortUnion s2) mf]
                ) x )
                  where ie = SortErr "sort-union multiadic argument (1)"
    rewriteFuncons' (FSortInter s1 s2)   = case (s1, s2) of
        (FValue (ComputationType (Type t1))
            , FValue (ComputationType (Type t2))) -> rewritten $ typeVal $ Intersection t1 t2
        (FValue _, FValue _) -> sortErr (FSortInter s1 s2) "sort-intersection not applied to two sorts"
        (FValue v1, _) -> rewriteFuncons s2 >>=  (\x -> concatInside$ sequence $ map (\y -> do
                  v <- y
                  case v of 
                    ValTerm [v2] -> rewriteFuncons $ FSortInter s1 (FValue v2)
                    ValTerm _ -> sortErr (FSortInter s1 s2) "sort-intersection multiadic argument (2)" 
                    CompTerm _ mf -> return [flattenApplyWithExc ie (FSortInter s1) mf]
                    )x)
              where ie = SortErr "sort-intersection multiadic argument (2)"
        _ -> do rewriteFuncons s1 >>= (\x -> concatInside$ sequence $ map (\y -> do
                    v <- y
                    case v of 
                      ValTerm [v1] -> rewriteFuncons $ FSortInter (FValue v1) s2
                      ValTerm _ -> sortErr (FSortInter s1 s2) "sort-intersection multiadic argument (1)" 
                      CompTerm _ mf   -> return [ flattenApplyWithExc ie (flip FSortInter s2) mf]
                      )x)
                      where ie = SortErr "sort-intersection multiadic argument (1)"
    rewriteFuncons' (FSortComplement s1) = case s1 of 
      FValue (ComputationType (Type t1)) -> rewritten $ typeVal $ Complement t1
      FValue _ -> sortErr (FSortComplement s1) "sort-complement not applied to a sort" 
      _ -> do rewriteFuncons s1 >>= (\x -> concatInside$ sequence $ map (\y -> do
                v <- y
                case v of 
                    ValTerm [v] -> rewriteFuncons $ FSortComplement (FValue v)
                    ValTerm vs -> sortErr (FSortComplement s1) "sort-complement multiadic argument"
                    CompTerm _ mf -> return [flattenApplyWithExc ie FSortComplement mf]) x )
                  where ie = SortErr "sort-complement multiadic argument"
    rewriteFuncons' (FName nm) = 
        do  mystepfs <- lookupFuncon nm 
            concatInside $ sequence $ map (\rewrite_mystepf -> do
              mystepf <- rewrite_mystepf
              case mystepf of 
                NullaryFuncon mystep -> return [mystep]
                StrictFuncon _ -> rewriteFuncons' (FApp nm [])
                ValueOp _ -> rewriteFuncons' (FApp nm [])
                _ -> error ("funcon " ++ unpack nm ++ " not applied to any arguments")) mystepfs 
    rewriteFuncons' (FApp nm arg)    = 
        do  mystepfs <- lookupFuncon nm
            concatInside $ sequence $ map (\rewrite_mystepf -> do
              mystepf <- rewrite_mystepf
              case mystepf of 
                  NullaryFuncon _     -> exception (FApp nm arg) ("nullary funcon " ++ unpack nm ++ " applied to arguments: " ++ (showFunconsSeq arg))
                  ValueOp mystep      -> evalStrictSequence' arg mystep (applyFuncon nm)
                  StrictFuncon mystep -> evalStrictSequence' arg mystep (applyFuncon nm)
                  NonStrictFuncon mystep -> return [mystep arg]
                  PartiallyStrictFuncon strns strn mystep -> 
                    evalSequence' (strns ++ repeat strn) arg mystep (applyFuncon nm)) mystepfs

rewriteStrictSequence :: [Funcons] -> Rewrite [Rewrite [Values]]
rewriteStrictSequence fs = case rest of 
  []      -> return [return (map downcastValue vs)]
  (x:xs)  -> rewriteFuncons x >>= \x -> concatInside$ sequence $ map (\y -> do
      v <- y
      case v of 
        ValTerm vs'    -> rewriteStrictSequence (vs++map FValue vs'++xs)
        CompTerm f0 mf -> internal ("step on sequence of computations: " ++ show fs)) x
  where (vs, rest) = span (not . hasStep) fs

--OPT: replace by specialised variant of evalSequence
evalStrictSequence' :: [Funcons] -> ([Values] -> Rewrite Rewritten) -> ([Funcons] -> Funcons) -> Rewrite [Rewrite Rewritten]
evalStrictSequence' args cont cons = 
    evalSequence' (replicate (length args) Strict) args 
        (cont . map downcastValue) cons

evalStrictSequence :: [Funcons] -> ([Values] -> Rewrite Rewritten) -> ([Funcons] -> Funcons) ->  Rewrite Rewritten
evalStrictSequence args cont cons = convert $ evalStrictSequence' args cont cons 

evalSequence :: [Strictness] -> [Funcons] -> 
    ([Funcons] -> Rewrite Rewritten) -> ([Funcons] -> Funcons) -> Rewrite Rewritten
evalSequence strns args cont cons = convert $ evalSequence' strns args cont cons


evalSequence' :: [Strictness] -> [Funcons] -> 
    ([Funcons] -> Rewrite Rewritten) -> ([Funcons] -> Funcons) -> Rewrite [Rewrite Rewritten]
evalSequence' strns args cont cons = do
    let args_map = zip [1..] (zip strns args)

    let evalSeqAux :: [(Int, (Strictness, Funcons))] -> [(Int, (Strictness, Funcons))]  -> Rewrite [Rewrite Rewritten]
        evalSeqAux args_done args_undone 
          | null args_undone = return $ [cont (map (snd . snd) (sorter args_done))]
          | otherwise        = do
              options <- all_randomRemove NDInterleaving args_undone
              -- ((i,(_,f)), args_undone') <- 
                -- maybe_randomRemove NDInterleaving args_undone
              let valueCont :: Int -> [(Int, (Strictness, Funcons))] -> [Values] -> Rewrite [Rewrite Rewritten]
                  valueCont i args_undone' vs = do 
                    -- count_rewrite TODO
                    evalSeqAux args_done' (map bump args_undone')
                    where args_done' = filter ((<i) . fst) args_done ++
                                        zip [i..] ((zip (replicate (length vs) Strict) 
                                                          (map FValue vs))) ++
                                       map bump (filter ((>i) . fst) args_done)
                          bump (k,v) | k > i      = (k + length vs - 1, v)
                                     | otherwise  = (k,v)
              let funconCont i args_undone' stepf = stepf >>= \case 
                    Left f' -> stepTo (cons (remakeArgs args_done [f'] args_undone'))
                    Right vs' -> stepTo (cons (remakeArgs args_done (map FValue vs') args_undone'))
                   where remakeArgs m1 l1 m2 =  
                          map (snd . snd) (sorter (filter ((<i) . fst) (m1++m2))) ++ l1 ++
                          map (snd . snd) (sorter (filter ((>i) . fst) (m1++m2)))

              concatInside $ sequence $ map (\option -> 
                                        do
                                          ((i,(_,f)), args_undone') <- option
                                          premiseEval (valueCont i args_undone' ) (funconCont i args_undone') f
                                                   ) options
              

    uncurry evalSeqAux (partition (isDone . snd) args_map)
 where  isDone (NonStrict, _)     = True
        isDone (Strict, FValue _) = True
        isDone (Strict,_)         = False
        sorter = sortBy (compare `on` fst)

-- | Yield an 'MSOS' computation as a fully rewritten term.
-- This function must be used in order to access entities in the definition
-- of funcons.
compstep :: MSOS StepRes -> Rewrite Rewritten
compstep mf = Rewrite $ \ctxt st -> 
    let f0 = local_fct ctxt 
    in (Right (CompTerm f0 mf), st, mempty)

--- transitive closure over steps
stepTrans :: RunOptions -> Int -> StepRes -> MSOS [MSOS StepRes]
stepTrans opts i res = case res of 
  Right vs -> return [return res]
  Left f | maybe False ((<= i)) (max_restarts opts) -> return [return res]
         | otherwise -> stepAndOutput f
         
        --  if_abruptly_terminates (do_abrupt_terminate opts) 
        --                   (stepAndOutput f) (\x -> return [return x]) continue
       where continue res = do 
              l_msos_stepres <- stepTrans opts (i+1) res
              return $ map (\x -> count_restart >> x) l_msos_stepres

stepAndOutput :: Funcons -> MSOS [MSOS StepRes]
stepAndOutput f = MSOS $ \ctxt mut -> 
   let MSOS stepper' = evalFuncons f
       stepper ctxt mut = stepper' (setGlobal ctxt) mut
       setGlobal ctxt = ctxt 
               { ereader = (ereader ctxt) {global_fct = f }}
   in do   (eres,mut',wr') <- stepper ctxt mut
           mapM_ (uncurry fprint) 
               [ (entity,val) 
               | (entity, vals) <- M.assocs (out_entities wr')
               , val <- vals ]
           return (eres, mut', wr')


toStepRes :: Funcons -> StepRes
toStepRes (FValue v)  = Right [v]
toStepRes f           = Left f

flattenApplyWithExc :: IE -> (Funcons -> Funcons) -> MSOS StepRes -> Rewrite Rewritten
flattenApplyWithExc ie app m = compstep $ m >>= \case 
    Left f    -> return $ Left $ app f
    Right [v] -> return $ Left $ app (FValue v)
    Right vs  -> msos_throw ie

concatInside :: Rewrite [[a]] -> Rewrite [a]
concatInside (Rewrite f) = Rewrite (\ctxt st -> do
                        let (e_a1,st1,cs1) = f ctxt st
                        case e_a1 of 
                          Left err  -> (Left err, st1, cs1)
                          Right a1  -> (Right $ concat a1, st1, cs1))
                            -- let (Rewrite list_b) = k a1
                            -- map (\b -> 
                            --   let (a2,st2,cs2) = b ctxt st1
                            --   in (a2,st2,cs1 <> cs2)
                            --   ) list_b) list_a)

-- TODO choose random
convertMSOS :: MSOS [MSOS a] ->  MSOS a
convertMSOS (MSOS l) = MSOS ( \ctxt st -> do
    (e_a1,st1,cs1) <- l ctxt st
    case e_a1 of 
        Left err  -> return (Left err, st1, cs1)
        Right a1 -> do 
          let (MSOS env) = (head a1)
          env ctxt st)