{-# LANGUAGE LambdaCase #-}

module Funcons.Substitution (
    Env(..), subsAndRewritesInEnv,
    subsAndRewritesToValue, subsAndRewritesToValuesInEnv, subsAndRewritesToValues,
    envInsert, emptyEnv,
    Levelled(..), substitute_signal, substitute,rewriteTermTo, stepTermTo, rewriteTermTo',
    envRewrite, envStore, lifted_envRewrite, lifted_envStore, 
    fLevel, fsLevel, vLevel, vsLevel, envLookup
    ) where

import Funcons.Types
import Funcons.MSOS
    ( internal,
      liftInnerAndOuterRewrite,
      liftRewrite,
      rewriteFunconsWcount,
      rewriteSeqTo,
      rewriteTo,
      rewriteTo',
      rewriteToValErr,
      rewritesToValue,
      rewritesToValues,
      stepSeqTo,
      stepTo,
      MSOS,
      Rewrite(Rewrite),
      Rewritten(..),
      StepRes, convertMSOS )

import Control.Applicative
import Control.Monad
import Data.Monoid
import qualified Data.Map as M

-- | An environment mapping meta-variables to funcon terms.
-- This environment is used by a substitution procedure to transform
-- funcon terms from 'FTerm' representation to 'Funcons'.
type Env = M.Map MetaVar Levelled 
data Levelled   = TypeTerm ComputationTypes
                | TypesTerm [ComputationTypes]
                | ValueTerm Values
                | ValuesTerm [Values]
                | FunconTerm Funcons (Maybe (MSOS StepRes)) {- cached step -}
                | FunconsTerm [Funcons]

-- | The empty substitution environment.
-- Bindings are inserted by pattern-matching.
emptyEnv = M.empty

envLookup :: Env -> MetaVar -> Rewrite Levelled
envLookup env k = case M.lookup k env of
                    Nothing -> internal ("no substitution for variable: " <> k)
                    Just lf -> return lf

envInsert :: MetaVar -> Levelled -> Env -> Env
envInsert = M.insertWith op
  where op new old = new --TODO somehow unify values
  {- 
        isWildCard (ValueTerm VAny) = True
        isWildCard (ValuesTerm [VAny]) = True
        isWildCard (FunconTerm (FValue VAny) _) = True
        isWildCard (FunconsTerm [FValue VAny]) = True
        isWildCard _ = False
  -}
        

{-
tsLevel :: Levelled -> Rewrite [ComputationTypes]
tsLevel = \case TypesTerm ts  -> return ts
                TypeTerm t    -> return [t]
                ValuesTerm vs 
                  | all isSort_ vs -> return $ map downcastSort (map FValue vs)
                  | otherwise     -> internal "not bound to types"
                ValueTerm v | isSort_ v-> return $ [downcastSort v]
-}

vsLevel :: Levelled -> Rewrite [Values]
vsLevel = \case FunconsTerm fs 
                  | all (not.hasStep) fs  -> return (map downcastValue fs)
                  | otherwise           -> internal "not bound to values"
                FunconTerm (FValue v) _ -> return [v]
                FunconTerm f         _  -> internal ("not bound to values")  
                ValuesTerm vs           -> return vs
                ValueTerm v             -> return [v]
                TypeTerm t              -> return [ComputationType t]
                TypesTerm ts            -> return (map ComputationType ts)

vLevel :: Levelled -> Rewrite Values
vLevel =  \case FunconsTerm [FValue v]  -> return v
                FunconsTerm fs          -> internal "not bound to values"
                FunconTerm (FValue v) _ -> return v
                FunconTerm f         _  -> internal ("not bound to value")  
                ValuesTerm [v]          -> return v
                ValuesTerm vs           -> internal ("not bound to value")  
                ValueTerm v             -> return v
                TypeTerm t              -> return (ComputationType t)
                TypesTerm [t]           -> return (ComputationType t)
                TypesTerm _             -> internal "not bound to a value"

fsLevel :: Levelled -> Rewrite [Funcons]
fsLevel = \case FunconsTerm f       -> return f
                FunconTerm f _      -> return [f]
                ValuesTerm vs       -> return (map FValue vs)
                ValueTerm v         -> return [FValue v]
                TypesTerm ts        -> return (map sort_ ts)
                TypeTerm t          -> return [sort_ t]

fLevel k = \case    
  FunconsTerm [f]   -> return f
  FunconsTerm fs    -> internal "not bound to a funcon"
  FunconTerm f _    -> return f
  ValuesTerm [v]    -> return (FValue v)
  ValuesTerm vs     -> internal "not bound to a funcon" 
  ValueTerm v       -> return (FValue v)
  TypeTerm t        -> return (sort_ t)
  TypesTerm [t]     -> return (sort_ t)
  TypesTerm ts      -> internal "not bound to a funcon"

-- substitution

substitute_signal :: FTerm -> Env -> Rewrite Values
substitute_signal t env = case t of
  TVar k        -> vLevel $ envMaybeLookup env k
  TName nm      -> return (ADTVal nm [])
  TApp nm terms -> ADTVal nm . map FValue  <$> subs_flatten terms env
  TSeq ts       -> internal "top level sequence during substitution (signal)" 
--  TList ts      -> List <$> subs_flatten ts env
  TSet ts       -> setval_ <$> subs_flatten ts env
  TMap ts       -> mapval_ <$> subs_flatten ts env
  TBinding x y  -> tuple <$> subs_flatten [x,y] env
  TFuncon (FValue v) -> return v
  TAny          -> return VAny
  _             -> internal "missing case in substitute_signal"
  where subs_flatten :: [FTerm] -> Env -> Rewrite [Values]
        subs_flatten terms env = (concat <$>) $ forM terms $ \case
              TVar k  -> vsLevel $ envMaybeLookup env k
              TSeq ts -> mapM (flip substitute_signal env) ts
              term    -> (:[]) <$> substitute_signal term env

        envMaybeLookup :: Env -> MetaVar -> Levelled
        envMaybeLookup env k = case M.lookup k env of
                            Nothing -> ValueTerm VAny
                            Just lf -> lf


substitute :: FTerm ->  Env -> Rewrite Funcons
substitute (TVar k) env = envLookup env k >>= fLevel k
substitute (TName nm) env = return $ FName nm
substitute (TApp nm terms) env = FApp nm <$> subsFlatten terms env
substitute (TSeq terms) env = internal ("top level sequence during substitution: " ++ show terms)
-- e.g. print(V+:values+) -- standard-out![V+] -> ()
--substitute (TList terms) env = FList <$> subsFlatten terms env 
substitute (TSet terms)  env = FSet <$> subsFlatten terms env
substitute (TMap terms)  env = FMap <$> subsFlatten terms env
substitute (TBinding x y) env = FBinding <$> substitute x env <*> subsFlatten [y] env
substitute (TFuncon f) env = return f
substitute (TSortUnion t1 t2) env = FSortUnion <$> substitute t1 env <*> substitute t2 env
substitute (TSortInter t1 t2) env = FSortInter <$> substitute t1 env <*> substitute t2 env
substitute (TSortComplement t1) env = FSortComplement <$> substitute t1 env
substitute (TSortSeq t1 op) env = flip FSortSeq op <$> substitute t1 env
substitute (TSortPower t1 t2) env = FSortPower <$> substitute t1 env <*> substitute t2 env
substitute (TSortComputes t1) env = FSortComputes <$> substitute t1 env
-- special case for thunks/continuations
substitute (TSortComputesFrom (TSeq []) t2) env = 
    FSortComputesFrom nulltype_ <$> substitute t2 env
substitute (TSortComputesFrom t1 t2) env = 
    FSortComputesFrom <$> substitute t1 env <*> substitute t2 env
substitute TAny env = internal "missing substitution (wildcard)"

-- flatten out sequence-variables
subsFlatten :: [FTerm] -> Env -> Rewrite [Funcons]
subsFlatten terms env = concat <$> (forM terms $ \case 
                            TVar k  -> envLookup env k >>= fsLevel
                            TSeq ts -> subsFlatten ts env
                            term    -> (:[]) <$> substitute term env)

-- Version of subsAndRewritesToValue that 'caches' computational steps:
-- If after rewriting a computational step is produced the
--  step and associated funcon replace the term in the environment
--  (if the term consists of just a meta-variable)
-- This function immediately returns a computational step when
--  a given term has a cached step
-- If the term is not just a meta-variable, this function behaves normally
subsAndRewritesInEnv :: FTerm -> Env -> Rewrite [Rewrite (Rewritten, Env)]
subsAndRewritesInEnv (TVar x) env 
  | Just (FunconTerm f (Just step)) <- M.lookup x env = 
      return $ [return (CompTerm f step, env)]
subsAndRewritesInEnv term env  = do 
  f <- substitute term env
  options <- rewriteFunconsWcount f
  case term of 
    TVar x -> return $ map (\rewrite -> do
      res <- rewrite
      case res of 
        ValTerm vs       -> return (res, envInsert x (ValuesTerm vs) env)
        CompTerm f step  -> return (res, envInsert x (FunconTerm f (Just step)) env)) options
    _ -> return $ map (\option -> do
        res <- option 
        return (res, env)) options
      
      -- return (res, env)

subsAndRewritesToValue :: FTerm -> Env -> Rewrite [Rewrite Values]
subsAndRewritesToValue f env = do
  l <- subsAndRewritesToValueInEnv f env
  return $ map (\r -> fst <$> r) l
  -- fst <$> subsAndRewritesToValueInEnv f env


-- Important optimisation:
-- If the given term is a var, 
--    update the env to store the rewritten value.
subsAndRewritesToValueInEnv :: FTerm -> Env -> Rewrite [Rewrite (Values, Env)]
subsAndRewritesToValueInEnv (TVar x) env 
  -- assumed to be already rewritten (because cached step is present)
  | Just (FunconTerm f (Just step)) <- M.lookup x env = rewriteToValErr
subsAndRewritesToValueInEnv term env = do
  f <- substitute term env 
  vals <- rewritesToValue f
  case term of 
            TVar var  -> return $ map(\v -> return (v, envInsert var (ValueTerm v) env)) vals
            _         -> return $ map(\v -> return (v, env)) vals

subsAndRewritesToValues :: FTerm -> Env -> Rewrite [Values]
subsAndRewritesToValues f env = fst <$> subsAndRewritesToValuesInEnv f env

subsAndRewritesToValuesInEnv :: FTerm -> Env -> Rewrite ([Values], Env)
subsAndRewritesToValuesInEnv (TVar x) env 
  -- assumed to be already rewritten (because cached step is present)
  | Just (FunconTerm f (Just step)) <- M.lookup x env = rewriteToValErr
subsAndRewritesToValuesInEnv term env = do
  fs  <- subsFlatten [term] env 
  vs  <- concat <$> mapM rewritesToValues fs
  case term of TVar var  -> return (vs, envInsert var (ValuesTerm vs) env)
               _         -> return (vs, env)


-- | Variant of 'rewriteTo' that applies substitution.
rewriteTermTo' :: FTerm -> Env -> Rewrite [Rewrite Rewritten]
rewriteTermTo' fterm env = subsFlatten [fterm] env >>= \case
  [f] -> rewriteTo' f
  fs  -> rewriteSeqTo fs 

rewriteTermTo :: FTerm -> Env -> Rewrite Rewritten
rewriteTermTo fterm env = convert $ rewriteTermTo' fterm env

convert :: Rewrite [Rewrite a] ->  Rewrite a
convert (Rewrite l) = Rewrite ( \ctxt st ->
    let (e_a1,st1,cs1) = l ctxt st
    in case e_a1 of 
        Left err  -> (Left err, st1, cs1)
        Right a1 -> do 
          let (Rewrite env) = (head a1)
          env ctxt st
    ) 

-- | Variant of 'stepTo' that applies substitution.
stepTermTo :: FTerm -> Env ->  MSOS StepRes
stepTermTo fterm env =  convertMSOS $ stepTermTo' fterm env

stepTermTo' :: FTerm -> Env -> MSOS [MSOS StepRes]
stepTermTo' fterm env = liftRewrite (subsFlatten [fterm] env) >>= \case 
  [f] -> return [stepTo f]
  fs  -> stepSeqTo fs

lifted_envStore :: MetaVar -> FTerm -> Env -> MSOS Env
lifted_envStore m t e = liftRewrite (envStore m t e)

envStore :: MetaVar -> FTerm -> Env -> Rewrite Env
envStore var term env = substitute term env >>= \case
    (FValue v)    -> return $ envInsert var (ValueTerm v) env
    fct           -> return $ envInsert var (FunconTerm fct Nothing) env

lifted_envRewrite :: MetaVar -> Env -> MSOS [MSOS Env]
lifted_envRewrite m e = liftInnerAndOuterRewrite (envRewrite m e)

-- | Apply as many rewrites as possible to the term bound to the
-- given variable in the meta-environment
envRewrite :: MetaVar -> Env -> Rewrite [Rewrite Env]
envRewrite var env = do
    envLookup env var >>= \case
      FunconTerm fct Nothing -> rewriteFunconsWcount fct >>= (\options -> return $  map (\rewrite -> do
        rewritten <- rewrite 
        case rewritten of 
          ValTerm vs    -> return $ envInsert var (ValuesTerm vs) env
          CompTerm f fs -> return $ envInsert var (FunconTerm f (Just fs)) env
       ) options )
      _ -> return [return env]


