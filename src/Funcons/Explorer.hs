{-# LANGUAGE FlexibleInstances, OverloadedStrings, LambdaCase, FlexibleContexts, RankNTypes, MultiParamTypeClasses #-}
{-# LANGUAGE InstanceSigs, ScopedTypeVariables, DataKinds#-}

module Funcons.Explorer where

import qualified Language.Explorer.Monadic as EI

import Funcons.EDSL hiding (isMap)
import Funcons.Operations (isMap, Values(Map, Atom, ADTVal), EvalResult(..), frombool) 
import Funcons.MSOS
import Funcons.RunOptions
import Funcons.Core
import Funcons.Core.Library
import Funcons.Core.Manual
import Funcons.Entities
import Funcons.Tools
import Funcons.Parser
import Funcons.Printer
import Funcons.Exceptions
import Funcons.Types (Funcons(..), Name, Values(..))

import Control.Monad (forM_, mapM_, join, liftM2)
import Control.Monad.Trans.Class (lift) 
import Data.IORef
import qualified Data.Map as M
import Data.Char (isSpace)
import Data.Tree (drawTree)
import Data.Text (pack)
import Text.Read (readMaybe)
import Data.Maybe (fromJust, isJust)

import System.Console.Haskeline
import System.Console.Haskeline.History
import System.Environment
import System.IO
import System.IO.Unsafe

import qualified MVD.Interface as MVD
import qualified MVD.Debugger as MVD
import qualified MVD.Finders as MVD


data Phrase = FTerm Funcons
            | Debug Funcons
            | Step 
            | SmallStep 
            | PrettyBigStep 
            | Finish
      deriving (Show, Eq) 

data Config = Config {
        reader  :: MSOSReader IO
      , state   :: MSOSState IO
      , progress:: StepRes 
      }
      deriving (Eq)

type Explorer = EI.Explorer Phrase IO Config ()

handle_revert :: EI.Ref -> Explorer -> IO Explorer
handle_revert r exp =
  case EI.revert r exp of
    Just e -> return e
    Nothing -> putStrLn "Invalid reference for revert" >> return exp

repll :: IO ()
repll = display_help >> getArgs >>= mk_explorer >>= (runInputT defaultSettings . repl')
 where 
  repl' exp = do
   getInputLine ("#" ++ show (EI.currRef exp) ++ " > ") >>= \case 
    Nothing    -> return ()
    Just input -> do
      case break isSpace input of
        (":help",_)       -> lift display_help >> repl' exp
        (":h",_)          -> lift display_help >> repl' exp
        (":quit",_)       -> return ()
        (":q",_)          -> return ()
        (":env",_)        -> lift (display_environment (EI.config exp)) >> repl' exp 
        (":environment",_)-> lift (display_environment (EI.config exp)) >> repl' exp
        (":store",_)      -> lift (display_mut_entity (EI.config exp) "store") >> repl' exp
        (":sto",_)        -> lift (display_mut_entity (EI.config exp) "store") >> repl' exp
        (":mut", rest)    -> lift (display_mut_entity (EI.config exp) (dropWhile isSpace rest)) >> repl' exp 
        (":mutable", rest)-> lift (display_mut_entity (EI.config exp) (dropWhile isSpace rest)) >> repl' exp 
        (":session", _)   -> do
          (outputStrLn . drawTree . fmap (show . fst) . EI.toTree) exp
          repl' exp
        (":revert", mint) | Just ref_id' <- readMaybe (dropWhile isSpace mint)
                          -> lift (handle_revert ref_id' exp)  >>= repl'
                          | otherwise -> outputStrLn "Revert requires an integer argument" >> repl' exp
        (":debug", mfct)  -> case fct_parse_either (dropWhile isSpace mfct) of
                              Left err -> outputStrLn err >> repl' exp
                              Right fct -> lift (EI.execute (Debug fct) exp) >>= (repl' . fst)
        (":step", _)      -> lift (EI.execute Step exp) >>= (repl' . fst)
        (":small-step", _)-> lift (EI.execute SmallStep exp) >>= (repl' . fst)
        (":pretty-big-step", _)      -> lift (EI.execute PrettyBigStep exp) >>= (repl' . fst)
        (":finish", _)    -> lift (EI.execute Finish exp) >>= (repl' . fst)
        _                 -> case fct_parse_either input of 
                                 Left err  -> outputStrLn err >> repl' exp 
                                 Right fct -> lift (EI.execute (FTerm fct) exp) >>= (repl'  . fst)


mk_interpreter :: [String] -> IO (RunOptions, Config)
mk_interpreter args = do 
  (opts, unknown_opts) <- run_options args
  forM_ unknown_opts $ \arg -> do
      putStrLn ("unknown option: " ++ arg) 
  opts_ref <- newIORef opts 
  cfg <- mk_initial_config library entities typeenv opts
  return (opts, cfg)
  where 
    library = libUnions [ Funcons.Core.Library.funcons, Funcons.EDSL.library, Funcons.Core.Manual.library ]
    entities = Funcons.Core.Library.entities 
    typeenv = Funcons.Core.Library.types


 
mk_explorer :: [String] -> IO Explorer 
mk_explorer args = do
  (opts, unknown_opts) <- run_options args
  forM_ unknown_opts $ \arg -> do
      putStrLn ("unknown option: " ++ arg) 
  opts_ref <- newIORef opts 
  cfg <- mk_initial_config library entities typeenv opts
  return $ EI.mkExplorer False (const . const $ False) (\f c -> (\c -> (c, ())) <$> def_interpreter opts_ref f c) cfg
 where
  library = libUnions [ Funcons.Core.Library.funcons, Funcons.EDSL.library, Funcons.Core.Manual.library ]
  entities = Funcons.Core.Library.entities 
  typeenv = Funcons.Core.Library.types

mk_initial_config :: FunconLibrary -> EntityDefaults -> TypeRelation -> RunOptions -> IO Config
mk_initial_config lib defaults tyenv opts = do
  let msos_ctxt = MSOSReader (RewriteReader lib tyenv opts f0 f0) emptyINH emptyDCTRL (fread (string_inputs opts))
  ((e_exc_f, mut, wr), rem_ins) <- 
      fexec (runMSOS (setEntityDefaults defaults (loop opts f0))
              msos_ctxt ((emptyMSOSState (random_seed opts)) {inp_es = M.empty})) (inputValues opts)
  return $ Config { reader = init msos_ctxt, state = mut, progress = done }
  where f0 = initialise_binding_ [initialise_storing_ [map_empty_ []]]
        init msos_reader = msos_reader {inh_entities = M.insert "environment" [Map M.empty] (inh_entities msos_reader) }

def_interpreter :: IORef RunOptions -> Phrase -> Config -> IO (Maybe Config)
def_interpreter opts_ref phrase cfg = do 
  opts <- readIORef opts_ref 
  case phrase of FTerm f0' -> let f0 = prep_term f0'
                              in fmap (setProgress done) <$> exec opts (loop opts) f0 (prep_ctxt f0 opts) []
                 Debug f0' -> let f0 = prep_term f0'
                              in putStrLn ("\nremaining funcon term:\n" ++ ppFuncons opts f0) 
                              >> return (Just (cfg { progress = Left f0 }))
                 Step      -> case progress cfg of 
                                Left fct  -> mk_step opts fct
                                Right vs  -> putStrLn "already done.." >> return (Just cfg)
                 SmallStep -> case progress cfg of 
                                Left fct  -> mk_step (turn_off_refocus opts) fct
                                Right vs  -> putStrLn "already done.." >> return (Just cfg)
                 PrettyBigStep -> case progress cfg of 
                                Left fct  -> mk_step (turn_on_refocus opts) fct
                                Right vs  -> putStrLn "already done.." >> return (Just cfg)
                 Finish    -> case progress cfg of
                                Left fct  -> fmap (setProgress done) <$> exec opts (loop opts) fct (prep_ctxt fct opts) [] 
                                Right vs  -> putStrLn "already done.." >> return (Just cfg)
 where prep_term f0' =
        give_ [f0', 
          give_ [if_else_ [is_ [given_, environments_], given_
                          ,if_else_ [is_ [given_, null_type_], given_
                                    ,bind_ [Funcons.EDSL.string_ "it", given_]]]
                ,if_else_ [is_ [given_, null_type_], given_
                          ,sequential_ [print_ [given_,Funcons.EDSL.string_ "\n"], given_]]]]
       prep_ctxt f0 opts = (reader cfg) { ereader = (ereader (reader cfg)) { local_fct = f0, global_fct = f0, run_opts = opts } }
       mk_step opts f0 = do im <- exec opts step f0 (prep_ctxt f0 opts) []
                            case im of Just cfg -> case progress cfg of 
                                                     Left fct -> putStrLn ("\nremaining funcon term:\n" ++ ppFuncons opts fct)
                                                     _        -> return ()
                                       Nothing -> return ()
                            return im

       exec opts stepper f0 msos_ctxt nd_choices = do 
        (e_exc_f, mut, wr) <- runMSOS (stepper f0) msos_ctxt (setNDs nd_choices $ state cfg)
        case e_exc_f of
          Left (_,local,NDEncounter ndsrc) -> do
            putStrLn (ndtype ++ " non-determinism encountered in: " ++ ppFuncons opts local)
            nd_choice <- runInputT defaultSettings (nd_selection opts ndsrc)
            exec opts stepper f0 msos_ctxt (nd_choices++[nd_choice])
           where ndtype = case ndsrc of NDInputInterleaving _ -> "interleaving"
                                        NDInputValueOperations _ -> "value-operation"
                                        NDInputPattern _ -> "pattern" 
          Left ie    -> putStrLn (showIException ie) >> return Nothing 
          Right (Left fct) -> return $ Just $ cfg { state = mut, progress = Left fct} -- did not yield an environment
          Right (Right efvs) -> case filter isMap efvs of
            []    -> return $ Just $ cfg { state = mut, progress = Right efvs }
            [env] -> return $ Just $ cfg { reader = accumulate (reader cfg) env, state = mut, progress = Right efvs } 
            _     -> putStrLn ("multiple environments computed") >> return Nothing
        where accumulate msos_reader env = msos_reader { inh_entities = M.update override "environment" (inh_entities msos_reader) }
                where override [old_env] = case (env, old_env) of 
                        (Map m1, Map m2) -> Just [Map (M.union m1 m2)] 
                        _                -> Nothing
                      override _ = Nothing

loop :: RunOptions -> Funcons -> MSOS StepRes
loop opts = stepTrans opts 0 . toStepRes

step :: Funcons -> MSOS StepRes
step = stepAndOutput

done :: StepRes
done = Right []

setProgress :: StepRes -> Config -> Config
setProgress res cfg = cfg { progress = res }

setNDs :: [Int] -> MSOSState m -> MSOSState m
setNDs is ctxt = ctxt { estate = (estate ctxt) { nd_choice = is } }

-- assumes all components of RewriteReader do not change per session
instance Eq (MSOSReader IO) where
  r1 == r2 = inh_entities r1 == inh_entities r2 
          && dctrl_entities r1 == dctrl_entities r2

-- assumes input is not used // does not change per session
instance Eq (MSOSState IO) where
  s1 == s2 = mut_entities s1 == mut_entities s2 

nd_selection :: RunOptions -> NDInput -> InputT IO Int
nd_selection opts ndsrc = do
  lift $ putStrLn "choose from the following alternatives:"
  lift $ forM_ (zip [1..] alts) (\(i,str) -> 
    putStrLn (show i ++ ") " ++ str)
    )
  mint <- getInputLine ("by selecting a number between " ++ show 1 ++ " and " ++ show m ++ "\n>")
  case join (fmap readMaybe mint) of
    Just i | i >= 1 && i <= m -> return (i-1)
    otherwise                 -> nd_selection opts ndsrc
  where m = length alts
        alts = case ndsrc of
          NDInputValueOperations eress -> concatMap display eress
            where display (Error _ _)         = []
                  display (EvalResults eress) = concatMap display eress
                  display (Success fct)       = [ppFuncons opts fct]
          NDInputInterleaving fcts -> map (ppFuncons opts) fcts
          NDInputPattern iis -> map toStr iis
            where toStr (k, r) = "variable #" ++ show (k+1) ++ " matching " ++ show r ++ " values"

display_environment :: Config -> IO ()
display_environment cfg =
  mapM_ (putStrLn . showValues) (inh_entities (reader cfg) M.! "environment")

display_mut_entity :: Config -> String -> IO ()
display_mut_entity cfg ent = 
  case M.lookup (pack ent) (mut_entities (state cfg)) of 
    Nothing -> putStrLn ("unknown mutable entity: " ++ ent)
    Just v  -> putStrLn $ showL (map showValues v)

display_help :: IO ()
display_help =
  putStrLn  "Available commands:\n\
            \  :environment :env    show the active bindings from identifiers to values\n\
            \  :store :sto          show the store with assignments to references\n\
            \  :mutable :mut <ENT>  show the mutable entity with name <ENT>\n\
            \  :session             displays the explored traces in the form of a tree\n\
            \                       with nodes labelled by state identifiers\n\
            \  :revert <INT>        revert to the state with id <INT>\n\
            \  :debug <FCT>         start step-by-step execution of funcon term <FCT>\n\
            \  :step                perform the next step in a step-by-step execution (without changing the refocusing setting)\n\
            \  :pretty-big-step     perform the next step in a step-by-step execution with refocusing\n\
            \  :small-step          perform the next step in a step-by-step execution without refocusing\n\
            \  :finish              perform all remaining steps of a step-by-step execution\n\
            \  :help :h             show these commands\n\
            \  :quit :q             end the exploration\n\
            \  or just type a funcon term"


type DebugConfig = DFunconsConfig

data BooleanBreakpoint b = And (BooleanBreakpoint b) (BooleanBreakpoint b) | Or (BooleanBreakpoint b) (BooleanBreakpoint b) | B b
data StoreBreakpoint = StoreBreakpoint {atom_id :: Int, val :: Funcons.EDSL.Values}


instance MVD.Reduce () DebugConfig DebugConfig where 
    rstate _ c = c

instance MVD.Evaluate DebugConfig DebugConfig Bool where 
    estate goal curr = goal == curr 
-- lib_single = Funcons.MSOS.libUnions [ Funcons.Core.Library.funcons, Funcons.EDSL.library, Funcons.Core.Manual.library ]
-- entities_single = Funcons.Core.Library.entities 
-- typeenv_single = Funcons.Core.Library.types

-- f0_single = Funcons.Core.Library.initialise_binding_ [Funcons.Core.Library.initialise_storing_ [Funcons.Core.Manual.map_empty_ []]]
fvalue_to_value :: Funcons -> Funcons.EDSL.Values
fvalue_to_value (FValue v) = v
fvalue_to_value _ = error "is not a value"

brv :: Funcons.EDSL.Values
brv = fvalue_to_value $ fct_parse "2"

store :: Config ->  Funcons.EDSL.Values
store cfg = 
  case M.lookup "store" (mut_entities $ state cfg) of
        Nothing -> error ""
        (Just store_list) -> case length store_list > 1 of
            True ->  error ""
            _ ->  head store_list

convert (Map x) = x 
instance (MVD.Evaluatem b DebugConfig Bool) => MVD.Evaluatem (BooleanBreakpoint b) DebugConfig Bool where
   estatem (B c) cfg = MVD.estatem c cfg
   estatem (And c1 c2) cfg = liftM2 (&&) (MVD.estatem c1 cfg) (MVD.estatem c2 cfg)
   estatem (Or c1 c2) cfg = liftM2 (||) (MVD.estatem c1 cfg) (MVD.estatem c2 cfg)

instance MVD.Evaluatem StoreBreakpoint DebugConfig (Bool) where
   estatem :: StoreBreakpoint -> DebugConfig -> IO Bool
   estatem condition (DFunconsConfig config _ _  opts _)  = do
      let s = convert $ store config
      putStrLn $ show s
      -- putStrLn $ show $ Atom "1"
      putStrLn $ show $ M.lookup (Atom $ "@" ++ show (atom_id condition)) s
      -- return False
      case M.lookup (Atom $ "@" ++ show (atom_id condition)) s of
        Nothing -> return False
        (Just [v]) -> do
          -- print "WOOOOOO"
          return $  v == val condition
        _ -> return False


instance Show Config where 
  show c = show (progress c)

-- def 
-- data Funcons    = FName Name
--                 | FApp Name [Funcons]
-- --                | FTuple [Funcons]
-- --                | FList [Funcons]
--                 | FSet [Funcons]
--                 | FMap [Funcons]
--                 | FBinding Funcons [Funcons] -- required for map-notation
--                 | FValue Values
--                 | FSortSeq Funcons VAL.SeqSortOp
--                 | FSortPower Funcons Funcons {- evals to natural number -}
--                 | FSortUnion Funcons Funcons
--                 | FSortInter Funcons Funcons
--                 | FSortComplement Funcons
--                 | FSortComputes Funcons
--                 | FSortComputesFrom Funcons Funcons 
--                 deriving (Eq, Ord, Show, Read)

-- swap :: Funcons -> Funcons -> Funcons -> IO Funcons
-- swap to_be_replaced new term
--     | term == to_be_replaced = return new
--     | otherwise = case term of
--         t@(FApp n l) ->
--             if n == "sequential" then do
--               -- putStrLn "Term"
--               -- putStrLn $ show to_be_replaced
  
--               -- putStrLn "FApp"
--               -- putStrLn $ show t
--               -- putStrLn $ show $ t == to_be_replaced

--               -- l' <- mapM (swap to_be_replaced new) l
--               return $ FApp n [new]
--               -- l'
--             else do
--               l' <- mapM (swap to_be_replaced new) l
--               return $ FApp n l'
--         FSet l -> do
--             l' <- mapM (swap to_be_replaced new) l
--             return $ FSet l'
--         FMap l -> do
--             l' <- mapM (swap to_be_replaced new) l
--             return $ FMap l'
--         FBinding f l -> do
--             f' <- swap to_be_replaced new f
--             l' <- mapM (swap to_be_replaced new) l
--             return $ FBinding f' l'
--         FSortSeq f op -> do
--             f' <- swap to_be_replaced new f
--             return $ FSortSeq f' op
--         FSortPower f1 f2 -> do
--             f1' <- swap to_be_replaced new f1
--             f2' <- swap to_be_replaced new f2
--             return $ FSortPower f1' f2'
--         FSortUnion f1 f2 -> do
--             f1' <- swap to_be_replaced new f1
--             f2' <- swap to_be_replaced new f2
--             return $ FSortUnion f1' f2'
--         FSortInter f1 f2 -> do
--             f1' <- swap to_be_replaced new f1
--             f2' <- swap to_be_replaced new f2
--             return $ FSortInter f1' f2'
--         FSortComplement f -> do
--             f' <- swap to_be_replaced new f
--             return $ FSortComplement f'
--         FSortComputes f -> do
--             f' <- swap to_be_replaced new f
--             return $ FSortComputes f'
--         FSortComputesFrom f1 f2 -> do
--             f1' <- swap to_be_replaced new f1
--             f2' <- swap to_be_replaced new f2
--             return $ FSortComputesFrom f1' f2'
--         _ -> return term

--     | term == to_be_replaced = new
--     | otherwise = case term of
--         FApp n l -> FApp n (map (swap to_be_replaced new) l)
--         FSet l         -> FSet (map (swap to_be_replaced new) l)
--         FMap l         -> FMap (map (swap to_be_replaced new) l)
--         FBinding f l     -> FBinding (swap to_be_replaced new f) (map (swap to_be_replaced new) l)
--         FSortSeq f op  -> FSortSeq (swap to_be_replaced new f) op
--         FSortPower f1 f2 -> FSortPower (swap to_be_replaced new f1) (swap to_be_replaced new f2)
--         FSortUnion f1 f2 -> FSortUnion (swap to_be_replaced new f1) (swap to_be_replaced new f2)
--         FSortInter f1 f2 -> FSortInter (swap to_be_replaced new f1) (swap to_be_replaced new f2)
--         FSortComplement f -> FSortComplement (swap to_be_replaced new f)
--         FSortComputes f -> FSortComputes (swap to_be_replaced new f)
--         FSortComputesFrom f1 f2 -> FSortComputesFrom (swap to_be_replaced new f1) (swap to_be_replaced new f2)
--         _              -> term

find_scopes :: Funcons -> [Funcons]
find_scopes term = find_scopes' term []
  where
    find_scopes' :: Funcons -> [Funcons] -> [Funcons]
    find_scopes' term found = case term of
        t@(FApp n l) -> 
            let new_found = if n == "scope" 
                            then t : found 
                            else found
            in foldr find_scopes' new_found l
        FSet l         -> foldr find_scopes' found l
        FMap l         -> foldr find_scopes' found l
        FValue vals ->  find_scopes_vals found vals
        FBinding f l   -> find_scopes' f found ++ foldr find_scopes' found l
        FSortSeq f op  -> find_scopes' f found
        FSortPower f1 f2 -> find_scopes' f1 found ++ find_scopes' f2 found
        FSortUnion f1 f2 -> find_scopes' f1 found ++ find_scopes' f2 found
        FSortInter f1 f2 -> find_scopes' f1 found ++ find_scopes' f2 found
        FSortComplement f -> find_scopes' f found
        FSortComputes f -> find_scopes' f found
        FSortComputesFrom f1 f2 -> find_scopes' f1 found ++ find_scopes' f2 found
        _              -> found
        
    find_scopes_vals :: [Funcons] -> Funcons.Types.Values -> [Funcons]
    find_scopes_vals found term= case term of
        (ADTVal _ l) -> foldr find_scopes' found l
        _          -> found

      
-- swap_main = swap $ fct_parse "apply(assigned(bound(\"main\")),tuple( ))"



-- instance MVD.Evaluatem Funcons DebugConfig (Bool) where 
--     estatem :: Funcons -> DebugConfig -> IO Bool
--     estatem break (DFunconsConfig config _ _  opts) = do
--       case progress config of 
--         (Left f) -> do
--           putStrLn "T"
--           -- putStrLn $ show $ fct_parse "apply(assigned(bound(\"main\")))"
--           putStrLn $ show $ progress config

          
--           n <- swap_main break $ f
--           putStrLn $ show n

--           (e_exc_f, mut, wr) <- runMSOS (stepTrans opts 0 (toStepRes n)) (reader config) ( state config)
--           putStrLn $ show e_exc_f
--           putStrLn $ show$ inh_entities $ reader config
--           putStrLn $ show$ mut_entities $ state config

--           -- return False

--           case e_exc_f of 
--             (Left _) -> return False
--             (Right stepres) -> case stepres of
--               (Left _) -> return False
--               (Right vals) -> if null vals then return False else
--                 case frombool $ head vals of
--                   (Just True) -> return True
--                   _ -> return False

--         _ -> return False -- TODO

-- Seach for environments
-- instance MVD.Evaluatem Funcons DebugConfig (Bool) where 
--     estatem :: Funcons -> DebugConfig -> IO Bool
--     estatem break (DFunconsConfig config _ _  opts) = do
--       let inh = inh_entities $ reader config
--       putStrLn $ show inh
--       case M.lookup "environment" inh of 
--         Nothing -> return False
--         (Just e) -> case M.null (convert $ head e) of 
--           True -> return False 
--           _ -> do 
--             putStrLn $ show (convert $ head e)
--             return True

-- used for debugging 
-- instance MVD.Evaluatem Funcons DebugConfig (Bool) where 
--     estatem :: Funcons -> DebugConfig -> IO Bool
--     estatem break dc@(DFunconsConfig config _ _  opts) = do
--       printDFunconsConfig opts dc
--       putStrLn $ show $ mut_entities $ state config
--       let inh = inh_entities $ reader config
--       putStrLn $ show inh
--       case M.lookup "environment" inh of 
--         Nothing -> return False
--         (Just e) -> case M.null (convert $ head e) of 
--           True -> return False 
--           _ -> do 
--             putStrLn $ show (convert $ head e)
--             return True

scope_target (FApp v x) = head $ reverse x

strore_not_empty ::  M.Map Name [Funcons.EDSL.Values] -> IO Bool
strore_not_empty mut = case M.lookup "store" mut of 
  Nothing -> return $ False 
  (Just x) -> do 
    putStrLn $ show $ convert ( head x)
    putStrLn $ show $ M.null $ convert ( head x)
    return $ not$ M.null $ convert ( head x)
    --  M.null $ x   

estatemtest :: Funcons -> DebugConfig -> IO Bool
estatemtest break dc@(DFunconsConfig config _ _  opts _) = do
  case progress config of 
    (Left f) -> do

      let p = head $ reverse  $ find_scopes f

      
      let s = convert $ head $ fromJust $ M.lookup "store" $   mut_entities $ state config

      let rest =  M.delete "store" $ mut_entities $ state config

      let functions = filter (\(k,v) -> and $ map isFunction v) (M.toList s)
      case null functions of
        True -> return False
        _ -> do 
          let (_, (funcons_values_main)) = head functions
              -- We assume funcons_values_main to be a singleton
              (ADTVal name funcons) = head $ funcons_values_main
              -- scope = head $ find_scopes $ head funcons
          case null funcons of 
            False -> case null $ find_scopes $ head funcons of
              False -> do
                -- putStrLn $ show $ head funcons
                let scope = head $ reverse $  find_scopes $ head funcons
                    (FApp "scope" internal) = scope
                    -- now we swap in the breakpoint
                    new_scope = (FApp "scope" (init internal ++ [break]))

                (e_exc_f, mut, wr) <- runMSOS (stepTrans opts 0 (toStepRes new_scope)) (reader config) ( state config)
        
                return $ isTrue $ fmap (\x -> map frombool x) $ fromRight $ e_exc_f

              True -> return False
            True -> return False

    _ -> 

        return False

  
  where 
    isFunction (ADTVal "function" _) = True
    isFunction _ = False

    fromRight( Right(Right x )) = Just x
    fromRight _ = Nothing

    isTrue(Just [Just True]) = True
    isTrue _ = False

-- extract scopes 
instance MVD.Evaluatem Funcons DebugConfig (Bool) where 
    estatem :: Funcons -> DebugConfig -> IO Bool
    estatem break dc@(DFunconsConfig config _ _  opts _) = do
      -- putStrLn $ show $ progress config
      case progress config of 
        (Left f) -> do
          -- putStrLn "scopes"
          
          -- putStrLn $ show $ find_scopes f
          -- putStrLn $ show $ "size" ++ (show $ length $ find_scopes f)
          let p = head $ reverse  $ find_scopes f
          -- putStrLn $ show p
          -- putStrLn $ "target"
          -- putStrLn $ show $ scope_target p
          -- putStrLn $ "mu"
          -- putStrLn $ show $ mut_entities $ state config
          -- putStrLn $ "store: "
          
          let s = convert $ head $ fromJust $ M.lookup "store" $   mut_entities $ state config
          -- forM_  (M.toList s) (\(key, val) -> do 
          --     putStrLn $ "key:" ++ show key
          --     putStrLn $ showValuesSeq val
          --     putStrLn $ show $ map isFunction val
          --   )
          let rest =  M.delete "store" $ mut_entities $ state config
          putStrLn $ show $ M.map showValuesSeq rest

          -- putStrLn "tessssssssssssss"

          -- putStrLn $  show f
          -- TODO
          -- Here we want to find the atom to which the main function is bound. This atom is mapped to a function that has a scope that contains the bindings between variables names and atoms, that we want to target with these breakpoints.
          -- For now we just assume there is only one function.

          let functions = filter (\(k,v) -> and $ map isFunction v) (M.toList s)
          case null functions of
            True -> return False
            _ -> do 
              let (_, (funcons_values_main)) = head functions
                  -- We assume funcons_values_main to be a singleton
                  (ADTVal name funcons) = head $ funcons_values_main
                  -- scope = head $ find_scopes $ head funcons
              case null funcons of 
                False -> case null $ find_scopes $ head funcons of
                  False -> do
                    -- putStrLn $ show $ head funcons
                    putStrLn $ "last scope"
                    let scope = head $ reverse $  find_scopes $ head funcons
                        (FApp "scope" internal) = scope
                        -- now we swap in the breakpoint
                        new_scope = (FApp "scope" (init internal ++ [break]))

                    (e_exc_f, mut, wr) <- runMSOS (stepTrans opts 0 (toStepRes new_scope)) (reader config) ( state config)
                    let ret = isTrue $ fmap (\x -> map frombool x) $ fromRight $ e_exc_f
                    putStrLn $ "ret" ++  (show $ ret)
                    b <- estatemtest break dc
                    putStrLn $ "Return val:" ++ show b
                    return $ ret
                    -- return True

                  True -> return False
                True -> return False


        _ -> 
            -- do
            -- putStrLn "" 
            return False
      -- strore_not_empty (mut_entities $ state config)
      -- return False
      
      where 
        isFunction (ADTVal "function" _) = True
        isFunction _ = False

        fromRight( Right(Right x )) = Just x
        fromRight _ = Nothing

        isTrue(Just [Just True]) = True
        isTrue _ = False
      -- printDFunconsConfig opts dc
      -- putStrLn $ show $ mut_entities $ state config
      -- let inh = inh_entities $ reader config
      -- putStrLn $ show inh
      -- case M.lookup "environment" inh of 
      --   Nothing -> return False
      --   (Just e) -> case M.null (convert $ head e) of 
      --     True -> return False 
      --     _ -> do 
      --       putStrLn $ show (convert $ head e)
      --       return True
    -- where remov 

-- repl :: IO ()
-- repl = getArgs >>= mk_interpreter >>= (runInputT defaultSettings . buildDebugger)
--   where buildDebugger (runopts, cfg) = do
--           getInputLine " > " >>= \case
--             Nothing -> return ()
--             (Just input) -> do
--                 case fct_parse_either input of 
--                   Left err  -> outputStrLn err
--                   Right fct -> do 
--                     -- getInputLine "Give a funcon term as a breakpoint > " >>= \case
--                     --   Nothing -> lift $ MVD.debugger (printDFunconsConfig runopts) (putStrLn . showFunconsActions runopts) (funconsSTR runopts (debugExecute runopts) (cfg { progress = Left fct})) MVD.equalityFinder (DFunconsConfig { nconfig = cfg, ndeter = Nothing }) ()

--                       -- (Just break) -> do
--                         -- case fct_parse_either break of 
--                         --   Left err  -> outputStrLn err
--                         --   Right fct_break -> do 
--                             lift $ MVD.debuggerm (printDFunconsConfig runopts) (putStrLn . showFunconsActions runopts) (funconsSTR runopts (debugExecute runopts) (cfg { progress = Left fct})) MVD.equalityFinderm (
--                               And (B $ StoreBreakpoint 1 brv) (B $ (StoreBreakpoint 1 brv))) ()

repl :: IO ()
repl = getArgs >>= mk_interpreter >>= (runInputT defaultSettings . buildDebugger)
  where buildDebugger (runopts, cfg) = do
          getInputLine " > " >>= \case
            Nothing -> return ()
            (Just input) -> do
                case fct_parse_either input of 
                  Left err  -> outputStrLn err
                  Right fct -> do 
                    getInputLine "Give a funcon term as a breakpoint > " >>= \case
                      Nothing -> lift $ MVD.debugger (printDFunconsConfig runopts) (putStrLn . showFunconsActions runopts) (funconsSTR runopts (debugExecute runopts) (cfg { progress = Left fct})) MVD.equalityFinder (DFunconsConfig { nconfig = cfg, ndeter = Nothing }) ()

                      (Just break) -> do
                        case fct_parse_either break of 
                          Left err  -> outputStrLn err
                          Right fct_break -> do 
                            lift $ MVD.debuggerm (printDFunconsConfig runopts) (putStrLn . showFunconsActions runopts) (funconsSTR runopts (debugExecute runopts) (cfg { progress = Left fct})) MVD.equalityFinderm fct_break ()

                        


data FunconsActions = FStep | NDChoice Int NDInput


showFunconsActions :: RunOptions -> FunconsActions -> String
showFunconsActions _ FStep = "Step"
showFunconsActions opts (NDChoice i (NDInputInterleaving [f])) = 
  "Choose: " ++ ppFuncons opts f
showFunconsActions opts (NDChoice i (NDInputValueOperations [s])) = 
  "Pick value: " ++ display s
  where display (Error _ _)         = ""
        display (EvalResults eress) = concatMap display eress
        display (Success fct)       = join [ppFuncons opts fct]
showFunconsActions opts (NDChoice i (NDInputPattern k)) = 
  concatMap toStr k
  where toStr (k, r) = "variable #" ++ show (k+1) ++ " matching " ++ show r ++ " values"

data DFunconsConfig = DFunconsConfig { nconfig :: Config, ndeter :: Maybe (Funcons, NDInput), ndchoice :: [Int], opts :: RunOptions, count :: Int }

printDFunconsConfig :: RunOptions -> DFunconsConfig -> IO ()
printDFunconsConfig opts c 
  | isJust (ndeter c) = do
    putStr "Current term: "
    putStrLn $ showProgress opts (progress $ nconfig c)
    -- putStrLn $ show $ mut_entities $ state $ nconfig c
    -- putStrLn $ show $ inh_entities $ reader $ nconfig c

    putStrLn $ "Non-determinism choice at: " ++ ppFuncons opts (fst . fromJust . ndeter $ c)
  | otherwise =  do
    putStr "Current term: "
    putStrLn $ showProgress opts (progress $ nconfig c)
    -- putStrLn $ show $ mut_entities $ state $ nconfig c
    -- putStrLn $ show $ inh_entities $ reader $ nconfig c
    -- show $ c
    
    -- showProgress opts (progress $ nconfig c)


instance Eq DFunconsConfig where 
  d1 == d2 = nconfig d1 == nconfig d2  && ndeter d1 == Nothing && ndeter d2 == Nothing 
  -- ss&& ndeter d1 == ndeter d2

-- Funcons [Values]
showProgress :: RunOptions -> StepRes -> String
showProgress opts (Left f) = ppFuncons opts f
showProgress _ (Right [vs]) = show vs
showProgress _ (Right vs) = show vs

instance Show DFunconsConfig where 
  show c = case ndeter c of 
    Nothing -> (showProgress (opts c) . progress $ nconfig c) ++ "\n" ++ "Mut:\n"++ show ( mut_entities $ state$ nconfig c)
    (Just (l, _)) -> show (nconfig c) ++ "\n" ++ "Has non-determinism: " ++ ppFuncons (opts c) l ++ "\n" ++ "Mut:\n"++ show ( mut_entities $ state$ nconfig c)


debugExecute :: RunOptions -> DFunconsConfig -> IO [DFunconsConfig]
debugExecute opts dcfg = do 
  case progress cfg of 
      Left fct  -> mk_step opts fct
      Right vs  -> return [dcfg]
  where 
        cfg = nconfig dcfg
        mk_step opts f0 = exec opts (loop opts) f0 (prep_ctxt f0 opts) (ndchoice dcfg)
        
        prep_ctxt :: Funcons -> RunOptions -> MSOSReader IO
        prep_ctxt f0 opts = (reader cfg) { ereader = (ereader (reader cfg)) { local_fct = f0, global_fct = f0, run_opts = opts } }

        exec :: t -> (t1 -> MSOS (Either Funcons [Funcons.Operations.Values Funcons])) -> t1 -> MSOSReader IO -> [Int] -> IO [DFunconsConfig]
        exec opts stepper f0 msos_ctxt nd_choices = do 
          (e_exc_f, mut, wr) <- runMSOS (stepper f0) msos_ctxt (setNDs nd_choices $ state cfg)
          case e_exc_f of
            Left (curr, local, NDEncounter ndsrc) -> do 
              -- putStrLn "C1"
              -- putStrLn ""
              -- putStrLn $ show curr
              -- putStrLn ""
              -- putStrLn $ show local
              -- putStrLn ""

              -- putStrLn $ show $ mut_entities mut
              -- putStrLn $ show $ inh_entities msos_ctxt

              -- putStrLn ""
              return [dcfg {ndeter = Just (local, ndsrc), nconfig = (nconfig dcfg){state = mut} , count = 1 + count dcfg} ]
            Left ie    -> putStrLn (showIException ie) >> return []
            Right (Left fct) -> do 
              return $ [dcfg { nconfig = cfg { state = mut, progress = Left fct}, count = 1 + count dcfg}] -- did not yield an environment
            Right (Right efvs) -> case filter isMap efvs of
              []    -> do
                return $ [dcfg { nconfig = cfg { state = mut, progress = Right efvs } , count = 1 + count dcfg}]
              [env] -> do
                -- print env
                
                return $ [dcfg { nconfig = cfg { reader = accumulate (reader cfg) env, state = mut, progress = Right efvs } , count = 1 + count dcfg} ]
              _     -> return [] 
          where accumulate msos_reader env = msos_reader { inh_entities = M.update override "environment" (inh_entities msos_reader) }
                  where override [old_env] = case (env, old_env) of 
                          (Map m1, Map m2) -> Just [Map (M.union m1 m2)] 
                          _                -> Nothing
                        override _ = Nothing


debugActions :: DFunconsConfig -> [FunconsActions]
debugActions c = case ndeter c of 
  Nothing -> [FStep]
  (Just (local, NDInputInterleaving l)) -> [NDChoice i (NDInputInterleaving [(l !! i)]) | i <- [0..length l - 1]]
  (Just (local, NDInputPattern l)) ->  [NDChoice i (NDInputPattern [(l !! i)]) | i <- [0..length l - 1]]
  (Just (local, NDInputValueOperations l)) -> [NDChoice i (NDInputValueOperations [(l !! i)]) | i <- [0..length l - 1]]


debugExecute' interp c p = 
  case p of 
    FStep -> unsafePerformIO $ interp c
    (NDChoice i _) -> unsafePerformIO $ interp (c { ndchoice = ndchoice c ++ [i], ndeter = Nothing })

funconsSTR :: RunOptions -> (DFunconsConfig -> IO [DFunconsConfig]) -> Config -> MVD.STR DFunconsConfig FunconsActions
funconsSTR ropts interp c = MVD.STR 
  { MVD.initial = [DFunconsConfig { nconfig = c, ndeter = Nothing, ndchoice = [], opts = ropts , count = 0}]
  , MVD.actions = debugActions
  , MVD.execute = debugExecute' interp
  }