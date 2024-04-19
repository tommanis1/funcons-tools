{-# LANGUAGE TupleSections, FlexibleInstances, OverloadedStrings,ScopedTypeVariables #-}

module Test where 
import Funcons.MSOS
import Funcons.GLLParser
import qualified Data.Map as M

import Funcons.Core
import Funcons.Core.Library
import Funcons.Core.Manual
import Funcons.EDSL hiding (isMap)
import Funcons.RunOptions (defaultRunOptions, string_inputs)
import Funcons.Explorer
import Funcons.RunOptions

-- import Data.Text (unpack)
import Funcons.MetaProgramming (cmp_MSOSReader)
import Funcons.Simulation
test :: MSOS [MSOS StepRes]
test = Funcons.MSOS.stepAndOutput (fromRight $ fct_parse_either "some-element {11,22,33}")

-- | Take a Right to a value, crashes on a Left
fromRight :: Either a b -> b
fromRight (Right a) = a
fromRight _         = error "Data.Either.Utils.fromRight: Left"

show :: StepRes -> String
show (Left _) = ":("
show (Right vals) = showValuesSeq vals 

-- printTest :: MSOS IO
printTest :: IO [IO ()]
printTest = do 

        -- let f = fromRight $ fct_parse_either "some-element {11,22,33}"
        (opts, _) <- run_options ["non-deterministic"]
        let msos_context :: MSOSReader IO  = MSOSReader (RewriteReader lib typeenv defaultRunOptions f0 f0) emptyINH emptyDCTRL (fread (string_inputs opts))

        let m =  fexec( runMSOS (test) msos_context ((emptyMSOSState (random_seed opts)) {inp_es = M.empty}) ) (inputValues opts)
        
        ((e_exc_f, mut, wr), rem_ins) <- m
        let l = fromRight e_exc_f
        let q = map (\x -> fexec (runMSOS x msos_context ((emptyMSOSState (random_seed opts)) {inp_es = M.empty}) ) (inputValues opts)) l
        let z = map (\x -> do 
                ((e_exc_f, mut, wr), rem_ins) <- x
                let r = fromRight e_exc_f
                putStrLn $ Test.show r
                    )q
        sequence z 
        return z

    --         -- MSOSReader (RewriteReader lib typeenv defaultRunOptions f f) emptyINH  emptyDCTRL (\x -> fvalue_parse_either $ unpack x)
      
    -- --   runMSOS (setEntityDefaults defaults (chooseRandomOption $ loop opts f0))
    -- --           msos_ctxt ((emptyMSOSState (random_seed opts)) {inp_es = M.empty})
    -- -- v <- test
    -- -- Test.show $ head v

    --     let z = runMSOS test msos_ctxt (emptyMSOSState 1) 
    --     let (q, _, _) = fromRight z
    --         results = fromRight q
    --         -- out = map fromRight results

    --     map (\x -> do 
    --         l <- x
    --         putStrLn $ Test.show l ) results
    where
            f0 = initialise_binding_ [initialise_storing_ [map_empty_ []]]

            lib = libUnions [ Funcons.Core.Library.funcons, Funcons.EDSL.library, Funcons.Core.Manual.library ]
            entities = Funcons.Core.Library.entities 
            typeenv = Funcons.Core.Library.types