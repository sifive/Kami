
{-
	Example of how to simulate a module using IncrementerImpl extracted from Tutorial.v
-}

module Main where

import HaskellTarget as T
import Simulator.All
import ExampleExtract

ruleNames :: [String]
ruleNames = 
    [
          "test.send"
        , "test.inc"
        
    ]

meths :: [(String, Val -> IO Val)]
meths = [("counterVal", \v -> do
                                putStrLn $ printVal (fullFormatHex (T.Bit 5)) v 
                                return (BitvectorVal []))]

main :: IO()
main = do
    simulate_module 0 (round_robin_rules) ruleNames meths [] coq_IncrMod
    return ()
