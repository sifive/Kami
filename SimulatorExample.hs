
{-
	Example of how to simulate a module using IncrementerImpl extracted from Tutorial.v
-}

module Main where

import Target as T
import Simulator
import Extract

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
    simulate_module 0 rand_rules ruleNames meths coq_IncrMod
    return ()
