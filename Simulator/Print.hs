
module Simulator.Print where

import Simulator.Evaluate
import Simulator.Util
import Simulator.Value

import qualified Target as T

import qualified Data.Vector as V

import Data.List (intersperse)
import Numeric (showHex)
import System.Exit (exitSuccess)

printVal :: T.FullFormat -> Val -> String
printVal (T.FBool n bf) (BoolVal b) = space_pad n (if b then "1" else "0")
printVal (T.FBit n _ bf) (BitvectorVal bs) = space_pad n $ printNum bf bs
printVal (T.FStruct n _ names ffs) (StructVal fields) = "{" ++ (concat $ intersperse ";" $ 
    zipWith (\(name,val) ff -> name ++ ":" ++ (printVal ff val)) fields (map ffs (T.getFins n))
    ) ++ "}"
printVal ff (ArrayVal vals) = "[" ++ (concat $ intersperse ";" (zipWith (\i v -> show i ++ ": " ++ printVal ff v) [0..((length vals)-1)] (V.toList vals))) ++ "]"
printVal _ _ = "Cannot print expression, mismatch between FullFormat and Kami Type." --make an error?

printNum :: T.BitFormat -> [Bool] -> String
printNum T.Binary bs = "0b" ++ map (\b -> if b then '1' else '0') (reverse bs)
printNum T.Decimal bs = show $ int_of_list bs
printNum T.Hex bs = "0x" ++ showHex (int_of_list bs) ""

sysIO :: T.SysT Val -> IO ()
sysIO T.Finish = do
    putStrLn "Exiting..."
    exitSuccess
sysIO (T.DispString msg) = putStrLn msg
sysIO (T.DispExpr _ e ff) = putStrLn $ printVal ff $ eval e
