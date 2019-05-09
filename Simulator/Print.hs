{-# OPTIONS_GHC -XStandaloneDeriving #-}

module Simulator.Print where

import Simulator.Evaluate
import Simulator.Util
import Simulator.Value

import qualified HaskellTarget as T

import qualified Data.BitVector as BV
import qualified Data.Vector as V

import Data.List (intersperse)
import Numeric (showHex)
import System.Exit (exitSuccess)

instance Show T.Kind where
    show T.Bool = "Bool"
    show (T.Bit n) = "(Bit " ++ show n ++ ")"
    show (T.Array n k) = "(Array " ++ show n ++ " " ++ show k ++ ")"
    show (T.Struct n fk fs) = "(Struct " ++ "{" ++ (concat $ intersperse "; " $ 
        map (\i-> fs i ++ ":" ++ show (fk i)) (T.getFins n)) ++ "})"

deriving instance Show T.BitFormat

instance Show T.FullFormat where
    show (T.FBool _ _) = "Bool"
    show (T.FBit n _ _) = "(Bit " ++ show n ++ ")"
    show (T.FArray n k _) = "(Array " ++ show n ++ " " ++ show k ++ ")"
    show (T.FStruct n fk fs _) = "(Struct " ++ "{" ++ (concat $ intersperse "; " $ 
        map (\i-> fs i ++ ":" ++ show (fk i)) (T.getFins n)) ++ "})"

printVal :: T.FullFormat -> Val -> String
printVal (T.FBool n bf) (BoolVal b) = space_pad n (if b then "1" else "0")
printVal (T.FBit n m bf) (BitvectorVal bs) = space_pad m $ printNum bf bs
printVal (T.FStruct n _ names ffs) (StructVal fields) = "{" ++ (concat $ intersperse "; " $ 
    zipWith (\(name,val) ff -> name ++ ":" ++ (printVal ff val)) fields (map ffs (T.getFins n))
    ) ++ "}"
printVal (T.FArray n k ff) (ArrayVal vals) = "[" ++ (concat $ intersperse "; " (zipWith (\i v -> show i ++ ":" ++ printVal ff v) [0..((length vals)-1)] (V.toList vals))) ++ "]"
printVal ff v = error $ "Cannot print expression " ++ (show v) ++ " with FullFormat " ++ (show ff) ++ "."

printNum :: T.BitFormat -> BV.BitVector -> String
printNum T.Binary = BV.showBin
printNum T.Decimal = \v -> show ((fromIntegral v) :: Integer)
printNum T.Hex = BV.showHex

sysIO :: T.SysT Val -> IO ()
sysIO T.Finish = do
    putStrLn "Exiting..."
    exitSuccess
sysIO (T.DispString msg) = putStr $ format_string msg
sysIO (T.DispExpr _ e ff) = putStr $ printVal ff $ eval e

format_string :: String -> String
format_string [] = []
format_string ('\\':'n':rest) = '\n': format_string rest
format_string ('\\':'r':rest) = '\r': format_string rest
format_string ('\\':'t':rest) = '\t': format_string rest
format_string ('\\':_:rest) = error "backlash encountered."
format_string (c:rest) = c : format_string rest
