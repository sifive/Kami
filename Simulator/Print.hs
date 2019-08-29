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
import System.IO
import Control.Monad (when)

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
    show (T.FStruct n fk fs _) = "(Struct " ++ "{ " ++ (concat $ intersperse "; " $ 
        map (\i-> fs i ++ ":" ++ show (fk i)) (T.getFins n)) ++ "})"

printVal :: T.FullFormat -> Val -> String
printVal (T.FBool n bf) (BoolVal b) = space_pad n (if b then "1" else "0")
printVal (T.FBit n m bf) (BVVal bs) = space_pad m $ printNum bf bs
printVal (T.FStruct n _ names ffs) (StructVal fields) = "{ " ++ (concat $ 
    zipWith (\(name,val) ff -> name ++ ":" ++ (printVal ff val) ++ "; ") fields (map ffs (T.getFins n))
    ) ++ "}"
printVal (T.FArray n k ff) (ArrayVal vals) = "[ " ++ (concat (zipWith (\i v -> show i ++ "=" ++ printVal ff v ++ "; ") [0..((length vals)-1)] (V.toList vals))) ++ "]"
printVal ff v = error $ "Cannot print expression " ++ (show v) ++ " with FullFormat " ++ (show ff) ++ "."

printNum :: T.BitFormat -> BV.BitVector -> String
printNum T.Binary v = resize_num (BV.size v) $ tail $ tail $ BV.showBin v
printNum T.Decimal v = show (BV.nat v)
printNum T.Hex v = resize_num (BV.size v `cdiv` 4) $ tail $ tail $ BV.showHex v

sysIO :: T.SysT Val -> IO ()
sysIO T.Finish = do
    no_print <- no_print_mode
    interactive <- interactive_mode
    when (not no_print && not interactive) $ hPutStrLn stdout "Exiting..."
    exitSuccess
sysIO (T.DispString msg) = do
    no_print <- no_print_mode
    interactive <- interactive_mode
    when (not no_print && not interactive) $ hPutStr stdout $ format_string $ msg
sysIO (T.DispExpr _ e ff) = do
    no_print <- no_print_mode
    interactive <- interactive_mode
    when (not no_print && not interactive) $ hPutStr stdout $ printVal ff $ eval e

format_string :: String -> String
format_string [] = []
format_string ('\\':'n':rest) = '\n': format_string rest
format_string ('\\':'r':rest) = '\r': format_string rest
format_string ('\\':'t':rest) = '\t': format_string rest
format_string ('\\':_:rest) = error "backslash encountered."
format_string (c:rest) = c : format_string rest
