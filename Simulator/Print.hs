{-# OPTIONS_GHC -XStandaloneDeriving #-}
{-# LANGUAGE Strict #-}

module Simulator.Print where

import Simulator.Evaluate
import Simulator.Util
import Simulator.Value

import qualified HaskellTarget as T

import qualified Data.BitVector as BV
import qualified Data.Array.MArray as M

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

printNum :: T.BitFormat -> BV.BitVector -> String
printNum T.Binary v = resize_num (BV.size v) $ tail $ tail $ BV.showBin v
printNum T.Decimal v = show (BV.nat v)
printNum T.Hex v = resize_num (BV.size v `cdiv` 4) $ tail $ tail $ BV.showHex v

printVal :: T.FullFormat -> Val -> IO String
printVal (T.FBool n bf) (BoolVal b) = return $ space_pad n (if b then "1" else "0")
printVal (T.FBit n m bf) (BVVal bs) = return $ space_pad m $ printNum bf bs
printVal (T.FStruct n _ names ffs) (StructVal fields) = do
    ps <- pair_sequence $ zipWith (\(name,val) ff -> (name, printVal ff val)) fields (map ffs $ T.getFins n)
    return ("{ " ++ concatMap (\(name,pval) -> name ++ ":" ++ pval ++ "; ") ps ++ "}")
printVal (T.FArray n k ff) (ArrayVal vals) = do
    ps <- pair_sequence $ map (\i -> (i, M.readArray vals i)) [0..(n-1)]
    qs <- pair_sequence $ map (\(i,v) -> (i, printVal ff v)) ps
    return ("[" ++ concatMap (\(i,pval) -> show i ++ "=" ++ pval ++ "; ") qs ++ "]")
printVal ff v = error $ "Cannot print expression with FullFormat " ++ (show ff) ++ "."

sysIO :: Modes -> T.SysT Val -> IO ()
sysIO modes T.Finish = do
    let no_print = no_print_mode modes
    let interactive = interactive_mode modes
    when (not no_print && not interactive) $ hPutStrLn stdout "Exiting..."
    exitSuccess
sysIO modes (T.DispString msg) = do
    let no_print = no_print_mode modes
    let interactive = interactive_mode modes
    when (not no_print && not interactive) $ hPutStr stdout $ format_string $ msg
sysIO modes (T.DispExpr _ e ff) = do
    let no_print = no_print_mode modes
    let interactive = interactive_mode modes
    v <- eval e
    pval <- printVal ff v
    when (not no_print && not interactive) $ hPutStr stdout $ pval

format_string :: String -> String
format_string [] = []
format_string ('\\':'n':rest) = '\n': format_string rest
format_string ('\\':'r':rest) = '\r': format_string rest
format_string ('\\':'t':rest) = '\t': format_string rest
format_string ('\\':_:rest) = error "backslash encountered."
format_string (c:rest) = c : format_string rest
