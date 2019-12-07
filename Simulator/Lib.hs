
{- useful functions for using the simulator -}

module Simulator.Lib where

import HaskellTarget as H

import Simulator.Print
import Simulator.Util
import Simulator.Value
import Simulator.RegisterFile

import qualified Data.Text as T
import qualified Data.BitVector as BV
import qualified Data.HashMap as M
import qualified Data.Array.MArray as MA

import Data.List (find)
import Data.Maybe (catMaybes)
import System.Environment (getArgs)
import System.Exit (exitSuccess)
import System.IO (isEOF)
import System.Random (randomRIO)

tt :: Val
tt = BVVal BV.nil

getArgVal :: String -> Int -> IO Val
getArgVal name n = do
    args <- getArgs

    let ps = catMaybes $ map (binary_split ':') args

    case find (\(x,y) -> x == name) ps of
        Just (_,y) -> return $ BVVal $ hex_to_bv n $ T.pack y
        Nothing -> error $ "Argument value " ++ name ++ " not supplied."


-- printVal :: T.FullFormat -> Val -> IO String
-- printVal (T.FBool n bf) (BoolVal b) = return $ space_pad n (if b then "1" else "0")
-- printVal (T.FBit n m bf) (BVVal bs) = return $ space_pad m $ printNum bf bs
-- printVal (T.FStruct n _ names ffs) (StructVal fields) = do
--     ps <- pair_sequence $ zipWith (\(name,val) ff -> (name, printVal ff val)) fields (map ffs $ T.getFins n)
--     return ("{ " ++ concatMap (\(name,pval) -> name ++ ":" ++ pval ++ "; ") ps ++ "}")
-- printVal (T.FArray n k ff) (ArrayVal vals) = do
--     ps <- pair_sequence $ map (\i -> (i, M.readArray vals i)) [0..(n-1)]
--     qs <- pair_sequence $ map (\(i,v) -> (i, printVal ff v)) ps
--     return ("[" ++ concatMap (\(i,pval) -> show i ++ "=" ++ pval ++ "; ") qs ++ "]")
-- printVal ff v = error $ "Cannot print expression with FullFormat " ++ (show ff) ++ "."


ppr_bitformat :: H.BitFormat -> Val -> IO String
ppr_bitformat bf (BoolVal b) = return $ if b then "1" else "0"
ppr_bitformat bf (BVVal v) = return $ printNum bf v
ppr_bitformat bf (StructVal fields) = do
    ps <- pair_sequence $ map (\(name,val) -> (name, ppr_bitformat bf val)) fields
    return ("{" ++ (concatMap (\(name,pval) -> name ++ ":" ++ pval ++ "; ") ps) ++ "}")
ppr_bitformat bf (ArrayVal vals) = do
    len <- arr_length vals
    ps <- pair_sequence $ map (\i -> (i, MA.readArray vals i)) [0..(len-1)]
    qs <- pair_sequence $ map (\(i,v) -> (i, ppr_bitformat bf v)) ps
    return ("[" ++ concatMap (\(i,pval) -> show i ++ "=" ++ pval ++ "; ") qs ++ "]") 

ppr_bin :: Val -> IO String
ppr_bin = ppr_bitformat H.Binary

ppr_hex :: Val -> IO String
ppr_hex = ppr_bitformat H.Hex

ppr_dec :: Val -> IO String
ppr_dec = ppr_bitformat H.Decimal

getRuleNames :: H.BaseModule -> [String]
getRuleNames mod = map fst $ H.getRules mod

print_reg :: M.Map String Val -> String -> IO()
print_reg regs regname =
    case M.lookup regname regs of
        Just v -> do 
            pval <- ppr_hex v
            putStrLn pval
        Nothing -> putStrLn $ "Register " ++ regname ++ " not found."

print_file_reg :: FileState -> String -> Int -> IO()
print_file_reg state filename addr =
    case M.lookup filename (arrs state) of
        Just arr -> do
            v <- MA.readArray arr addr
            pval <- ppr_hex v
            putStrLn pval
        Nothing -> putStrLn $ "File " ++ filename ++ " not found."

--generates rules randomly from the given list
rand_rules :: [H.RuleT] -> Str (IO H.RuleT)
rand_rules [] = error "Empty rule list."
rand_rules rs = rule :+ rand_rules rs where

    rule = do
        i <- randomRIO (0,length rs - 1)
        return $ rs !! i

--generates rules in order from the given list, returning to the beginning upon reaching the end
round_robin_rules :: [H.RuleT] -> Str (IO H.RuleT)
round_robin_rules [] = error "Empty rule list."
round_robin_rules rs = unwind_list $ map return rs

--prompts the user to supply rules at each step
user_rules :: [H.RuleT] -> Str (IO H.RuleT)
user_rules [] = error "Empty rule list."
user_rules rs = rule :+ user_rules rs where

    rule = do
        putStrLn "Next rule:\n"
        b <- isEOF
        if not b then do
            ruleName <- getLine
            case lookup ruleName rs of
                Nothing -> do
                    putStrLn ("Rule " ++ ruleName ++ " not found.")
                    rule
                Just a -> return (ruleName,a)
        else exitSuccess

--modifies the given strategy to add a getLine after n steps
with_breaks :: Int -> ([H.RuleT] -> Str (IO H.RuleT)) -> [H.RuleT] -> Str (IO H.RuleT)
with_breaks n strategy rs = intersperse_with_period n (getLine >>) (strategy rs)
