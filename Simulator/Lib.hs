
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
import qualified Data.Vector as V

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

ppr_bitformat :: H.BitFormat -> Val -> String
ppr_bitformat bf (BoolVal b) = if b then "1" else "0"
ppr_bitformat bf (BVVal v) = printNum bf v
ppr_bitformat bf (StructVal fields) = "{ " ++ (concat $ 
    map (\(name,val) -> name ++ ":" ++ (ppr_bitformat bf val) ++ "; ") fields
    ) ++ "}"
ppr_bitformat bf (ArrayVal vals) = "[ " ++ (concat (zipWith (\i v -> show i ++ "=" ++ ppr_bitformat bf v ++ "; ") [0..((length vals)-1)] (V.toList vals))) ++ "]"

ppr_bin :: Val -> String
ppr_bin = ppr_bitformat H.Binary

ppr_hex :: Val -> String
ppr_hex = ppr_bitformat H.Hex

ppr_dec :: Val -> String
ppr_dec = ppr_bitformat H.Decimal

getRuleNames :: H.BaseModule -> [String]
getRuleNames mod = map fst $ H.getRules mod

print_reg :: M.Map String Val -> String -> IO()
print_reg regs regname =
    case M.lookup regname regs of
        Just v -> putStrLn $ ppr_hex v
        Nothing -> putStrLn $ "Register " ++ regname ++ " not found."

print_file_reg :: FileState -> String -> Int -> IO()
print_file_reg state filename addr =
    case M.lookup filename (arrs state) of
        Just arr -> case arr V.!? addr of
                Just v -> putStrLn $ ppr_hex v
                Nothing -> putStrLn "Index out of bounds."
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
