
{- useful functions for using the simulator -}

module Simulator.Lib where

import HaskellTarget as H

import Simulator.Print
import Simulator.Util
import Simulator.Value

import qualified Data.Text as T
import qualified Data.BitVector as BV

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

ppr_bin :: Kind -> Val -> String
ppr_bin k = printVal $ H.fullFormatBinary k

ppr_hex :: Kind -> Val -> String
ppr_hex k = printVal $ H.fullFormatHex k

ppr_dec :: Kind -> Val -> String
ppr_dec k = printVal $ H.fullFormatDecimal k

getRuleNames :: H.BaseModule -> [String]
getRuleNames mod = map fst $ H.getRules mod

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
