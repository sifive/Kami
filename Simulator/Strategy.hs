
module Simulator.Strategy where

import qualified HaskellTarget as T

import Simulator.Util
import Simulator.Value

import System.Exit (exitSuccess)
import System.IO (isEOF)
import System.Random (randomRIO)

exitStr :: String -> Str (IO a)
exitStr msg = exit :+ (exitStr msg) where
    exit = do
        putStrLn msg
        exitSuccess

--generates rules randomly from the given list
rand_rules :: [T.RuleT] -> Str (IO T.RuleT)
rand_rules [] = exitStr "Empty rule list."
rand_rules rs = rule :+ rand_rules rs where

    rule = do
        i <- randomRIO (0,length rs - 1)
        return $ rs !! i

--generates rules in order from the given list, returning to the beginning upon reaching the end
round_robin_rules :: [T.RuleT] -> Str (IO T.RuleT)
round_robin_rules [] = exitStr "Empty rule list."
round_robin_rules (r:rs) = (return r) :+ (round_robin_rules (rs ++ [r]))

--prompts the user to supply rules at each step
user_rules :: [T.RuleT] -> Str (IO T.RuleT)
user_rules [] = exitStr "Empty rule list."
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
with_breaks :: Int -> ([T.RuleT] -> Str (IO T.RuleT)) -> [T.RuleT] -> Str (IO T.RuleT)
with_breaks n strategy rs = intersperse_with_period n (getLine >>) (strategy rs)
