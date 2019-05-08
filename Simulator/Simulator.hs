{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MagicHash #-}

{-
  Haskell simulator for Kami modules.  Should be executed alongside extracted Haskell version of the Kami library.
-}

module Simulator.Simulator where

import Simulator.Evaluate
import Simulator.RegisterFile
import Simulator.Print
import Simulator.Util
import Simulator.Value

import qualified HaskellTarget as T

import qualified Data.Map as M

import Data.Maybe (isJust)
import Control.Monad (mapM, when)
import System.Random (mkStdGen, setStdGen)

get_rules :: [String] -> [T.RuleT] -> Either String [T.RuleT]
get_rules [] _ = Right []
get_rules (x:xs) rules = case lookup x rules of
    Nothing -> Left x
    Just a -> do
        rest <- get_rules xs rules
        return ((x,a):rest)

initialize :: T.RegInitT -> IO (String,Val)
initialize (_, (_, Just (T.NativeConst _))) = error "Encountered a NativeConst."
initialize (regName, (_, Just (T.SyntaxConst _ c))) = return (regName, eval c)
initialize (regName, (k, Nothing)) = do
    v <- randVal_FK k
    return (regName,v)

check_assertions :: T.ActionT Val -> M.Map String Val -> Bool
check_assertions act regs = isJust $ tryEval act where

    tryEval :: T.ActionT Val -> Maybe Val
    tryEval (T.MCall _ (_,k) _ cont) = tryEval (cont $ defVal k)
    tryEval (T.LetExpr _ e cont) = tryEval (cont $ unsafeCoerce $ (eval e :: Val))
    tryEval (T.LetAction _ a cont) = do
        v <- tryEval a
        tryEval (cont v)
    tryEval (T.ReadNondet k cont) = tryEval $ cont $ unsafeCoerce $ defVal_FK k
    tryEval (T.ReadReg regName _ cont) = case M.lookup regName regs of
        Nothing -> error ("Register " ++ regName ++ " not found.")
        Just v -> tryEval $ cont $ unsafeCoerce v
    tryEval (T.WriteReg regName _ e a) = tryEval a
    tryEval (T.IfElse e _ a1 a2 cont) = let a = if (boolCoerce $ eval e) then a1 else a2 in
        do
            v <- tryEval a
            tryEval (cont v)
    tryEval (T.Assertion e a) = if (boolCoerce $ eval e) then tryEval a else Nothing
    tryEval (T.Sys _ a) = tryEval a
    tryEval (T.Return e) = Just $ eval e

simulate_action :: FileState -> [(String, Val -> IO Val)] -> T.ActionT Val -> M.Map String Val -> IO ([(String,Val)], [FileUpd] ,Val)
simulate_action state meths act regs = sim act where

    sim (T.MCall methName _ arg cont) = case rf_methcall state methName (eval arg) of
        Just (Nothing,v) -> sim $ cont v
        Just (Just u,v) -> do
            (upd,fupd, v') <- sim $ cont v
            return (upd, u:fupd, v')
        Nothing -> case lookup methName meths of
            Nothing -> error ("Method " ++ methName ++ " not found.")
            Just f -> do
                v <- f $ eval arg
                sim $ cont v

    sim (T.LetExpr _ e cont) = sim (cont $ unsafeCoerce $ (eval e :: Val))

    sim (T.LetAction _ a cont) = do
        (upd, fupd, v) <- sim a
        (upd', fupd', v') <- sim $ cont v
        return (upd ++ upd', fupd ++ fupd', v')

    --using a default val for now
    sim (T.ReadNondet k cont) = sim $ cont $ unsafeCoerce $ defVal_FK k

    sim (T.ReadReg regName _ cont) = case M.lookup regName regs of
        Nothing -> error ("Register " ++ regName ++ " not found.")
        Just v -> sim $ cont $ unsafeCoerce v 

    sim (T.WriteReg regName _ e a) = case M.lookup regName regs of
        Nothing -> error ("Register " ++ regName ++ " not found.")
        Just _ -> do
            (upd,fupd,v) <- sim a
            return ((regName,eval e):upd,fupd,v)

    sim (T.IfElse e _ a1 a2 cont) = let a = if (boolCoerce $ eval e) then a1 else a2 in
        do
            (upd,fupd,v) <- sim a
            (upd',fupd',v') <- sim $ cont v
            return (upd ++ upd', fupd ++ fupd', v')

    sim (T.Assertion e a) = if (boolCoerce $ eval e) then sim a else error "Assertion depends upon method return values."

    sim (T.Sys syss a) = do
        execIOs $ map sysIO syss
        sim a

    sim (T.Return e) = return ([],[], eval e)

simulate_module :: Int -> ([T.RuleT] -> Str (IO T.RuleT)) -> [String] -> [(String, Val -> IO Val)] -> [T.RegFileBase] -> T.BaseModule -> IO (M.Map String Val)
simulate_module _ _ _ _ _ (T.BaseRegFile _) = error "BaseRegFile encountered."
simulate_module seed strategy rulenames meths rfbs (T.BaseMod init_regs rules defmeths) = 

    -- passes the seed to the global rng
    (setStdGen $ mkStdGen seed) >>

    (when (not $ null defmeths) $ putStrLn "Warning: Encountered internal methods.") >>
 
    case get_rules rulenames rules of
        Left ruleName -> error ("Rule " ++ ruleName ++ " not found.")
        Right rules' -> do
            state <- initialize_files rfbs
            regs <- mapM initialize init_regs
            sim (strategy rules') (M.fromList regs) state  where
                sim (r :+ rs) regs filestate = do
                    (ruleName,a) <- r
                    let b = check_assertions (unsafeCoerce $ a ()) regs
                    if b then do
                        (upd,fupd,_) <- simulate_action filestate meths (unsafeCoerce $ a ()) regs
                        sim rs (updates regs upd) (exec_file_updates filestate fupd)

                        else do
                            putStrLn $ "Guard for " ++ ruleName ++ " failed."
                            sim rs regs filestate

