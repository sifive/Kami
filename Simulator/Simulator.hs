{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MagicHash #-}

{-
  Haskell simulator for Kami modules.  Should be executed alongside extracted Haskell version of the Kami library.
-}

module Simulator.Simulator where

import Simulator.Environment
import Simulator.Evaluate
import Simulator.RegisterFile
import Simulator.Print
import Simulator.Util
import Simulator.Value

import qualified HaskellTarget as T

import qualified Data.HashMap as M

import Data.IORef
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

initialize :: Modes -> T.RegInitT -> IO (String,Val)
initialize _ (regName, (_, Just (T.NativeConst T.Nat c))) = return (regName, IntVal $ unsafeCoerce c)
initialize _ (regName, (_, Just (T.NativeConst (T.List lk) c))) = return (regName, ListVal $ unsafeCoerce c)
initialize _ (regName, (_, Just (T.NativeConst (T.Anything _) _))) = error "Cannot be simulated."
initialize _ (regName, (_, Just (T.SyntaxConst _ c))) = return (regName, eval c)
initialize modes (regName, (k, Nothing)) = do
    let debug = debug_mode modes
    v <- (if debug then (pure . defVal_FK) else randVal_FK) k
    return (regName,v)

simulate_action :: AbstractEnvironment a => Modes -> IORef a -> FileState -> [(String, a -> Val -> FileState -> M.Map String Val -> IO (a, Val))] -> T.ActionT Val -> M.Map String Val -> IO ([(String,Val)], [FileUpd] ,Val)
simulate_action modes envRef state meths act regs = sim act [] [] where

    sim (T.MCall methName _ arg cont) updates fupdates = case rf_methcall state methName (eval arg) of
        Just (Nothing,v) -> sim (cont v) updates fupdates
        Just (Just u,v) -> sim (cont v) updates (u:fupdates)
        Nothing -> case lookup methName meths of
            Nothing -> error ("Method " ++ methName ++ " not found.")
            Just f -> do
                currEnv <- readIORef envRef
                (nextEnv, v) <- f currEnv (eval arg) state regs
                writeIORef envRef nextEnv
                sim (cont v) updates fupdates

    sim (T.LetExpr _ e cont) updates fupdates = sim (cont $ unsafeCoerce $ (eval e :: Val)) updates fupdates

    sim (T.LetAction _ a cont) updates fupdates = do
        (updates', fupdates', v) <- sim a updates fupdates
        sim (cont v) updates' fupdates'

    --using a default val for now
    sim (T.ReadNondet k cont) updates fupdates = sim (cont $ unsafeCoerce $ defVal_FK k) updates fupdates

    sim (T.ReadReg regName _ cont) updates fupdates = case M.lookup regName regs of
        Nothing -> error ("Register " ++ regName ++ " not found.")
        Just v -> sim (cont $ unsafeCoerce v) updates fupdates

    sim (T.WriteReg regName _ e a) updates fupdates = case M.lookup regName regs of
        Nothing -> error ("Register " ++ regName ++ " not found.")
        Just _ -> sim a ((regName, eval e):updates) fupdates
        
    sim (T.IfElse e _ a1 a2 cont) updates fupdates = let a = if (boolCoerce $ eval e) then a1 else a2 in
        do
            (updates',fupdates',v) <- sim a updates fupdates
            sim (cont v) updates' fupdates'

    sim (T.Sys syss a) updates fupdates = do
        execIOs $ map (sysIO modes) syss
        sim a updates fupdates

    sim (T.Return e) updates fupdates = return (updates, fupdates, eval e)

simulate_module :: AbstractEnvironment a => Int -> ([T.RuleT] -> Str (IO T.RuleT)) -> IORef a -> [String] -> [(String, a -> Val -> FileState -> M.Map String Val -> IO (a, Val))] -> [T.RegFileBase] -> T.BaseModule -> IO (M.Map String Val)
simulate_module _ _ _ _ _ _ (T.BaseRegFile _) = error "BaseRegFile encountered."
simulate_module seed strategy envRef rulenames meths rfbs (T.BaseMod init_regs rules defmeths) = do
    modes <- get_modes
    setStdGen $ mkStdGen seed
    when (not $ null defmeths) $ putStrLn "Warning: Encountered internal methods."
    case get_rules rulenames rules of
        Left ruleName -> error ("Rule " ++ ruleName ++ " not found.")
        Right rules' -> do
            state <- initialize_files modes rfbs
            regs <- mapM (initialize modes) init_regs
            sim (strategy rules') (M.fromList regs) state  where
                sim (r :+ rs) regs filestate = do
                    (ruleName,a) <- r
                    currEnv <- readIORef envRef
                    preEnv <- envPre currEnv filestate regs ruleName
                    writeIORef envRef preEnv
                    (upd,fupd,_) <- simulate_action modes envRef filestate meths (unsafeCoerce $ a ()) regs
                    postEnv <- readIORef envRef
                    nextEnv <- envPost postEnv filestate regs ruleName
                    writeIORef envRef nextEnv
                    sim rs (updates regs upd) (exec_file_updates filestate fupd)

