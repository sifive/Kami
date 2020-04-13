{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

{-
  Haskell simulator for Kami modules.  Should be executed alongside extracted Haskell version of the Kami library.
-}

module Simulator.Simulator where

import Simulator.Classes
import Simulator.Environment
import Simulator.Evaluate
import Simulator.RegisterFile
import Simulator.Print
import Simulator.Util
import Simulator.Value
import qualified Data.Set as S

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

initialize :: Vec v => Modes -> T.RegInitT -> IO (String,Val v)
initialize _ (regName, (_, Just (T.NativeConst c))) = return (regName, unsafeCoerce c)
initialize _ (regName, (_, Just (T.SyntaxConst _ c))) = do
    return (regName, eval_ConstT c)
initialize modes (regName, (k, Nothing)) = do
    let debug = debug_mode modes
    v <- (if debug then (pure . defVal_FK) else randVal_FK) k
    return (regName,v)

simulate_action :: forall m a v e. (StringMap m, Array a, Vec v, AbstractEnvironment e) => [T.DefMethT] -> [String] -> Modes -> IORef e -> FileState m a v -> [(String, e -> Val v -> FileState m a v -> m (Val v) -> IO (e, Val v))] -> T.ActionT (Val v) -> m (Val v) -> IO ([String], [(String,Val v)], [FileUpd v] ,Val v)
simulate_action defmeths methcalls modes envRef state meths act regs = sim methcalls act [] [] where

    sim mcs (T.MCall methName _ arg cont) updates fupdates = if methName `elem` mcs then error ("Method " ++ methName  ++ " called twice in same cycle.") else do
        let arg' = eval_Expr arg
        case rf_methcall state methName arg' of
            Just (Nothing,v) -> do 
                v' <- v
                sim (methName:mcs) (cont v') updates fupdates
            Just (Just u,v) -> do
                v' <- v
                u' <- u
                sim (methName:mcs) (cont v') updates (u':fupdates)
            Nothing -> case lookup methName defmeths of
                Just (_,f) -> sim (methName:mcs) (cont $ unsafeCoerce $ f () $ unsafeCoerce arg') updates fupdates
                Nothing -> case lookup methName meths of
                                Nothing -> error ("Method " ++ methName ++ " not found.")
                                Just f -> do
                                    currEnv <- readIORef envRef
                                    (nextEnv, v) <- f currEnv arg' state regs
                                    writeIORef envRef nextEnv
                                    sim (methName:mcs) (cont v) updates fupdates

    sim mcs (T.LetExpr _ e cont) updates fupdates = do
        let v = eval_Expr e
        sim mcs (cont $ unsafeCoerce $ (v :: Val v)) updates fupdates

    sim mcs (T.LetAction _ a cont) updates fupdates = do
        (mcs', updates', fupdates', v) <- sim mcs a updates fupdates
        sim mcs' (cont v) updates' fupdates'

    --using a default val for now
    sim mcs (T.ReadNondet k cont) updates fupdates = sim mcs (cont $ unsafeCoerce $ defVal_FK @v k) updates fupdates

    sim mcs (T.ReadReg regName _ cont) updates fupdates = case map_lookup regName regs of
        Nothing -> error ("Register " ++ regName ++ " not found.")
        Just v -> sim mcs (cont $ unsafeCoerce v) updates fupdates

    sim mcs (T.WriteReg regName _ e a) updates fupdates = case map_lookup regName regs of
        Nothing -> error ("Register " ++ regName ++ " not found.")
        Just _ -> do
            let v = eval_Expr e
            sim mcs a ((regName, v):updates) fupdates

    sim mcs (T.IfElse e _ a1 a2 cont) updates fupdates = do
        let b = eval_Expr @v e
        let a = if boolCoerce b then a1 else a2
        (mcs',updates',fupdates',v) <- sim mcs a updates fupdates
        sim mcs' (cont v) updates' fupdates'

    sim mcs (T.Sys syss a) updates fupdates = do
        execIOs $ map (sysIO modes) syss
        sim mcs a updates fupdates

    sim mcs (T.Return e) updates fupdates = do
        let v = eval_Expr e
        return (mcs, updates, fupdates, v)

simulate_module :: forall m a v e. (StringMap m, Array a, Vec v, AbstractEnvironment e) => Int -> ([T.RuleT] -> Str (IO T.RuleT)) -> IORef e -> [String] -> [(String, e -> Val v -> FileState m a v -> m (Val v) -> IO (e, Val v))] -> [T.RegFileBase] -> [String] -> T.BaseModule -> IO ()
simulate_module _ _ _ _ _ _ _ (T.BaseRegFile _) = error "BaseRegFile encountered."
simulate_module seed strategy envRef rulenames meths rfbs hiddenMeths (T.BaseMod init_regs rules defmeths) = do
    modes <- get_modes
    setStdGen $ mkStdGen seed
    when (not (S.fromList (map fst defmeths) `S.isSubsetOf` (S.fromList hiddenMeths))) $ error "Default methods are not a subset of the Hidden methods."
    case get_rules rulenames rules of
        Left ruleName -> error ("Rule " ++ ruleName ++ " not found.")
        Right rules' -> do
            state <- initialize_files modes rfbs
            regs <- mapM (initialize modes) init_regs
            sim [] (strategy rules') (map_of_list regs) state  where

                sim mcs (EndOfCycle rs) regs filestate = sim [] rs regs filestate
                sim mcs (r :+ rs) regs filestate = do
                    (ruleName,a) <- r
                    currEnv <- readIORef envRef
                    preEnv <- envPre currEnv filestate regs ruleName
                    writeIORef envRef preEnv
                    (mcs',upd,fupd,_) <- simulate_action defmeths mcs modes envRef filestate meths (unsafeCoerce $ a ()) regs
                    postEnv <- readIORef envRef
                    nextEnv <- envPost postEnv filestate regs ruleName
                    writeIORef envRef nextEnv
                    s <- exec_file_updates filestate fupd
                    sim mcs' rs (updates regs upd) s
