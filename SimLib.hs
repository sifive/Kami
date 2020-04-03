
module SimLib where

import Control.Monad
import System.Environment

import qualified Data.Map.Strict as M
import qualified Data.Vector.Mutable as MV

import Simulator
import Syntax
import Checkpoint
import RegisterFile as R

--state initialization

initialize :: Mod -> [(String,String)] -> IO KamiState
initialize = init_state

-- one-step simulation

simulate :: M.Map String (Signature, Coq_meth_sig) -> Coq_evaluated_Rule -> KamiState -> IO KamiState
simulate meths rule state = Simulator.sim_step undefined rule state meths


-- checkpointing

createCheckpoint :: KamiState -> FilePath -> IO ()
createCheckpoint (regs,state) out = do
    writeFile out "REGS\n\n"
    print_SimRegs regs out
    appendFile out "\n"
    appendFile out "INT_REGS\n\n"
    print_SimRegs (fmap (\(k,v) -> (SyntaxKind k,v)) $ int_regs state) out
    appendFile out "\n"
    appendFile out "REGFILES\n\n"
    let rfs = M.toList (files state)
    forM_ rfs $ \(name,file) -> do
        appendFile out (name ++ "\n")
        print_RegFile out file

readCheckpoint :: FilePath -> Mod -> IO KamiState
readCheckpoint path mod = do
    let (_,(rfbs,_)) = separateModRemove mod
    txt <- readFile path
    let tokss = parse_tokss txt
    let (regs, int_regs, rfs) = split_tokss tokss
    state <- initialize_files_zero rfbs 
    fs <- get_rfs rfs
    return (M.fromList $ map (\(s,(k,a)) -> (s, (SyntaxKind k, a))) (get_regpairs regs), restart_FileState fs (get_regpairs int_regs) state)

-- getters and putters

getRegVal :: KamiState -> String -> R.Any
getRegVal (regs,_) regName = case M.lookup regName regs of
  Just v -> snd v
  Nothing -> error ("Register " ++ regName ++ " not found.")

getRegFileVal :: KamiState -> String -> Int -> IO R.Any
getRegFileVal (_,(Build_FileState methods int_regs files)) fileName i = do
  case M.lookup fileName (R.unsafeCoerce files) of
    Nothing -> error ("File " ++ fileName ++ " not found.")
    Just (R.Build_RegFile _ _ _ _ _ _ _ v) -> MV.read v i

putRegVal :: KamiState -> String -> R.Any -> KamiState
putRegVal (regs,state) regName v = (M.insert regName (undefined, v) regs,state)

putRegFileVal :: KamiState -> String -> Int -> R.Any -> IO KamiState
putRegFileVal ks@(regs,(Build_FileState methods int_regs files)) fileName i v =
  case M.lookup fileName (R.unsafeCoerce files) of
    Nothing -> error ("File " ++ fileName ++ " not found.")
    Just (Build_RegFile _ _ _ _ _ _ _ a) -> do
      MV.write a i v
      return ks