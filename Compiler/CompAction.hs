{-# OPTIONS_GHC -XStandaloneDeriving #-}
{-# OPTIONS_GHC -XFlexibleInstances #-}
{-# LANGUAGE Strict #-}

import qualified Target as T
import Data.List
import Data.Char
import Control.Monad.State.Lazy
import qualified Data.Map.Lazy as H
import Debug.Trace
import Numeric
import PrettyPrintVerilog
import CustomExtract
import System.IO
import Data.Time.Clock
import Data.Maybe

{- Show instances for debugging -}

deriving instance Show T.UniBoolOp
deriving instance Show T.CABoolOp
deriving instance Show T.UniBitOp
deriving instance Show T.CABitOp
deriving instance Show T.BinBitOp
deriving instance Show T.BitFormat
deriving instance Show T.RegFileReaders
deriving instance Show T.RegFileBase

show_finfun :: Show a => Int -> (CustomExtract.EFin -> a) -> String
show_finfun n f = "{ " ++ intercalate " ; " (map (show . f) $ T.getFins n) ++ " }"

instance Show T.FullFormat where
  show (T.FBool n bf) = "FBool " ++ show n ++ " " ++ show bf
  show (T.FBit n m bf) = "FBit " ++ show n ++ " " ++ show m ++ " " ++ show bf
  show (T.FStruct n fk fs ffs) = "FStruct " ++ show n ++ " " ++ show_finfun n fk ++ " " ++ show_finfun n fs ++ " " ++ show_finfun n ffs
  show (T.FArray n k ff) = "FArray " ++ show n ++ " " ++ show k ++ " " ++ show ff
 
instance Show T.ConstT where
  show (T.ConstBool b) = "ConstBool " ++ show b
  show (T.ConstBit n w) = "ConstBit " ++ show n ++ " " ++ show w
  show (T.ConstStruct n fk fs fc) = "ConstStruct " ++ show n ++ " " ++ show_finfun n fk ++ " " ++ show_finfun n fs ++ " " ++ show_finfun n fc
  show (T.ConstArray n k fc) = "ConstArray " ++ show n ++ " " ++ show k ++ " " ++ show_finfun n fc

instance Show T.ConstFullT where
  show (T.SyntaxConst k c) = "SyntaxConst " ++ show k ++ " " ++ show c
  show (T.NativeConst _) = "NativeConst"

instance Show T.Kind where
  show T.Bool = "Bool"
  show (T.Bit n) = "Bit " ++ show n
  show (T.Struct n fk fs) = "Struct " ++ show n ++ " " ++ show_finfun n fk ++ " " ++ show_finfun n fs
  show (T.Array n k) = "Array " ++ show n ++ " " ++ show k

instance Show T.FullKind where
  show (T.SyntaxKind k) = "SyntaxKind " ++ show k
  show (T.NativeKind _) = "FullKind"

instance Show (T.Expr ty) where
  show (T.Var fk t) = "Var " ++ show fk ++ " " ++ show (T.unsafeCoerce t :: T.VarType)
  show (T.Const k c) = "Const " ++ show k ++ show c
  show (T.UniBool o e) = "UniBool " ++ show o ++ " " ++ show e
  show (T.CABool o es) = "CABool " ++ show o ++ " " ++ show es
  show (T.UniBit n m o e) = "UniBit " ++ show n ++ " " ++ show m ++ " " ++ show o ++ show e
  show (T.CABit n o es) = "CABit " ++ show n ++ " " ++ show o ++ " " ++ show es
  show (T.BinBit n m p o e1 e2) = "BinBit " ++ show n ++ " " ++ show m ++ " " ++ show p ++ " " ++ show o ++ " " ++ show e1 ++ " " ++ show e2
  show (T.BinBitBool n m o e1 e2) = "BinBitBool " ++ show n ++ " " ++ show m ++ " " ++ show o ++ " " ++ show e1 ++ " " ++ show e2
  show (T.ITE fk e1 e2 e3) = "ITE " ++ show fk ++ " " ++ show e1 ++ " " ++ show e2 ++ " " ++ show e3
  show (T.Eq k e1 e2) = "Eq " ++ show k ++ " " ++ show e1 ++ " " ++ show e2
  show (T.ReadStruct n fk fs e i) = "ReadStruct " ++ show n ++ " " ++ show_finfun n fk ++ " " ++ show_finfun n fs ++ " " ++ show e ++ " " ++ show i
  show (T.BuildStruct n fk fs fe) = "BuildStruct " ++ show n ++ " " ++ show_finfun n fk ++ " " ++ show_finfun n fs ++ " " ++ show_finfun n fe
  show (T.ReadArray n m k e1 e2) = "ReadArray " ++ show n ++ " " ++ show m ++ " " ++ show e1 ++ " " ++ show e2
  show (T.ReadArrayConst n k e i) = "ReadArrayConst " ++ show n ++ " " ++ show k ++ " " ++ show e ++ " " ++ show i
  show (T.BuildArray n k f) = "BuildArray " ++ show n ++ " " ++ show k ++ " " ++ show_finfun n f

deriving instance Show T.SyncRead

deriving instance Show (T.SysT ty)
deriving instance Show T.RtlModule

instance Show T.RegFileInitT where
  show _ = "RegFileInitT"

instance Eq T.ConstT where
  (==) (T.ConstBool x) (T.ConstBool y) = x == y
  (==) (T.ConstBit n x) (T.ConstBit m y) = and [n == m, x == y]
  (==) (T.ConstArray n k xs) (T.ConstArray m k' ys) = and ((n == m) : [x == y | x <- map xs $ T.getFins n, y <- map ys $ T.getFins n])
  (==) (T.ConstStruct n fk fs xs) (T.ConstStruct m fk' fs' ys) = and ((n == m) : [x == y | x <- map xs $ T.getFins n, y <- map ys $ T.getFins n])
  (==) _ _ = False

--access with helpful error msg
(!!!) :: (Ord k, Show k, Show v) => H.Map k v -> k -> v
(!!!) m k = case m H.!? k of
  Just v -> v
  Nothing -> error ("Key " ++ show k ++ " not found in map " ++ show m ++ ".") 

get_rfr_meths :: T.RegFileReaders -> [String]
get_rfr_meths (T.Async reads) = reads
get_rfr_meths (T.Sync _ reads) = concatMap (\(T.Build_SyncRead r1 r2 r3) -> [r1,r2,r3]) reads

get_rf_meths :: T.RegFileBase -> [String]
get_rf_meths (T.Build_RegFileBase _ _ _ readers write _ _ _) = write : get_rfr_meths readers

get_normal_meth_calls_with_sign :: T.BaseModule -> [T.RegFileBase] -> [(String,(T.Kind,T.Kind))]
get_normal_meth_calls_with_sign m rfbs =
  let rf_meths = concatMap get_rf_meths rfbs in
    filter (\(f,_) -> not $ f `elem` rf_meths) $ nubBy (\(x, _) (y, _) -> x == y) (T.getCallsWithSignPerMod (T.Base m))

get_write_meths_with_arg :: [T.RegFileBase] -> [(String,T.Kind)]
get_write_meths_with_arg rfbs = map (\(T.Build_RegFileBase isWrMask num _ _ write idxNum k _) -> 
    if isWrMask then (write, T.coq_WriteRqMask (log2_up idxNum) num k) else (write, T.coq_WriteRq (log2_up idxNum) (T.Array num k))
  ) rfbs

get_async_reads_with_arg :: [Async] -> [(String, T.Kind)]
get_async_reads_with_arg asyncs = do
  (Async common reads) <- asyncs
  read <- reads
  let idxNum = commonIdxNum common
  return (read, T.Bit $ log2_up idxNum)

get_sync_readReqs_with_arg :: [Sync] -> [(String, T.Kind)]
get_sync_readReqs_with_arg sync = do
  (Sync common reads) <- sync
  (T.Build_SyncRead readRq _ _) <- reads
  let idxNum = commonIdxNum common
  return (readRq, T.Bit $ log2_up idxNum)

get_sync_readResps_with_arg :: [Sync] -> [(String, T.Kind)]
get_sync_readResps_with_arg sync = do
  (Sync _ reads) <- sync
  (T.Build_SyncRead _ readRs _) <- reads
  return (readRs, T.Bit 0)

type RME = T.RmeSimple T.Coq_rtl_ty RegMapTy
--deriving instance Show (T.RmeSimple T.Coq_rtl_ty RegMapTy)

type PreModInput = ([String], ([T.RegFileBase], T.BaseModule))
type ModInput = (PreModInput, T.CompActionSimple T.Coq_rtl_ty RegMapTy)

regs_of_basemod :: T.BaseModule -> [Register]
regs_of_basemod basemod = map (\(reg,(k,_)) -> Register reg k) (T.getRegisters basemod)

process_rfbs :: [T.RegFileBase] -> ([Async], {-isAddrs-} [Sync], {-notIsAddrs-} [Sync])
process_rfbs rfbs = go [] [] [] rfbs where
  go asyncs isAddrs notIsAddrs [] = (asyncs, isAddrs, notIsAddrs)
  go asyncs isAddrs notIsAddrs ((T.Build_RegFileBase isMask num dataArray readers write idxNum k init):rest) = 
    let common = CommonInfo isMask num dataArray write idxNum k init in case readers of
      T.Async reads -> go ((Async common reads):asyncs) isAddrs notIsAddrs rest
      T.Sync True reads -> go asyncs ((Sync common reads):isAddrs) notIsAddrs rest
      T.Sync False reads -> go asyncs isAddrs ((Sync common reads):notIsAddrs) rest

all_isAddr_shadows :: [Sync] -> [Register]
all_isAddr_shadows isAddrs = concatMap (\(Sync common names) -> map (\(T.Build_SyncRead _ _ name) -> Register name $ T.SyntaxKind $ T.Bit $ log2_up (commonIdxNum common)) names) isAddrs

all_not_isAddr_shadows :: [Sync] -> [Register]
all_not_isAddr_shadows notIsAddrs = concatMap (\(Sync common names) -> map (\(T.Build_SyncRead _ _ name) -> Register name $ T.SyntaxKind $ T.Array (commonNum common) $ T.coq_Maybe (commonData common)) names) notIsAddrs

all_regs_of_modinput :: ModInput -> [Register]
all_regs_of_modinput ((_,(rfbs,basemod)),cas) = let (asyncs,isAddrs,notIsAddrs) = process_rfbs rfbs in
     regs_of_basemod basemod
  ++ all_isAddr_shadows isAddrs
  ++ all_not_isAddr_shadows notIsAddrs
  
en_arg_initialize :: String -> T.Kind -> [(T.VarType, T.RtlExpr')]
en_arg_initialize f k = [((f ++ "#_enable",Just 0), T.Const T.Bool $ T.ConstBool False),
                   ((f ++ "#_argument",Just 0), T.Const k $ T.getDefaultConst k)]

get_calls_from_basemod :: T.BaseModule -> [T.RegFileBase] -> [String]
get_calls_from_basemod basemod rfbs = map fst (get_normal_meth_calls_with_sign basemod rfbs)

all_initialize :: ModInput -> [(T.VarType, T.RtlExpr')]
all_initialize modinput@((_,(rfbs,basemod)),_) =
  let regs = all_regs_of_modinput modinput in
  let (asyncs,isAddrs,notIsAddrs) = process_rfbs rfbs in

    --regular regs/shadow regs
     map (\(Register reg k) -> ((reg, Just 0), T.Var k $ T.unsafeCoerce (reg,Nothing))) regs

    --all rf meths
  ++ concatMap (\(f,argk) -> en_arg_initialize f argk) (get_write_meths_with_arg rfbs ++ get_async_reads_with_arg asyncs ++ get_sync_readReqs_with_arg (isAddrs ++ notIsAddrs))

    --normal methods
  ++ concatMap (\(f,(argk,_)) -> en_arg_initialize f argk) (get_normal_meth_calls_with_sign basemod rfbs)

data CommonInfo =
  CommonInfo
  { commonIsWrMask :: Bool
  , commonNum :: Int
  , commonDataArray :: String
  , commonWrite :: String
  , commonIdxNum :: Int
  , commonData :: T.Kind
  , commonInit :: T.RegFileInitT } deriving (Show)
  
data Async =
  Async
  { asyncCommon :: CommonInfo
  , asyncNames :: [String] } deriving (Show)

data Sync =
  Sync
  { syncCommon :: CommonInfo
  , syncNames :: [T.SyncRead] } deriving (Show)

data Register =
  Register
  { registerName :: String
  , registerKind :: T.FullKind }

data RME2 = 
    WriteRME2 Int Int String String T.RtlExpr' T.Kind T.RtlExpr' (Maybe T.RtlExpr') T.RtlExpr' RME2 RME2 T.RtlExpr'
  | ReadReqRME2 Int Int String String String T.RtlExpr' T.Kind Bool T.RtlExpr' RME2 RME2 T.RtlExpr'
  | AsyncReadRME2 Int Int String String String Bool T.RtlExpr' T.RtlExpr' T.Kind RME2 RME2
  | ReadRespRME2 Int Int String String String String Bool T.Kind Bool RME2 RME2
  | NilRME2 --deriving (Show)

instance Show RME2 where
  show NilRME2 = "nil\n\n"
  show (WriteRME2 _ _ f _ _ _ _ _ _ m _ _) = "write: " ++ f ++ "\n" ++ show m
  show (ReadReqRME2 _ _ f _ _ _ _ _ _ m _ _) = "readreq: " ++ f ++ "\n" ++ show m
  show (AsyncReadRME2 _ _ f _ _ _ _ _ _ m _) = "asyncread: " ++ f ++ "\n" ++ show m
  show (ReadRespRME2 _ _ f _ _ _ _ _ _ m _) = "readresp: " ++ f ++ "\n" ++ show m

instance Show (T.RmeSimple T.Coq_rtl_ty RegMapTy) where
  show (T.VarRME v) = "var:\n" ++ show (meth_call_history v) ++ "\n"
  show (T.UpdRegRME r _ _ _ m) = "upd: " ++ r ++ "\n" ++ show m
  show (T.WriteRME _ _ f _ _ _ _ _ _ m _ _) = "write: " ++ f ++ "\n" ++ show m
  show (T.ReadReqRME _ _ f _ _ _ _ _ _ m _ _) = "readreq: " ++ f ++ "\n" ++ show m
  show (T.ReadRespRME _ _ f _ _ _ _ _ _ m _) = "readresp: " ++ f ++ "\n" ++ show m
  show (T.AsyncReadRME _ _ f _ _ _ _ _ _ m _) = "asyncread: " ++ f ++ "\n" ++ show m
  show (T.CompactRME m) = "compact\n" ++ show m

-- length_RME2 :: RME2 -> Int
-- length_RME2 NilRME2 = 0
-- length_RME2 (WriteRME2 _ _ _ _ _ _ _ _ _ m _ _) = 1 + length_RME2 m
-- length_RME2 (ReadReqRME2 _ _ _ _ _ _ _ _ _ m _ _) = 1 + length_RME2 m
-- length_RME2 (AsyncReadRME2 _ _ _ _ _ _ _ _ _ m) = 1 + length_RME2 m


rme2_to_rme :: RME2 -> RME
rme2_to_rme (WriteRME2 idxNum num writePort dataArray idx dataK val mask pred writeMap readMap arr) =
  T.WriteRME idxNum num writePort dataArray idx dataK val mask pred (rme2_to_rme writeMap) (rme2_to_rme readMap) arr
rme2_to_rme (ReadReqRME2 idxNum num readReq readReg dataArray idx dataK isAddr pred writeMap readMap arr) =
  T.ReadReqRME idxNum num readReq readReg dataArray idx dataK isAddr pred (rme2_to_rme writeMap) (rme2_to_rme readMap) arr
rme2_to_rme NilRME2 = T.VarRME $ empty_rmt
rme2_to_rme (AsyncReadRME2 idxNum num readPort dataArray writePort isWriteMask idx pred dataK writeMap readMap) =
  T.AsyncReadRME idxNum num readPort dataArray writePort isWriteMask idx pred dataK (rme2_to_rme writeMap) (rme2_to_rme readMap)
rme2_to_rme (ReadRespRME2 idxNum num readResp readReg dataArray writePort isWrMask dataK isAddr writeMap readMap) =
  T.ReadRespRME idxNum num readResp readReg dataArray writePort isWrMask dataK isAddr (rme2_to_rme writeMap) (rme2_to_rme readMap)

data RegMapTy =
  RegMapTy
  { reg_counters :: H.Map String Int
  , reg_constant :: H.Map String T.ConstT
  , meth_call_history :: RME2 } --deriving (Show)

is_nil_RME2 :: RME2 -> Bool
is_nil_RME2 NilRME2 = True
is_nil_RME2 _ = False

empty_rmt :: RegMapTy
empty_rmt = RegMapTy {
    reg_counters = H.empty
  , reg_constant = H.empty
  , meth_call_history = NilRME2
}

init_rmt :: [Register] -> [Async] -> [Sync] -> [Sync] -> RegMapTy
init_rmt regs asyncs isAddrs notIsAddrs = RegMapTy {
    reg_counters = foldr (\r m -> H.insert r 0 m) (foldr (\r m -> H.insert r 0 m) (foldr (\r m -> H.insert (registerName r) 0 m) H.empty regs) (concatMap (\s -> map T.readRegName $ syncNames s) isAddrs))
                   (concatMap (\s -> map T.readRegName $ syncNames s) notIsAddrs)
  , reg_constant = H.empty
  , meth_call_history = NilRME2
}

data ExprState = ExprState
  { let_counter :: Int
  , regmap_counters :: RegMapTy
  , meth_counters :: H.Map String Int
  , all_regs :: [Register]
  , all_asyncs :: [Async]
  , all_isAddrs :: [Sync]
  , all_not_isAddrs :: [Sync] }

init_state_aux :: [Register] -> [Async] -> [Sync] -> [Sync] -> [String] -> ExprState
init_state_aux regs asyncs isAddrs notIsAddrs meths = ExprState {
    let_counter = 0
  , regmap_counters = init_rmt regs asyncs isAddrs notIsAddrs
  , meth_counters = foldr (\meth m -> H.insert meth 0 m) H.empty meths
  , all_regs = regs
  , all_asyncs = asyncs
  , all_isAddrs = isAddrs
  , all_not_isAddrs = notIsAddrs
}

init_state :: PreModInput -> ExprState
init_state (_,(rfbs,basemod)) = let (asyncs, isAddrs, notIsAddrs) = process_rfbs rfbs in
 init_state_aux (regs_of_basemod basemod) asyncs isAddrs notIsAddrs (get_calls_from_basemod basemod rfbs) 

type PredCall = (T.RtlExpr', T.RtlExpr')

queryReg :: String -> T.FullKind -> Bool -> RME -> T.RtlExpr
queryReg name k isWrite regMap =
  query regMap
  where
    query (T.VarRME v) = T.Var k $ T.unsafeCoerce (name, Just $ reg_counters v !!! name)
    query (T.UpdRegRME r pred k val regMap') =
      let restVal = query regMap' in
        if r == name
        then
          case pred of
            T.Const T.Bool (T.ConstBool True) -> val
            _ -> T.ITE k pred val restVal
        else restVal
    query (T.WriteRME idxNum num writePort dataArray idx dataK val mask pred writeMap readMap arr) =
      query (if isWrite then writeMap else readMap)
    query (T.ReadReqRME idxNum num readReq readReg dataArray idx dataK isAddr pred writeMap readMap arr) =
      query (if isWrite then writeMap else readMap)
    query (T.ReadRespRME idxNum num readResp readReg dataArray writePort isWrMask dataK isAddr writeMap readMap) =
      query (if isWrite then writeMap else readMap)
    query (T.AsyncReadRME idxNum num readPort dataArray writePort isWrMask idx pred k writeMap readMap) =
      query (if isWrite then writeMap else readMap)
    query (T.CompactRME regMap) =
      query regMap

createPredCall :: String -> T.Kind -> [PredCall] -> PredCall
createPredCall s k [a@(T.Var _ pred, T.Var _ call)] = a
createPredCall _ k predCalls = T.predPackOr k predCalls

getPredCallList :: String -> T.Kind -> Int -> [PredCall]
getPredCallList name k count =
  (map (\i -> (T.Var (T.SyntaxKind T.Bool) $ T.unsafeCoerce (name ++ "#_enable", Just i), T.Var (T.SyntaxKind k) $ T.unsafeCoerce (name ++ "#_argument", Just i))) [0..count])

eval_bool_expr :: T.RtlExpr' -> Maybe Bool --three-value logic, Nothing = not statically known
eval_bool_expr (T.Const T.Bool (T.ConstBool b)) = Just b
eval_bool_expr (T.UniBool T.Neg e) = liftM not $ eval_bool_expr e
eval_bool_expr (T.CABool T.And es) = foldr (liftM2 (&&)) (Just True) $ map eval_bool_expr es
eval_bool_expr (T.CABool T.Or es) = foldr (liftM2 (||)) (Just False) $ map eval_bool_expr es
eval_bool_expr (T.CABool T.Xor es) = foldr (liftM2 (/=)) (Just False) $ map eval_bool_expr es
eval_bool_expr _ = Nothing

is_const_true :: T.RtlExpr' -> Bool
is_const_true e = case eval_bool_expr e of
  Just True -> True
  _ -> False

is_const_false :: T.RtlExpr' -> Bool
is_const_false e = case eval_bool_expr e of
  Just False -> True
  _ -> False

-- is_const_true :: T.RtlExpr' -> Bool
-- is_const_true (T.Const T.Bool (T.ConstBool True)) = True
-- is_const_true (T.UniBool T.Neg e) = is_const_false e
-- is_const_true (T.CABool T.And es) = all is_const_true es
-- is_const_true (T.CABool T.Or es) = any is_const_true es
-- is_const_true (T.CABool T.Xor es) = all (\e -> is_const_true e || is_const_false e) es &&
--   (odd $ length $ filter is_const_true es)
-- is_const_true _ = False

-- is_const_false :: T.RtlExpr' -> Bool
-- is_const_false (T.Const T.Bool (T.ConstBool False)) = True
-- is_const_false (T.UniBool T.Neg e) = is_const_true e
-- is_const_false (T.CABool T.And es) = any is_const_false es
-- is_const_false (T.CABool T.Or es) = all is_const_false es
-- is_const_false (T.CABool T.Xor es) = all (\e -> is_const_true e || is_const_false e) es &&
--   (even $ length $ filter is_const_true es)
-- is_const_false _ = False

flatten_RME :: RME -> RME2
flatten_RME (T.VarRME v) = meth_call_history v
flatten_RME (T.UpdRegRME r pred k val regMap') = flatten_RME regMap'
flatten_RME (T.WriteRME idxNum num writePort dataArray idx dataK val mask pred writeMap readMap arr) = 
  WriteRME2 idxNum num writePort dataArray idx dataK val mask pred (flatten_RME writeMap) (flatten_RME readMap) arr
flatten_RME (T.ReadReqRME idxNum num readReq readReg dataArray idx dataK isAddr pred writeMap readMap arr) =
  ReadReqRME2 idxNum num readReq readReg dataArray idx dataK isAddr pred (flatten_RME writeMap) (flatten_RME readMap) arr
flatten_RME (T.ReadRespRME idxNum num readResp readReg dataArray writePort isWrMask dataK isAddr writeMap readMap) =
  ReadRespRME2 idxNum num readResp readReg dataArray writePort isWrMask dataK isAddr (flatten_RME writeMap) (flatten_RME readMap)
flatten_RME (T.AsyncReadRME idxNum num readPort dataArray writePort isWrMask idx pred k writeMap readMap) = 
  AsyncReadRME2 idxNum num readPort dataArray writePort isWrMask idx pred k (flatten_RME writeMap) (flatten_RME readMap)
flatten_RME (T.CompactRME rme) = flatten_RME rme

queryRfWrite :: String -> Int -> Int -> T.Kind -> Bool -> Bool -> RME2 -> PredCall
queryRfWrite name idxNum num k isMask isWrite regMap =
  createPredCall name writeType predCalls
  where
    writeType = if isMask then T.coq_WriteRqMask (log2_up idxNum) num k else T.coq_WriteRq (log2_up idxNum) (T.Array num k)
    addrSize = log2_up idxNum
    predCalls = query regMap

    query NilRME2 = []
    query (ReadReqRME2 idxNum num readReq readReg dataArray idx dataK isAddr pred writeMap readMap arr) = query (if isWrite then writeMap else readMap)
    query (AsyncReadRME2 idxNum num readPort dataArray writePort isWriteMask idx pred dataK writeMap readMap) = query (if isWrite then writeMap else readMap)
    query (ReadRespRME2 idxNum num readResp readReg dataArray writePort isWrMask dataK isAddr writeMap readMap) = query (if isWrite then writeMap else readMap)
    query (WriteRME2 idxNum num writePort dataArray idx dataK val mask pred writeMap readMap arr) =
      let restPredCall = query (if isWrite then writeMap else readMap) in
      let writeRq = (case mask of
                      Nothing -> T.createWriteRq idxNum num dataK idx val
                      Just mask' -> T.createWriteRqMask idxNum num dataK idx val mask') in
      let predpair = (pred, T.predPack (T.Bit $ T.size writeType) pred writeRq) in
      if is_const_false pred
        then restPredCall
        else if writePort == name
          then if is_const_true pred
            then [predpair]
            else predpair : restPredCall
          else restPredCall

queryAsyncReadReq :: String -> Int -> Bool -> RME2 -> PredCall
queryAsyncReadReq name idxNum isWrite regMap =
  createPredCall name (T.Bit (log2_up idxNum)) predCalls
  where
    predCalls = query regMap

    query NilRME2 = []
    query (ReadReqRME2 idxNum num readReq readReg dataArray idx dataK isAddr pred writeMap readMap arr) = query (if isWrite then writeMap else readMap)
    query (WriteRME2 idxNum num writePort dataArray idx dataK val mask pred writeMap readMap arr) = query (if isWrite then writeMap else readMap)
    query (ReadRespRME2 idxNum num readResp readReg dataArray writePort isWrMask dataK isAddr writeMap readMap) = query (if isWrite then writeMap else readMap)
    query (AsyncReadRME2 idxNum num readPort dataArray writePort isWriteMask idx pred dataK writeMap readMap) =
      let restPredAddr = query (if isWrite then writeMap else readMap) in
      let predpair = (pred, T.predPack (T.Bit (log2_up idxNum)) pred idx) in
      if is_const_false pred
        then restPredAddr
        else if readPort == name
          then if is_const_true pred
            then [predpair]
            else predpair : restPredAddr
          else restPredAddr

querySyncReadReqTail :: String -> RME2 -> RME2
querySyncReadReqTail name' regMap2 = query regMap2
  where
    query NilRME2 = NilRME2
    query (WriteRME2 idxNum num writePort dataArray idx dataK val mask pred writeMap readMap arr) = query writeMap
    query (AsyncReadRME2 idxNum num readPort dataArray writePort isWriteMask idx pred dataK writeMap readMap) = query writeMap
    query (ReadRespRME2 idxNum num readResp readReg dataArray writePort isWrMask dataK isAddr writeMap readMap) = query writeMap
    query (ReadReqRME2 idxNum num readReq readReg dataArray idx dataK isAddr pred writeMap readMap arr) =
      if readReq == name'
        then writeMap
        else query writeMap

querySyncReadReq :: String -> Int -> Bool -> RME2 -> (RME2, PredCall)
querySyncReadReq name idxNum isWrite regMap =
  (tail, createPredCall name (T.Bit (log2_up idxNum)) predCalls)
  where
    (tail, predCalls) = query regMap

    query NilRME2 = (NilRME2, [])
    query (WriteRME2 idxNum num writePort dataArray idx dataK val mask pred writeMap readMap arr) = query (if isWrite then writeMap else readMap)
    query (AsyncReadRME2 idxNum num readPort dataArray writePort isWriteMask idx pred dataK writeMap readMap) = query (if isWrite then writeMap else readMap)
    query (ReadRespRME2 idxNum num readResp readReg dataArray writePort isWrMask dataK isAddr writeMap readMap) = query (if isWrite then writeMap else readMap)
    query (ReadReqRME2 idxNum num readReq readReg dataArray idx dataK isAddr pred writeMap readMap arr) =
      let (tail', restPredAddr) = query (if isWrite then writeMap else readMap) in
      let predpair = (pred, T.predPack (T.Bit (log2_up idxNum)) pred idx) in
      if is_const_false pred
        then (tail', restPredAddr)
        else if readReq == name
          then if is_const_true pred
            then (if isWrite then writeMap else readMap ,[predpair])
            else (if isWrite then writeMap else readMap, predpair : restPredAddr)
          else (tail', restPredAddr)

queryIsAddrRegWrite :: String -> String -> Int -> RME2 -> T.RtlExpr'
queryIsAddrRegWrite name readReqName idxNum regMap = T.ITE (T.SyntaxKind (T.Bit (log2_up idxNum))) (fst readCall) (snd readCall) regVal
  where
    (_,readCall) = querySyncReadReq readReqName idxNum True regMap
    regVal = T.Var (T.SyntaxKind (T.Bit (log2_up idxNum))) (T.unsafeCoerce (name, Nothing))

queryNotIsAddrRegWrite :: String -> String -> Int -> Int -> T.Kind -> Bool -> RME2 -> T.RtlExpr'
queryNotIsAddrRegWrite writeName readReqName idxNum num k isMask regMap = pointwise
  where
    (tail, readCall) = querySyncReadReq readReqName idxNum True regMap
    writeCall = queryRfWrite writeName idxNum num k isMask True tail
    pointwise = T.pointwiseIntersection idxNum num k isMask (fst readCall) (snd readCall) (fst writeCall) (T.unsafeCoerce $ snd writeCall)

queryAsyncReadResp :: String -> String -> Int -> Int -> T.Kind -> Bool -> RME2 -> T.RtlExpr'
queryAsyncReadResp name writeName idxNum num k isMask regMap =
  T.pointwiseBypass num k pointwise respVal
  where
    respVal = (T.Var (T.SyntaxKind (T.Array num k)) (T.unsafeCoerce (name ++ "#_return", Nothing)))
    readCall = queryAsyncReadReq name idxNum False regMap
    writeCall = queryRfWrite writeName idxNum num k isMask False regMap
    pointwise = T.pointwiseIntersection idxNum num k isMask (fst readCall) (snd readCall) (fst writeCall) (T.unsafeCoerce $ snd writeCall)

queryIsAddrReadResp :: String -> String -> String -> Int -> Int -> T.Kind -> Bool -> RME2 -> T.RtlExpr'
queryIsAddrReadResp name writeName regName idxNum num k isMask regMap =
  T.pointwiseBypass num k pointwise respVal
  where
    respVal = T.Var (T.SyntaxKind (T.Array num k)) (T.unsafeCoerce (name ++ "#_return", Nothing))
    readAddr = T.Var (T.SyntaxKind (T.Array num k)) (T.unsafeCoerce (regName, Nothing))
    writeCall = queryRfWrite writeName idxNum num k isMask False regMap
    pointwise = T.pointwiseIntersection idxNum num k isMask (T.Const T.Bool (T.ConstBool True)) readAddr (fst writeCall) (T.unsafeCoerce $ snd writeCall)

queryNotIsAddrReadResp :: String -> String -> Int -> T.Kind -> T.RtlExpr'
queryNotIsAddrReadResp name regName num k =
  T.pointwiseBypass num k bypass respVal
  where
    bypass = T.Var (T.SyntaxKind (T.Array num (T.coq_Maybe k))) (T.unsafeCoerce (regName, Nothing))
    respVal = T.Var (T.SyntaxKind (T.Array num k)) (T.unsafeCoerce (name ++ "#_return", Nothing))

type CA_rtl = T.CompActionSimple T.Coq_rtl_ty RegMapTy

data VerilogExprs = VerilogExprs {
    assign_exprs :: [(T.VarType, T.RtlExpr')]
  , if_begin_end_exprs :: [(T.RtlExpr', [T.SysT T.Coq_rtl_ty])]
  , return_expr :: T.RtlExpr'
  , return_maps :: RME
}

monad_concat :: Monad m => [m [a]] -> m [a]
monad_concat ms = fmap concat $ sequence ms

tmp_var :: Int -> T.VarType
tmp_var j = ("tmp", Just j)

arg_var :: String -> Int -> T.VarType
arg_var f i = (f ++ "#_argument", Just i)

let_count :: State ExprState Int
let_count = do
  s <- get
  let n = let_counter s
  put $ s { let_counter = n+1 }
  return (n+1)

meth_count :: String -> State ExprState Int
meth_count f = do
  s <- get
  let n = meth_counters s !!! f
  put $ s { meth_counters = H.insert f (n+1) $ meth_counters s }
  return (n+1)

reg_count :: String -> State ExprState Int
reg_count r = do
  s <- get
  let rmc = regmap_counters s
  let rc = reg_counters rmc
  let n = rc !!! r
  put $ s { regmap_counters = rmc { reg_counters = H.insert r (n+1) rc } }
  return (n+1)

ins_reg_constant :: String -> T.ConstT -> State ExprState ()
ins_reg_constant r val = do
  s <- get
  let rmc = regmap_counters s
  let rc = reg_constant rmc
  put (s { regmap_counters = rmc { reg_constant = H.insert r val rc } })
  
del_reg_constant :: String -> State ExprState ()
del_reg_constant r = do
  s <- get
  let rmc = regmap_counters s
  let rc = reg_constant rmc
  put (s { regmap_counters = rmc { reg_constant = H.delete r rc } })

convAny :: T.Any -> T.VarType
convAny x = T.unsafeCoerce x

do_reg :: String -> T.FullKind -> RME -> State ExprState [(T.VarType, T.RtlExpr')]
do_reg r k m = case queryReg r k True m of
  e@(T.Const k val) -> do
    i <- reg_count r
    ins_reg_constant r val
    return [((r, Just i), e)]
  e@(T.Var _ x) -> do
    let (r', Just _) = convAny x
    if r == r'
      then return []
      else do
        del_reg_constant r
        i <- reg_count r
        return [((r, Just i),e)]
  e -> do
    del_reg_constant r
    i <- reg_count r
    return [((r, Just i),e)]

do_regs :: RME -> State ExprState [(T.VarType, T.RtlExpr')]
do_regs m = do
  s <- get
  monad_concat $ map (\(Register r k) -> do_reg r k m) (all_regs s)

do_isAddr_read_reg :: String -> String -> Int -> RME2 -> State ExprState [(T.VarType, T.RtlExpr')]
do_isAddr_read_reg name readReqName idxNum regMap = case queryIsAddrRegWrite name readReqName idxNum regMap of
  e@(T.Var _ x) ->
    let (name', Just _) = convAny x in
      if name == name'
      then return []
      else do
        i <- reg_count name
        return [((name, Just i), e)]
  e -> do
    i <- reg_count name
    return [((name, Just i), e)]

do_isAddr_read_regs :: RME2 -> State ExprState [(T.VarType, T.RtlExpr')]
do_isAddr_read_regs m = do
  s <- get
  monad_concat $ concatMap (\(Sync common reads) -> map (\(T.Build_SyncRead readReqName _ r) -> do_isAddr_read_reg r readReqName (commonIdxNum common) m) reads) $ all_isAddrs s

flatten_RME_state :: RME -> State ExprState ()
flatten_RME_state regMap = do
  s <- get
  let rmc = regmap_counters s
  put $ s { regmap_counters = rmc { meth_call_history = {-trace ("RME:\n" ++ (show regMap) ++ "Method Call History:\n" ++ (show $ flatten_RME regMap))-} flatten_RME regMap } } 

do_not_isAddr_read_reg :: String -> String -> String -> Int -> Int -> T.Kind -> Bool -> RME2 -> State ExprState [(T.VarType, T.RtlExpr')]
do_not_isAddr_read_reg regName writeName readReqName idxNum num k isMask regMap = do
  case queryNotIsAddrRegWrite writeName readReqName idxNum num k isMask regMap of
    e@(T.Var _ x) ->
      let (regName', Just _) = convAny x in
        if regName == regName'
        then return []
        else do
          i <- reg_count regName
          return [((regName, Just i), e)]
    e -> do
      i <- reg_count regName
      return [((regName, Just i), e)]

do_not_isAddr_read_regs :: RME2 -> State ExprState [(T.VarType, T.RtlExpr')]
do_not_isAddr_read_regs m = do
  s <- get
  monad_concat $ concatMap (\(Sync common reads) -> map (\(T.Build_SyncRead reqName _ regName) ->
    do_not_isAddr_read_reg regName (commonWrite common) reqName (commonIdxNum common) (commonNum common) (commonData common) (commonIsWrMask common) m) reads) $ all_not_isAddrs s

get_all_upds :: RME -> State ExprState [(T.VarType, T.RtlExpr')]
get_all_upds m = let m' = flatten_RME m in do
  flatten_RME_state m
  assigns1 <- do_regs m
  assigns2 <- do_isAddr_read_regs m'
  assigns3 <- do_not_isAddr_read_regs m'
  return $ assigns1 ++ assigns2 ++ assigns3

-- Counters contain the next value to assign

ppCAS :: CA_rtl -> State ExprState VerilogExprs
ppCAS (T.CompCall_simple f (_,k) pred arg _ cont) = do
  i <- meth_count f
  j <- let_count
  y <- ppCAS (cont $ tmp_var j)
  return $ y {
    assign_exprs = ((f ++ "#_argument", Just i), arg) :
                   ((f ++ "#_enable", Just i), pred) :
                   (tmp_var j, T.Var (T.SyntaxKind k) $ T.unsafeCoerce (f ++ "#_return", Nothing)) :
                   assign_exprs y 
  }

ppCAS (T.CompLetExpr_simple (T.NativeKind _) _ _ _) = error "NativeKind encountered."
ppCAS (T.CompLetExpr_simple (T.SyntaxKind _) expr _ cont) = do
  j <- let_count
  y <- ppCAS (cont $ T.unsafeCoerce $ tmp_var j)
  return $ y {
    assign_exprs = (tmp_var j, expr) : assign_exprs y
  }

ppCAS (T.CompNondet_simple (T.NativeKind _) _ _) = error "NativeKind encountered."
ppCAS (T.CompNondet_simple (T.SyntaxKind k) _ cont) = do
  j <- let_count
  y <- ppCAS (cont $ T.unsafeCoerce $ tmp_var j)
  return $ y {
    assign_exprs = (tmp_var j, T.Const k $ T.getDefaultConst k) : assign_exprs y
  }

ppCAS (T.CompSys_simple pred xs _ a) = do
  y <- ppCAS a
  return $ y {
    if_begin_end_exprs = (pred,xs) : if_begin_end_exprs y
  }

ppCAS (T.CompReadReg_simple r k regMap _ cont) = do
  j <- let_count
  y <- ppCAS (cont $ T.unsafeCoerce $ tmp_var j)
  return $ y {
    assign_exprs = (tmp_var j, trace ("RME @ CompReadReg_simple:\n" ++ show regMap ++ "\n\n") $ queryReg r k False regMap) : assign_exprs y
  }

ppCAS (T.CompRet_simple _ retVal regMap) = do
  return $ VerilogExprs {
    assign_exprs = []
    , if_begin_end_exprs = []
    , return_expr = retVal
    , return_maps = trace ("RME @ CompRet_simple:\n" ++ show regMap ++ "\n\n") $ regMap
  }

ppCAS (T.CompLetFull_simple _  a _ cont) = do
  (VerilogExprs assigns_a if_begin_ends_a ret_a map_a) <- ppCAS a
  j <- let_count
  assigns <- trace ("RME returned @ CompLetFull_simple:\n" ++ show map_a ++ "\n\n") $ get_all_upds map_a
  s <- get
  y <- ppCAS (cont (tmp_var j) $ regmap_counters s)
  return $ y {
    assign_exprs = assigns_a ++ (tmp_var j, ret_a) : assigns ++ assign_exprs y
    , if_begin_end_exprs = if_begin_ends_a ++ if_begin_end_exprs y
  }

ppCAS (T.CompAsyncRead_simple idxNum num readPort dataArray writePort isWrMask idx pred k readMap _ cont) = do
  j <- let_count
  y <- ppCAS (cont $ tmp_var j)
  return $ y {
    assign_exprs = (tmp_var j, trace ("RME @ CompAsyncRead_simple:\n" ++ show readMap ++ "\n\n") $ queryAsyncReadResp readPort writePort idxNum num k isWrMask $ flatten_RME readMap) : assign_exprs y
  }

ppCAS (T.CompSyncReadRes_simple idxNum num readResp readReg dataArray writePort isWrMask k True readMap _ cont) = do
  j <- let_count
  y <- ppCAS (cont $ tmp_var j)
  return $ y {
    assign_exprs = (tmp_var j, trace ("RME @ CompSyncReadRes_simple:\n" ++ show readMap ++ "\n\n") $ queryIsAddrReadResp readResp writePort readReg idxNum num k isWrMask $ flatten_RME readMap) : assign_exprs y
  }

ppCAS (T.CompSyncReadRes_simple idxNum num readResp readReg dataArray writePort isWrMask k False readMap _ cont) = do
  j <- let_count
  y <- ppCAS (cont $ tmp_var j)
  return $ y {
    assign_exprs = (tmp_var j, trace ("RME @ CompSyncReadRes_simple:\n" ++ show readMap ++ "\n\n") $ queryNotIsAddrReadResp readResp readReg num k) : assign_exprs y
  }

ppCAS (T.CompWrite_simple idxNum k writePort dataArray readMap _ cont) = do
  j <- let_count
  y <- ppCAS (cont $ tmp_var j)
  return $ y {
    assign_exprs = (tmp_var j, trace ("RME @ CompWrite_simple:\n" ++ show readMap ++ "\n\n") $ T.Const (T.Bit 0) $ T.getDefaultConst (T.Bit 0)) : assign_exprs y
  }

ppCAS (T.CompSyncReadReq_simple idxNum num k readReq readReg dataArray isAddr readMap _ cont) = do
  j <- let_count
  y <- ppCAS (cont $ tmp_var j)
  return $ y {
    assign_exprs = (tmp_var j, trace ("RME @ CompSyncReadReq_simple:\n" ++ show readMap ++ "\n\n") $ T.Const (T.Bit 0) $ T.getDefaultConst (T.Bit 0)) : assign_exprs y
  }

get_final_assigns :: ExprState -> [T.RegFileBase] -> [(T.VarType, T.RtlExpr')]
get_final_assigns s rfbs = let (_,isAddrs,notIsAddrs) = process_rfbs rfbs in
  map (\(Register r k) -> ((r,Nothing), T.Var k $ T.unsafeCoerce (r, Just $ reg_counters (regmap_counters s) !!! r))) (all_regs s ++
                                                                                                                        all_isAddr_shadows isAddrs ++
                                                                                                                        all_not_isAddr_shadows notIsAddrs)


en_arg_helper :: String -> PredCall -> [(T.VarType, T.RtlExpr')]
en_arg_helper f (pred, call) =
  [ ((f ++ "#_enable",Nothing), pred)
  , ((f ++ "#_argument",Nothing), call)
  ]

en_arg_final :: String -> T.Kind -> H.Map String Int -> [(T.VarType, T.RtlExpr')]
en_arg_final f argk counters =
  en_arg_helper f (createPredCall f argk (getPredCallList f argk (counters !!! f)))

get_final_meth_assigns :: T.BaseModule -> [T.RegFileBase] -> ExprState -> [(T.VarType, T.RtlExpr')]
get_final_meth_assigns basemod rfbs s =
  concatMap (\(f, (argk, _)) -> en_arg_final f argk $ meth_counters s) (get_normal_meth_calls_with_sign basemod rfbs)

get_common_from_write :: String -> [Async] -> [Sync] -> [Sync] -> CommonInfo
get_common_from_write write asyncs isAddrs notIsAddrs =
  let commons = map asyncCommon asyncs ++ map syncCommon (isAddrs ++ notIsAddrs) in
  fromJust $ find (\c -> commonWrite c == write) commons

get_common_from_async_read :: String -> [Async] -> CommonInfo
get_common_from_async_read read asyncs = asyncCommon $ fromJust $ find (\async -> read `elem` asyncNames async) asyncs

get_common_from_sync_readRq :: String -> [Sync] -> CommonInfo
get_common_from_sync_readRq readRq syncs = syncCommon $ fromJust $ find
  (\sync -> readRq `elem` map (\(T.Build_SyncRead r _ _) -> r) (syncNames sync)) syncs

get_final_rfmeth_assigns :: [T.RegFileBase] -> ExprState -> [(T.VarType, T.RtlExpr')]
get_final_rfmeth_assigns rfbs s = let (asyncs,isAddrs,notIsAddrs) = process_rfbs rfbs in
  let history = meth_call_history $ regmap_counters s in

    --writes
       concatMap (\(write,argk) ->
          let c = get_common_from_write write asyncs isAddrs notIsAddrs in
            en_arg_helper write $ queryRfWrite write (commonIdxNum c) (commonNum c) (commonData c) (commonIsWrMask c) True history) (get_write_meths_with_arg rfbs)

    --async reads
    ++ concatMap (\(read,argk) ->
          let c = get_common_from_async_read read asyncs in
            en_arg_helper read $ queryAsyncReadReq read (commonIdxNum c) True history) (get_async_reads_with_arg asyncs)
 
    --isAddr readreq
    ++ concatMap (\(readRq,argk) ->
          let c = get_common_from_sync_readRq readRq isAddrs in
            en_arg_helper readRq $ snd $ querySyncReadReq readRq (commonIdxNum c) True history) (get_sync_readReqs_with_arg isAddrs)
 
    --notIsAddr readreq
    ++ concatMap (\(readRq,argk) ->
          let c = get_common_from_sync_readRq readRq notIsAddrs in
            en_arg_helper readRq $ snd $ querySyncReadReq readRq (commonIdxNum c) True history) (get_sync_readReqs_with_arg notIsAddrs)
 
all_verilog :: ModInput -> (VerilogExprs, [(T.VarType, T.RtlExpr')], H.Map String T.ConstT)
all_verilog input@((strs,(rfbs,basemod)),cas) =
  let (vexprs,final_state) = runState (ppCAS $ cas) (init_state (fst input)) in
  let reg_consts = reg_constant $ regmap_counters final_state in
  let final_assigns = get_final_assigns final_state rfbs in
  let final_meth_assigns = get_final_meth_assigns basemod rfbs final_state in
  let final_rfmeth_assigns = get_final_rfmeth_assigns rfbs final_state in
    (vexprs { assign_exprs = (all_initialize input) ++ assign_exprs vexprs ++ final_meth_assigns ++ final_rfmeth_assigns }, final_assigns, reg_consts)

kind_of_expr :: T.Expr ty -> T.FullKind
kind_of_expr (T.Var k _) = k
kind_of_expr (T.Const k _) = T.SyntaxKind k
kind_of_expr (T.UniBool _ _) = T.SyntaxKind T.Bool
kind_of_expr (T.CABool _ _) = T.SyntaxKind T.Bool
kind_of_expr (T.UniBit _ n2 _ _) = T.SyntaxKind $ T.Bit n2
kind_of_expr (T.CABit n _ _) = T.SyntaxKind $ T.Bit n
kind_of_expr (T.BinBit _ _ n3 _ _ _) = T.SyntaxKind $ T.Bit n3
kind_of_expr (T.BinBitBool _ _ _ _ _) = T.SyntaxKind T.Bool
kind_of_expr (T.ITE k _ _ _) = k
kind_of_expr (T.Eq _ _ _) = T.SyntaxKind T.Bool
kind_of_expr (T.ReadStruct _ fk _ _ i) = T.SyntaxKind $ fk i
kind_of_expr (T.BuildStruct n fk fs _) = T.SyntaxKind $ T.Struct n fk fs
kind_of_expr (T.ReadArray _ _ k _ _) = T.SyntaxKind k
kind_of_expr (T.ReadArrayConst _ k _ _) = T.SyntaxKind k
kind_of_expr (T.BuildArray n k _) = T.SyntaxKind $ T.Array n k

data RtlModStats = RtlModStats {
    num_hiddenWires :: Int
  , num_regFiles :: Int
  , num_inputs :: Int
  , num_outputs :: Int
  , num_regInits :: Int
  , num_regWrites :: Int
  , num_wires :: Int
  , num_sys :: Int
} deriving (Show)

get_stats :: T.RtlModule -> RtlModStats
get_stats (T.Build_RtlModule hw rf ins outs inits writes wires sys) = RtlModStats {
    num_hiddenWires = length hw
  , num_regFiles = length rf
  , num_inputs = length ins
  , num_outputs = length outs
  , num_regInits = length inits
  , num_regWrites = length writes
  , num_wires = length wires
  , num_sys = length sys
}

mkInits :: ModInput -> [(T.VarType, (T.FullKind,T.RegInitValT))]
mkInits ((strs,(rfbs,basemod)),cas) = let (_,isAddrs,notIsAddrs) = process_rfbs rfbs in

  --regular inits
     map (\(r,p) -> ((r,Nothing),p)) (T.getRegisters basemod)

  --isAddr shadow regs
  ++ (map (\(Register r k) -> ((r,Nothing),(k,Nothing))) $ all_isAddr_shadows isAddrs)

  --notIsAddr shadow regs
  ++ (map (\(Register r k) -> ((r,Nothing),(k, Just $ T.getDefaultConstFullKind k ))) $ all_not_isAddr_shadows notIsAddrs)

not_is_reg_constant :: H.Map String T.ConstT -> [(T.VarType, (T.FullKind,T.RegInitValT))] -> T.VarType -> Bool
not_is_reg_constant reg_consts inits (r, _) =
  case (H.lookup r reg_consts, find (\((x, _), _) -> x == r) inits) of
    (Just constVal, Just (_, (_, Just (T.SyntaxConst _ constVal2)))) -> constVal /= constVal2
    (_, _) -> True

mkRtlMod :: ModInput -> T.RtlModule
mkRtlMod input@((strs,(rfbs,basemod)),cas) =
  let (vexprs,fin_assigns,reg_consts) = all_verilog input in
                  T.Build_RtlModule
  {- hiddenWires -} (concatMap (\f -> [(f ++ "#_enable",Nothing), (f ++ "#_return",Nothing), (f ++ "#_argument",Nothing)]) strs)
  {- regFiles    -} rfbs
  {- inputs      -} (map (\(f,(_,k)) -> ((f ++ "#_return",Nothing),k)) $ T.getCallsWithSignPerMod $ T.Base basemod)
  {- outputs     -} (concatMap (\(f,(k,_)) -> [((f ++ "#_enable",Nothing), T.Bool), ((f ++ "#_argument",Nothing),k)]) $ T.getCallsWithSignPerMod $ T.Base basemod)
  {- regInits    -} inits
  {- regWrites   -} (filter (\(x, _) -> not_is_reg_constant reg_consts inits x) (map (\(v,e) -> (v,(kind_of_expr e,e))) $ fin_assigns))
  {- wires       -} (map (\(v,e) -> (v,(kind_of_expr e,e))) $ assign_exprs vexprs)
  {- sys         -} (if_begin_end_exprs vexprs)
  where
    inits = mkInits input
    

mkRtlFull ::  ([String], ([T.RegFileBase], T.BaseModule)) -> T.RtlModule
mkRtlFull x@(hides, (rfs, bm)) = mkRtlMod (x, T.coq_CAS_RulesRf (regmap_counters $ init_state x) (T.getRules bm) rfs)
--mkRtlFull m = T.getRtl m

get_sys (T.Build_RtlModule _ _ _ _ _ _ _ sys) = sys

get_wires (T.Build_RtlModule _ _ _ _ _ _ wires _) = wires

print_ind_elt :: Show a => Int -> a -> IO()
print_ind_elt i x = do
  start <- getCurrentTime
  putStrLn $ show x
  end <- getCurrentTime
  let delta = diffUTCTime end start
  hPutStrLn stderr (show i ++ "; time = " ++ show delta)

output_list :: Show a => [a] -> [IO()]
output_list xs = let n = length xs in do
  i <- [0..(n-1)]
  return $ print_ind_elt i (xs !! i)

main :: IO()
main = putStrLn $ ppTopModule $ mkRtlFull T.rtlMod
