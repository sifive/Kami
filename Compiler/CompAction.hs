{-# OPTIONS_GHC -XStandaloneDeriving #-}

import qualified Target as T
import Data.List
import Data.Char
import Control.Monad.State.Lazy
import qualified Data.Map.Lazy as H
import Debug.Trace
import Numeric
import PrettyPrintVerilog

{-
--show instances for debugging
deriving instance Show T.SyncRead

instance Show T.Kind where
  show _ = "kind"

instance Show T.RegFileInitT where
  show _ = "RegFileInitT"

--access with helpful error msg
(!!!) :: (Ord k, Show k, Show v) => H.Map k v -> k -> v
(!!!) m k = case m H.!? k of
  Just v -> v
  Nothing -> error ("Key " ++ show k ++ " not found in map " ++ show m ++ ".") 

-- log2_up :: Int -> Int
-- log2_up = ceiling . (logBase 2) . fromIntegral

get_rfr_meths :: T.RegFileReaders -> [String]
get_rfr_meths (T.Async reads) = reads
get_rfr_meths (T.Sync _ reads) = concatMap (\(T.Build_SyncRead r1 r2 r3) -> [r1,r2,r3]) reads

get_rf_meths :: T.RegFileBase -> [String]
get_rf_meths (T.Build_RegFileBase _ _ _ readers write _ _ _) = write : get_rfr_meths readers

get_normal_meth_calls_with_sign :: T.Mod -> [(String,(T.Kind,T.Kind))]
get_normal_meth_calls_with_sign m =
  let (_,(rfbs,_)) = T.separateModRemove m in
  let rf_meths = concatMap get_rf_meths rfbs in
    filter (\(f,_) -> not $ f `elem` rf_meths) $ T.getCallsWithSignPerMod m

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

--ModInput without the CAS
type PreModInput = ([T.RegFileBase], T.BaseModule)

type ModInput = ([String], [T.RegFileBase], T.BaseModule, T.CompActionSimple T.Coq_rtl_ty RegMapTy)

get_premodinput :: ModInput -> PreModInput
get_premodinput (a,b,c,d) = (b,c)

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
all_isAddr_shadows isAddrs = concatMap (\(Sync common names) -> map (\(T.Build_SyncRead _ _ name) -> Register name $ T.SyntaxKind $ T.Bit $ commonIdxNum common) names) isAddrs

all_not_isAddr_shadows :: [Sync] -> [Register]
all_not_isAddr_shadows notIsAddrs = concatMap (\(Sync common names) -> map (\(T.Build_SyncRead _ _ name) -> Register name $ T.SyntaxKind $ T.Array (commonNum common) $ T.coq_Maybe (commonData common)) names) notIsAddrs

all_regs_of_modinput :: ModInput -> [Register]
all_regs_of_modinput (_,rfbs,basemod,cas) = let (asyncs,isAddrs,notIsAddrs) = process_rfbs rfbs in
     regs_of_basemod basemod
  ++ all_isAddr_shadows isAddrs
  ++ all_not_isAddr_shadows notIsAddrs
  
en_arg_initialize :: String -> T.Kind -> [(T.VarType, T.RtlExpr')]
en_arg_initialize f k = [((f ++ "#_enable",Just 0), T.Const T.Bool $ T.ConstBool False),
                   ((f ++ "#_argument",Just 0), T.Const k $ T.getDefaultConst k)]

get_calls_from_basemod :: T.BaseModule -> [String]
get_calls_from_basemod basemod = map fst (get_normal_meth_calls_with_sign $ T.Base basemod)

all_initialize :: ModInput -> [(T.VarType, T.RtlExpr')]
all_initialize modinput@(_,rfbs,basemod,_) =
  let regs = all_regs_of_modinput modinput in
  let (asyncs,isAddrs,notIsAddrs) = process_rfbs rfbs in

    --regular regs/shadow regs
     map (\(Register reg k) -> ((reg, Just 0), T.Var k $ T.unsafeCoerce (reg,Nothing))) regs

    --all rf meths
  ++ concatMap (\(f,argk) -> en_arg_initialize f argk) (get_write_meths_with_arg rfbs ++ get_async_reads_with_arg asyncs ++ get_sync_readReqs_with_arg (isAddrs ++ notIsAddrs))

    --normal methods
  ++ concatMap (\(f,(argk,_)) -> en_arg_initialize f argk) (get_normal_meth_calls_with_sign $ T.Base basemod)

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

data RegMapTy =
  RegMapTy
  { reg_counters :: H.Map String Int
  , write_counters :: H.Map String Int
  , async_read_counters :: H.Map String Int
  , isAddr_read_req_counters :: H.Map String Int
  , isAddr_read_reg_counters :: H.Map String Int
  , not_isAddr_read_req_counters :: H.Map String Int
  , not_isAddr_read_reg_counters :: H.Map String Int } deriving (Show)

init_rmt :: [Register] -> [Async] -> [Sync] -> [Sync] -> RegMapTy
init_rmt regs asyncs isAddrs notIsAddrs = RegMapTy {
    reg_counters = foldr (\r m -> H.insert (registerName r) 0 m) H.empty regs
  , write_counters = foldr (\wr m -> H.insert wr 0 m) H.empty (map (commonWrite . asyncCommon) asyncs ++ map (commonWrite . syncCommon) (isAddrs ++ notIsAddrs))
  , async_read_counters = foldr (\r m -> H.insert r 0 m) H.empty $ concatMap asyncNames asyncs
  , isAddr_read_req_counters = foldr (\r m -> H.insert r 0 m) H.empty $ concatMap (\s -> map T.readReqName $ syncNames s) isAddrs
  , isAddr_read_reg_counters = foldr (\r m -> H.insert r 0 m) H.empty $ concatMap (\s -> map T.readRegName $ syncNames s) isAddrs
  , not_isAddr_read_req_counters = foldr (\r m -> H.insert r 0 m) H.empty $ concatMap (\s -> map T.readReqName $ syncNames s) notIsAddrs
  , not_isAddr_read_reg_counters = foldr (\r m -> H.insert r 0 m) H.empty $ concatMap (\s -> map T.readRegName $ syncNames s) notIsAddrs
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
init_state (rfbs,basemod) = let (asyncs, isAddrs, notIsAddrs) = process_rfbs rfbs in
 init_state_aux (regs_of_basemod basemod) asyncs isAddrs notIsAddrs (get_calls_from_basemod basemod) 

async_of_readName :: String -> State ExprState Async
async_of_readName readName = do
  s <- get
  case find (\a -> readName `elem` asyncNames a) (all_asyncs s) of
    Just a -> return a
    Nothing -> error $ "Name " ++ readName ++ " not found in all_asyncs."

sync_of_readResp :: String -> State ExprState Sync
sync_of_readResp readResp = do
  s <- get
  case find (\sy -> readResp `elem` (map (\(T.Build_SyncRead _ r _) -> r) $ syncNames sy)) (all_isAddrs s) of
    Just sy -> return sy
    Nothing -> error $ "Name " ++ readResp ++ " not found in all_isAddrs."

data PredCall =
  PredCall
  { pred_val :: T.RtlExpr'
  , call_val :: T.RtlExpr' }

queryReg :: String -> T.FullKind -> Bool -> RME -> T.RtlExpr
queryReg name k isWrite regMap =
  query regMap
  where
    query (T.VarRME v) = T.Var k $ T.unsafeCoerce (name, Just $ reg_counters v !!! name)
    query (T.UpdRegRME r pred k val regMap') =
      let restVal = query regMap' in
        if r == name
        then T.ITE k pred val restVal
        else restVal
    query (T.WriteRME idxNum num writePort dataArray idx dataK val mask pred writeMap readMap arr) =
      query (if isWrite then writeMap else readMap)
    query (T.ReadReqRME idxNum num readReq readReg dataArray idx dataK isAddr pred writeMap readMap arr) =
      query (if isWrite then writeMap else readMap)
    query (T.ReadRespRME idxNum num readResp readReg dataArray dataK isAddr readMap) =
      query readMap
    query (T.AsyncReadRME idxNum num readPort dataArray idx pred k readMap) =
      query readMap
    query (T.CompactRME regMap) =
      query regMap

createPredCall :: String -> T.Kind -> [T.RtlExpr'] -> [T.RtlExpr'] -> PredCall
createPredCall s k [a@(T.Var _ pred)] [b@(T.Var _ call)] = PredCall a b
createPredCall _ k preds calls = PredCall (T.CABool T.Or preds) (T.CABit (T.size k) T.Bor calls)
  

queryRfWrite :: String -> Int -> Int -> T.Kind -> Bool -> Bool -> RME -> PredCall
queryRfWrite name idxNum num k isMask isWrite regMap =
  createPredCall name writeType preds calls
  -- PredCall (T.CABool T.Or preds) (T.orKind writeType calls)
  where
    writeType = if isMask then T.coq_WriteRqMask (log2_up idxNum) num k else T.coq_WriteRq (log2_up idxNum) (T.Array num k)
    addrSize = log2_up idxNum
    (preds, calls) = query regMap
    query (T.VarRME v) =
      let count = write_counters v !!! name in
        ([T.Var (T.SyntaxKind T.Bool) $ T.unsafeCoerce (name ++ "#_enable", Just count)], [T.Var (T.SyntaxKind writeType) $ T.unsafeCoerce (name ++ "#_argument", Just count)])
    query (T.UpdRegRME r pred k val regMap') = query regMap'
    query (T.WriteRME idxNum num writePort dataArray idx dataK val mask pred writeMap readMap arr) =
      let (restPred, restCall) = query (if isWrite then writeMap else readMap) in
        if writePort == name
        then (pred : restPred, T.predPack (T.Bit $ T.size writeType) pred (case mask of
                                                                              Nothing -> T.createWriteRq idxNum num dataK idx val
                                                                              Just mask' -> T.createWriteRqMask idxNum num dataK idx val mask') : restCall)
        else (restPred, restCall)
    query (T.ReadReqRME idxNum num readReq readReg dataArray idx dataK isAddr pred writeMap readMap arr) =
      query (if isWrite then writeMap else readMap)
    query (T.ReadRespRME idxNum num readResp readReg dataArray dataK isAddr readMap) =
      query readMap
    query (T.AsyncReadRME idxNum num readPort dataArray idx pred k readMap) =
      query readMap
    query (T.CompactRME regMap) =
      query regMap

queryAsyncReadReq :: String -> Int -> Bool -> RME -> PredCall
queryAsyncReadReq name idxNum isWrite regMap =
  createPredCall name (T.Bit (log2_up idxNum)) preds calls
  -- PredCall (T.CABool T.Or preds) (T.orKind (T.Bit $ log2_up idxNum) calls)
  where
    (preds, calls) = query regMap
    query (T.VarRME v) =
      let count = async_read_counters v !!! name in
        ([T.Var (T.SyntaxKind T.Bool) $ T.unsafeCoerce (name ++ "#_enable", Just count)], [T.Var (T.SyntaxKind (T.Bit (log2_up idxNum))) $ T.unsafeCoerce (name ++ "#_argument", Just count)])
    query (T.UpdRegRME r pred k val regMap') = query regMap'
    query (T.WriteRME idxNum num writePort dataArray idx dataK val mask pred writeMap readMap arr) =
      query (if isWrite then writeMap else readMap)
    query (T.ReadReqRME idxNum num readReq readReg dataArray idx dataK isAddr pred writeMap readMap arr) =
      query (if isWrite then writeMap else readMap)
    query (T.ReadRespRME idxNum num readResp readReg dataArray dataK isAddr readMap) =
      query readMap
    query (T.AsyncReadRME idxNum num readPort dataArray idx pred k readMap) =
      let (restPred, restAddr) = query readMap in
        if readPort == name
        then (pred : restPred, T.predPack (T.Bit (log2_up idxNum)) pred idx : restAddr)
        else (restPred, restAddr)
    query (T.CompactRME regMap) =
      query regMap

querySyncReadReq :: String -> Int -> Bool -> RME -> PredCall
querySyncReadReq name idxNum isWrite regMap =
  createPredCall name (T.Bit (log2_up idxNum)) preds calls
  -- PredCall (T.CABool T.Or preds) (T.orKind (T.Bit $ log2_up idxNum) calls)
  where
    (preds, calls) = query regMap
    query (T.VarRME v) =
      let count = (case isAddr_read_req_counters v H.!? name of
                      Just c -> c
                      Nothing -> not_isAddr_read_req_counters v !!! name) in
          ([T.Var (T.SyntaxKind T.Bool) $ T.unsafeCoerce (name ++ "#_enable", Just count)], [T.Var (T.SyntaxKind (T.Bit (log2_up idxNum))) $ T.unsafeCoerce (name ++ "#_argument", Just count)])
    query (T.UpdRegRME r pred k val regMap') = query regMap'
    query (T.WriteRME idxNum num writePort dataArray idx dataK val mask pred writeMap readMap arr) =
      query (if isWrite then writeMap else readMap)
    query (T.ReadReqRME idxNum num readReq readReg dataArray idx dataK isAddr pred writeMap readMap arr) =
      let (restPred, restAddr) = query (if isWrite then writeMap else readMap) in
        if readReq == name
        then (pred : restPred, T.predPack (T.Bit (log2_up idxNum)) pred idx : restAddr)
        else (restPred, restAddr)
    query (T.ReadRespRME idxNum num readResp readReg dataArray dataK isAddr readMap) =
      query readMap
    query (T.AsyncReadRME idxNum num readPort dataArray idx pred k readMap) =
      query readMap
    query (T.CompactRME regMap) =
      query regMap

queryIsAddrRegWrite :: String -> String -> Int -> RME -> T.RtlExpr'
queryIsAddrRegWrite name readReqName idxNum regMap = T.ITE (T.SyntaxKind (T.Bit (log2_up idxNum))) (pred_val readCall) (call_val readCall) regVal
  where
    readCall = querySyncReadReq readReqName idxNum True regMap
    regVal = T.Var (T.SyntaxKind (T.Bit (log2_up idxNum))) (T.unsafeCoerce (name, Nothing))

queryNotIsAddrRegWrite :: String -> String -> Int -> Int -> T.Kind -> Bool -> RME -> T.RtlExpr'
queryNotIsAddrRegWrite writeName readReqName idxNum num k isMask regMap = pointwise
  where
    readCall = querySyncReadReq readReqName idxNum True regMap
    writeCall = queryRfWrite writeName idxNum num k isMask True regMap
    pointwise = T.pointwiseIntersection idxNum num k isMask (pred_val readCall) (call_val readCall) (pred_val writeCall) (T.unsafeCoerce $ call_val writeCall)

queryAsyncReadResp :: String -> String -> Int -> Int -> T.Kind -> Bool -> RME -> T.RtlExpr'
queryAsyncReadResp name writeName idxNum num k isMask regMap =
  T.pointwiseBypass num k pointwise respVal
  where
    respVal = (T.Var (T.SyntaxKind (T.Array num k)) (T.unsafeCoerce (name ++ "#_return", Nothing)))
    readCall = queryAsyncReadReq name idxNum False regMap
    writeCall = queryRfWrite writeName idxNum num k isMask False regMap
    pointwise = T.pointwiseIntersection idxNum num k isMask (pred_val readCall) (call_val readCall) (pred_val writeCall) (T.unsafeCoerce $ call_val writeCall)

queryIsAddrReadResp :: String -> String -> String -> Int -> Int -> T.Kind -> Bool -> RME -> T.RtlExpr'
queryIsAddrReadResp name writeName regName idxNum num k isMask regMap =
  T.pointwiseBypass num k pointwise respVal
  where
    respVal = T.Var (T.SyntaxKind (T.Array num k)) (T.unsafeCoerce (name ++ "#_return", Nothing))
    readAddr = T.Var (T.SyntaxKind (T.Array num k)) (T.unsafeCoerce (regName, Nothing))
    writeCall = queryRfWrite writeName idxNum num k isMask False regMap
    pointwise = T.pointwiseIntersection idxNum num k isMask (T.Const T.Bool (T.ConstBool True)) readAddr (pred_val writeCall) (T.unsafeCoerce $ call_val writeCall)

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

write_count :: String -> State ExprState Int
write_count r = do
  s <- get
  let rmc = regmap_counters s
  let rc = write_counters rmc
  let n = rc !!! r
  put $ s { regmap_counters = rmc { write_counters = H.insert r (n+1) rc } }
  return (n+1)

async_read_count :: String -> State ExprState Int
async_read_count r = do
  s <- get
  let rmc = regmap_counters s
  let rc = async_read_counters rmc
  let n = rc !!! r
  put $ s { regmap_counters = rmc { async_read_counters = H.insert r (n+1) rc } }
  return (n+1)

isAddr_read_req_count :: String -> State ExprState Int
isAddr_read_req_count r = do
  s <- get
  let rmc = regmap_counters s
  let rc = isAddr_read_req_counters rmc
  let n = rc !!! r
  put $ s { regmap_counters = rmc { isAddr_read_req_counters = H.insert r (n+1) rc } }
  return (n+1)

isAddr_read_reg_count :: String -> State ExprState Int
isAddr_read_reg_count r = do
  s <- get
  let rmc = regmap_counters s
  let rc = isAddr_read_reg_counters rmc
  let n = rc !!! r
  put $ s { regmap_counters = rmc { isAddr_read_reg_counters = H.insert r (n+1) rc } }
  return (n+1)
  
not_isAddr_read_req_count :: String -> State ExprState Int
not_isAddr_read_req_count r = do
  s <- get
  let rmc = regmap_counters s
  let rc = not_isAddr_read_req_counters rmc
  let n = rc !!! r
  put $ s { regmap_counters = rmc { not_isAddr_read_req_counters = H.insert r (n+1) rc } }
  return (n+1)

not_isAddr_read_reg_count :: String -> State ExprState Int
not_isAddr_read_reg_count r = do
  s <- get
  let rmc = regmap_counters s
  let rc = not_isAddr_read_reg_counters rmc
  let n = rc !!! r
  put $ s { regmap_counters = rmc { not_isAddr_read_reg_counters = H.insert r (n+1) rc } }
  return (n+1)

do_reg :: String -> T.FullKind -> RME -> State ExprState [(T.VarType, T.RtlExpr')]
do_reg r k m = case queryReg r k True m of
  T.Var _ _ -> return []
  e -> do
    i <- reg_count r
    return [((r, Just i),e)]

do_regs :: RME -> State ExprState [(T.VarType, T.RtlExpr')]
do_regs m = do
  s <- get
  monad_concat $ map (\(Register r k) -> do_reg r k m) (all_regs s)

do_write :: String -> Int -> Int -> T.Kind -> Bool -> RME -> State ExprState [(T.VarType, T.RtlExpr')]
do_write writeName idxNum num k isMask regMap = case queryRfWrite writeName idxNum num k isMask True regMap of
  PredCall (T.Var _ _) (T.Var _ _) -> return []
  PredCall e1 e2 -> do
    i <- write_count writeName
    return [((writeName ++ "#_enable", Just i), e1), ((writeName ++ "#_argument", Just i), e2)]

all_writes :: ExprState -> [(String, Int, Int, T.Kind, Bool)]
all_writes s =
     (map (\(Async c _) -> (commonWrite c, commonIdxNum c, commonNum c, commonData c, commonIsWrMask c)) $ all_asyncs s)
  ++ (map (\(Sync c _) ->(commonWrite c, commonIdxNum c, commonNum c, commonData c, commonIsWrMask c)) $ (all_isAddrs s ++ all_not_isAddrs s))

do_writes :: RME -> State ExprState [(T.VarType, T.RtlExpr')]
do_writes m = do
  s <- get
  monad_concat $ map (\(r, idxNum, num, k, isMask) -> do_write r idxNum num k isMask m)
    (all_writes s)

do_async_read :: String -> Int -> RME -> State ExprState [(T.VarType, T.RtlExpr')]
do_async_read name idxNum regMap = case queryAsyncReadReq name idxNum True regMap of
  PredCall (T.Var _ _) (T.Var _ _) -> return []
  PredCall e1 e2 -> do
    i <- async_read_count name
    return [((name ++ "#_enable", Just i), e1), ((name ++ "#_argument", Just i), e2)]

do_async_reads :: RME -> State ExprState [(T.VarType, T.RtlExpr')]
do_async_reads m = do
  s <- get
  monad_concat $ concatMap (\(Async common names) -> map (\name -> do_async_read name (commonIdxNum common) m) names) $ all_asyncs s

do_isAddr_read_req :: String -> Int -> RME -> State ExprState [(T.VarType, T.RtlExpr')]
do_isAddr_read_req name idxNum regMap = case querySyncReadReq name idxNum True regMap of
  PredCall (T.Var _ _) (T.Var _ _) -> return []
  PredCall e1 e2 -> do
    i <- isAddr_read_req_count name
    return [((name ++ "#_enable", Just i),e1), ((name ++ "#_argument", Just i),e2)]

do_isAddr_read_reqs :: RME -> State ExprState [(T.VarType, T.RtlExpr')]
do_isAddr_read_reqs m = do
  s <- get
  monad_concat $ concatMap (\(Sync common reads) -> map (\(T.Build_SyncRead r _ _) -> do_isAddr_read_req r (commonIdxNum common) m) reads) $ all_isAddrs s

do_isAddr_read_reg :: String -> String -> Int -> RME -> State ExprState [(T.VarType, T.RtlExpr')]
do_isAddr_read_reg name readReqName idxNum regMap = case queryIsAddrRegWrite name readReqName idxNum regMap of
  T.Var _ _ -> return []
  e -> do
    i <- isAddr_read_reg_count name
    return [((name, Just i), e)]

do_isAddr_read_regs :: RME -> State ExprState [(T.VarType, T.RtlExpr')]
do_isAddr_read_regs m = do
  s <- get
  monad_concat $ concatMap (\(Sync common reads) -> map (\(T.Build_SyncRead readReqName _ r) -> do_isAddr_read_reg r readReqName (commonIdxNum common) m) reads) $ all_isAddrs s

do_not_isAddr_read_req :: String -> Int -> RME -> State ExprState [(T.VarType, T.RtlExpr')]
do_not_isAddr_read_req name idxNum regMap = case querySyncReadReq name idxNum True regMap of
  PredCall (T.Var _ _) (T.Var _ _) -> return []
  PredCall e1 e2 -> do
    i <- not_isAddr_read_req_count name
    return [((name ++ "#_enable", Just i),e1), ((name ++ "#_argument", Just i),e2)]

do_not_isAddr_read_reqs :: RME -> State ExprState [(T.VarType, T.RtlExpr')]
do_not_isAddr_read_reqs m = do
  s <- get
  monad_concat $ concatMap (\(Sync common reads) -> map (\(T.Build_SyncRead r _ _) -> do_not_isAddr_read_req r (commonIdxNum common) m) reads) $ all_not_isAddrs s

do_not_isAddr_read_reg :: String -> String -> Int -> Int -> T.Kind -> Bool -> RME -> State ExprState [(T.VarType, T.RtlExpr')]
do_not_isAddr_read_reg writeName readReqName idxNum num k isMask regMap = case queryNotIsAddrRegWrite writeName readReqName idxNum num k isMask regMap of
  T.Var _ _ -> return []
  e -> do
    i <- not_isAddr_read_req_count readReqName
    return [((readReqName, Just i), e)]

do_not_isAddr_read_regs :: RME -> State ExprState [(T.VarType, T.RtlExpr')]
do_not_isAddr_read_regs m = do
  s <- get
  monad_concat $ concatMap (\(Sync common reads) -> map (\(T.Build_SyncRead reqName _ _) ->
    do_not_isAddr_read_reg (commonWrite common) reqName (commonIdxNum common) (commonNum common) (commonData common) (commonIsWrMask common) m) reads) $ all_not_isAddrs s

get_all_upds :: RME -> State ExprState [(T.VarType, T.RtlExpr')]
get_all_upds m = do
  assigns1 <- do_regs m
  assigns2 <- do_writes m
  assigns3 <- do_async_reads m
  assigns4 <- do_isAddr_read_reqs m
  assigns5 <- do_isAddr_read_regs m
  assigns6 <- do_not_isAddr_read_reqs m
  assigns7 <- do_not_isAddr_read_regs m
  return $ assigns1 ++ assigns2 ++ assigns3 ++ assigns4 ++ assigns5 ++ assigns6 ++ assigns7

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
    assign_exprs = (tmp_var j, queryReg r k False regMap) : assign_exprs y
  }

ppCAS (T.CompRet_simple _ retVal regMap) = do
  return $ VerilogExprs {
    assign_exprs = []
    , if_begin_end_exprs = []
    , return_expr = retVal
    , return_maps = regMap
  }

ppCAS (T.CompLetFull_simple _  a _ cont) = do
  (VerilogExprs assigns_a if_begin_ends_a ret_a map_a) <- ppCAS a
  j <- let_count
  assigns <- get_all_upds map_a
  s <- get
  y <- ppCAS (cont (tmp_var j) $ regmap_counters s)
  return $ y {
    assign_exprs = assigns_a ++ (tmp_var j, ret_a) : assigns ++ assign_exprs y
    , if_begin_end_exprs = if_begin_ends_a ++ if_begin_end_exprs y
  }

ppCAS (T.CompAsyncRead_simple idxNum num readPort dataArray idx pred k readMap _ cont) = do
  j <- let_count
  y <- ppCAS (cont $ tmp_var j)
  a <- async_of_readName readPort
  return $ y {
    assign_exprs = (tmp_var j, queryAsyncReadResp readPort (commonWrite $ asyncCommon a) idxNum num k (commonIsWrMask $ asyncCommon a) readMap) : assign_exprs y
  }

ppCAS (T.CompSyncReadRes_simple idxNum num readResp readReg dataArray k True readMap _ cont) = do
  j <- let_count
  y <- ppCAS (cont $ tmp_var j)
  sy <- sync_of_readResp readResp
  return $ y {
    assign_exprs = (tmp_var j, queryIsAddrReadResp readResp (commonWrite $ syncCommon sy) readReg idxNum num k (commonIsWrMask $ syncCommon sy) readMap) : assign_exprs y
  }

ppCAS (T.CompSyncReadRes_simple idxNum num readResp readReg dataArray k False readMap _ cont) = do
  j <- let_count
  y <- ppCAS (cont $ tmp_var j)
  return $ y {
    assign_exprs = (tmp_var j, queryNotIsAddrReadResp readResp readReg num k) : assign_exprs y
  }

ppCAS (T.CompWrite_simple idxNum k writePort dataArray readMap _ cont) = do
  j <- let_count
  y <- ppCAS (cont $ tmp_var j)
  return $ y {
    assign_exprs = (tmp_var j, T.Const (T.Bit 0) $ T.getDefaultConst (T.Bit 0)) : assign_exprs y
  }

ppCAS (T.CompSyncReadReq_simple idxNum num k readReq readReg dataArray isAddr readMap _ cont) = do
  j <- let_count
  y <- ppCAS (cont $ tmp_var j)
  return $ y {
    assign_exprs = (tmp_var j, T.Const (T.Bit 0) $ T.getDefaultConst (T.Bit 0)) : assign_exprs y
  }

get_final_assigns :: ExprState -> [T.RegFileBase] -> [(T.VarType, T.RtlExpr')]
get_final_assigns s rfbs = let (_,isAddrs,notIsAddrs) = process_rfbs rfbs in

  -- regular regs
     (map (\(Register r k) -> ((r,Nothing), T.Var k $ T.unsafeCoerce (r, reg_counters (regmap_counters s) !!! r))) $ all_regs s)

  -- isAddr shadow regs
  ++ (map (\(Register r k) -> ((r,Nothing), T.Var k $ T.unsafeCoerce (r, isAddr_read_reg_counters (regmap_counters s) !!! r))) $ all_isAddr_shadows isAddrs)

  -- notIsAddr shadow regs
  ++ (map (\(Register r k) -> ((r,Nothing), T.Var k $ T.unsafeCoerce (r, not_isAddr_read_reg_counters (regmap_counters s) !!! r))) $ all_not_isAddr_shadows isAddrs)

 -- TODO: also include shadowregs

get_final_meth_assigns :: T.BaseModule -> ExprState -> [(T.VarType, T.RtlExpr')]
get_final_meth_assigns basemod s = do
  (f,(argk,_)) <- get_normal_meth_calls_with_sign $ T.Base basemod
  let n = (meth_counters s) !!! f
  [((f ++ "#_enable",Nothing), T.Var (T.SyntaxKind T.Bool) $ T.unsafeCoerce (f ++ "#_enable", Just n)),((f ++ "#_argument",Nothing), T.Var (T.SyntaxKind argk) $ T.unsafeCoerce (f ++ "#_argument", Just n))] 

en_arg_final :: String -> T.Kind -> H.Map String Int -> [(T.VarType, T.RtlExpr')]
en_arg_final f argk counters = let n = counters !!! f in
  [   ((f ++ "#_enable",Nothing), T.Var (T.SyntaxKind T.Bool) $ T.unsafeCoerce (f ++ "#_enable", Just n))
    , ((f ++ "#_argument",Nothing), T.Var (T.SyntaxKind argk) $ T.unsafeCoerce (f ++ "#_argument", Just n))
  ]

get_final_rfmeth_assigns :: [T.RegFileBase] -> ExprState -> [(T.VarType, T.RtlExpr')]
get_final_rfmeth_assigns rfbs s = let (asyncs,isAddrs,notIsAddrs) = process_rfbs rfbs in

  --writes
     concatMap (\(write,argk) -> en_arg_final write argk $ write_counters $ regmap_counters s) (get_write_meths_with_arg rfbs)

  --async reads
  ++ concatMap (\(read,argk) -> en_arg_final read argk $ async_read_counters $ regmap_counters s) (get_async_reads_with_arg asyncs)

  --isAddr readreq
  ++ concatMap (\(readRq,argk) -> en_arg_final readRq argk $ isAddr_read_req_counters $ regmap_counters s) (get_sync_readReqs_with_arg isAddrs)
 

all_verilog :: ModInput -> (VerilogExprs, [(T.VarType, T.RtlExpr')])
all_verilog input@(strs,rfbs,basemod,cas) =
  let (vexprs,final_state) = runState (ppCAS $ cas) (init_state $ get_premodinput input) in
  let final_assigns = get_final_assigns final_state rfbs in
  let final_meth_assigns = get_final_meth_assigns basemod final_state in
  let final_rfmeth_assigns = get_final_rfmeth_assigns rfbs final_state in
    (vexprs { assign_exprs = (all_initialize input) ++ assign_exprs vexprs ++ final_meth_assigns ++ final_rfmeth_assigns }, final_assigns)

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

mkInits :: ModInput -> [(T.VarType, (T.FullKind,T.RegInitValT))]
mkInits (strs,rfbs,basemod,cas) = let (_,isAddrs,notIsAddrs) = process_rfbs rfbs in

  --regular inits
     map (\(r,p) -> ((r,Nothing),p)) (T.getRegisters basemod)

  --isAddr shadow regs
  ++ (map (\(Register r k) -> ((r,Nothing),(k,Nothing))) $ all_isAddr_shadows isAddrs)

  --notIsAddr shadow regs
  ++ (map (\(Register r k) -> ((r,Nothing),(k, Just $ T.getDefaultConstFullKind k ))) $ all_not_isAddr_shadows notIsAddrs)


mkRtlMod :: ModInput -> T.RtlModule
mkRtlMod input@(strs,rfbs,basemod,cas) =
  let (vexprs,fin_assigns) = all_verilog input in
                  T.Build_RtlModule
  {- hiddenWires -} (concatMap (\f -> [(f ++ "#_enable",Nothing), (f ++ "#_return",Nothing), (f ++ "#_argument",Nothing)]) strs)
  {- regFiles    -} rfbs
  {- inputs      -} (map (\(f,(_,k)) -> ((f ++ "#_return",Nothing),k)) $ T.getCallsWithSignPerMod $ T.Base basemod)
  {- outputs     -} (concatMap (\(f,(k,_)) -> [((f ++ "#_enable",Nothing), T.Bool), ((f ++ "#_argument",Nothing),k)]) $ T.getCallsWithSignPerMod $ T.Base basemod)
  {- regInits    -} (mkInits input)
  {- regWrites   -} (map (\(v,e) -> (v,(kind_of_expr e,e))) $ fin_assigns)
  {- wires       -} (map (\(v,e) -> (v,(kind_of_expr e,e))) $ assign_exprs vexprs)
  {- sys         -} (if_begin_end_exprs vexprs)

mkRtlFull ::  ([String], ([T.RegFileBase], T.BaseModule)) -> T.RtlModule
mkRtlFull (hides, (rfs, bm)) = mkRtlMod (hides, rfs, bm, T.coq_CAS_RulesRf (regmap_counters $ init_state (rfs, bm)) (T.getRules bm) rfs)

-}

mkRtlFull ::  ([String], ([T.RegFileBase], T.BaseModule)) -> T.RtlModule
mkRtlFull m = T.getRtl m

main :: IO()
main = putStrLn $ ppTopModule $ mkRtlFull T.rtlMod

