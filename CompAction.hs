module CompAction where

import qualified Target as T
import Data.List
import Data.Char
import Control.Monad.State.Lazy
import qualified Data.Map.Lazy as H
import Debug.Trace
import Numeric

log2_up :: Int -> Int
log2_up = ceiling . (logBase 2) . fromIntegral

data CommonInfo =
  CommonInfo
  { commonIsWrMask :: Bool
  , commonNum :: Int
  , commonDataArray :: String
  , commonWrite :: String
  , commonIdxNum :: Int
  , commonInit :: T.RegFileInitT }
  
data Async =
  Async
  { asyncCommon :: CommonInfo
  , asyncNames :: [String] }

data Sync =
  Sync
  { isAddrCommon :: CommonInfo
  , isAddrNames :: [T.SyncRead] }

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
  , not_isAddr_read_reg_counters :: H.Map String Int }

data ExprState = ExprState
  { let_counter :: Int
  , regmap_counters :: RegMapTy
  , meth_counters :: H.Map String Int
  , all_regs :: [Register]
  , all_asyncs :: [Async]
  , all_isAddrs :: [Sync]
  , all_not_isAddrs :: [Sync] }

data PredCall =
  PredCall
  { pred_val :: T.RtlExpr'
  , call_val :: T.RtlExpr' }

queryReg :: String -> T.FullKind -> Bool -> T.RME_simple T.Coq_rtl_ty RegMapTy -> T.RtlExpr
queryReg name k isWrite regMap =
  query regMap
  where
    query (T.VarRME v) = T.Var k $ T.unsafeCoerce (name, Just $ reg_counters v H.! name)
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

queryWrite :: String -> Int -> Int -> T.Kind -> Bool -> Bool -> T.RME_simple T.Coq_rtl_ty RegMapTy -> PredCall
queryWrite name idxNum num k isMask isWrite regMap =
  PredCall (T.CABool T.Or preds) (T.or_kind writeType calls)
  where
    writeType = if isMask then T.coq_WriteRqMask (log2_up idxNum) num k else T.coq_WriteRq (log2_up idxNum) (T.Array num k)
    addrSize = log2_up idxNum
    (preds, calls) = query regMap
    query (T.VarRME v) =
      let count = async_read_counters v H.! name in
        ([T.Var (T.SyntaxKind T.Bool) $ T.unsafeCoerce (name ++ "#_enable", Just count)], [T.Var (T.SyntaxKind writeType) $ T.unsafeCoerce (name ++ "#_argument", Just count)])
    query (T.UpdRegRME r pred k val regMap') = query regMap'
    query (T.WriteRME idxNum num writePort dataArray idx dataK val mask pred writeMap readMap arr) =
      let (restPred, restCall) = query (if isWrite then writeMap else readMap) in
        if writePort == name
        then (pred : restPred, T.pred_pack (T.Bit $ T.size writeType) pred (case mask of
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

queryAsyncRead :: String -> Int -> Bool -> T.RME_simple T.Coq_rtl_ty RegMapTy -> PredCall
queryAsyncRead name idxNum isWrite regMap =
  PredCall (T.CABool T.Or preds) (T.or_kind (T.Bit $ log2_up idxNum) calls)
  where
    (preds, calls) = query regMap
    query (T.VarRME v) =
      let count = async_read_counters v H.! name in
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
        then (pred : restPred, T.pred_pack (T.Bit (log2_up idxNum)) pred idx : restAddr)
        else (restPred, restAddr)
    query (T.CompactRME regMap) =
      query regMap

querySyncRead :: String -> Int -> Bool -> T.RME_simple T.Coq_rtl_ty RegMapTy -> PredCall
querySyncRead name idxNum isWrite regMap =
  PredCall (T.CABool T.Or preds) (T.or_kind (T.Bit $ log2_up idxNum) calls)
  where
    (preds, calls) = query regMap
    query (T.VarRME v) =
      let count = async_read_counters v H.! name in
        ([T.Var (T.SyntaxKind T.Bool) $ T.unsafeCoerce (name ++ "#_enable", Just count)], [T.Var (T.SyntaxKind (T.Bit (log2_up idxNum))) $ T.unsafeCoerce (name ++ "#_argument", Just count)])
    query (T.UpdRegRME r pred k val regMap') = query regMap'
    query (T.WriteRME idxNum num writePort dataArray idx dataK val mask pred writeMap readMap arr) =
      query (if isWrite then writeMap else readMap)
    query (T.ReadReqRME idxNum num readReq readReg dataArray idx dataK isAddr pred writeMap readMap arr) =
      let (restPred, restAddr) = query (if isWrite then writeMap else readMap) in
        if readReq == name
        then (pred : restPred, T.pred_pack (T.Bit (log2_up idxNum)) pred idx : restAddr)
        else (restPred, restAddr)
    query (T.ReadRespRME idxNum num readResp readReg dataArray dataK isAddr readMap) =
      query readMap
    query (T.AsyncReadRME idxNum num readPort dataArray idx pred k readMap) =
      query readMap
    query (T.CompactRME regMap) =
      query regMap

queryAsyncReadResp :: String -> String -> Int -> Int -> T.Kind -> Bool -> T.RME_simple T.Coq_rtl_ty RegMapTy -> T.RtlExpr'
queryAsyncReadResp name writeName idxNum num k isMask regMap =
  T.pointwiseIntersection idxNum num k isMask (call_val readcall) respVal (pred_val writecall) (T.unsafeCoerce $ call_val writecall)
  where
    respVal = (T.Var (T.SyntaxKind (T.Array num k)) (T.unsafeCoerce (name ++ "#_return", Nothing)))
    readcall = queryAsyncRead name idxNum False regMap
    writecall = queryWrite writeName idxNum num k isMask False regMap

queryIsAddrReadResp :: String -> String -> String -> Int -> Int -> T.Kind -> Bool -> T.RME_simple T.Coq_rtl_ty RegMapTy -> T.RtlExpr'
queryIsAddrReadResp name writeName regName idxNum num k isMask regMap =
  T.pointwiseIntersection idxNum num k isMask readAddr respVal (pred_val writecall) (T.unsafeCoerce $ call_val writecall)
  where
    respVal = (T.Var (T.SyntaxKind (T.Array num k)) (T.unsafeCoerce (name ++ "#_return", Nothing)))
    readAddr = T.Var (T.SyntaxKind (T.Array num k)) (T.unsafeCoerce (regName, Nothing))
    writecall = queryWrite writeName idxNum num k isMask False regMap
