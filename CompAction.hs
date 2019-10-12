{-# OPTIONS_GHC -XStandaloneDeriving #-}

module CompAction where

import qualified Target as T
import Data.List
import Data.Char
import Control.Monad.State.Lazy
import qualified Data.Map.Lazy as H
import Debug.Trace
import Numeric

type Name = String

data RegMapTy =
  RegMapTy
  { reg_counters :: H.Map Name Int
  , async_read_counters :: H.Map Name Int
  , async_write_counters :: H.Map Name Int
  , isAddr_read_req_counters :: H.Map Name Int
  , isAddr_write_counters :: H.Map Name Int
  , isAddr_read_reg_counters :: H.Map Name Int
  , not_isAddr_read_req_counters :: H.Map Name Int
  , not_isAddr_write_counters :: H.Map Name Int
  , not_isAddr_read_reg_counters :: H.Map Name Int }

data CommonInfo =
  CommonInfo
  { common_IdxNum :: Int
  , common_Num :: Int
  , common_dataArray :: String
  , common_write :: String
  , common_Kind :: Kind
  , common_mask :: Bool
  , common_init :: T.RegFileInitT }


--     Record RegFileBase := { rfIsWrMask : bool ;
--                         rfNum: nat ;
--                         rfDataArray: string ;
--                         rfRead: RegFileReaders ;
--                         rfWrite: string ;
--                         rfIdxNum: nat ;
--                         rfData: Kind ;
--                         rfInit: RegFileInitT rfIdxNum rfData }.
                       


-- data AsyncInfo =
--   AsyncInfo
--   { 
  

data ExprState = ExprState {
    let_counter :: Int
  , regmap_counters :: RegMapTy
  , meth_counters :: H.Map Name Int
  , all_regs :: [(Name,T.FullKind)]
  , all_asyncs :: [(Name,[Name],Bool)]
  , all_isAddrs :: [(Name,[Name,Name,Name],Bool)]
  , all_not_isAddrs :: [(Name,[Name,Name,Name],Bool)]
}

{-
data ReadReqPort = ReadReqPort {
    rd_req_pred :: T.RtlExpr
  , rd_req_addr :: T.RtlExpr
}

data WritePort = WritePort {
    wr_pred :: T.RtlExpr
  , wr_addr :: T.RtlExpr
  , wr_mask :: Maybe T.RtlExpr
  , wr_data :: T.RtlExpr
}



has_mask :: Name -> Bool
has_mask dataArray = undefined
{- we need some global association between the dataArray names and whether or not they 
   have a mask.  Probably a lookup on getregfiles followed by accessing iswrmask or something
-}


var :: T.FullKind -> Name -> Int -> T.RtlExpr'
var k n i = T.Var k $ T.unsafeCoerce (n, Just i)

var' :: T.FullKind -> Name -> T.RtlExpr'
var' k n = T.Var k $ T.unsafeCoerce (n, Nothing)

writeMap_query_read :: T.FullKind -> Name -> RME -> ReadPort
writeMap_query_read k readPort m = case m of
  T.VarRME rmt -> let i = (async_read_counters rmt) H.! readPort in
    ReadPort {
        rd_pred = var k (readPort ++ "__pred__") i
      , rd_addr = var k (readPort ++ "__addr__") i
    }
  T.UpdReg _ _ _ _ m' -> writeMap_query_read k readPort m'
  T.UpdRegFile _ _ _ _ _ _ _ _ wm rm _ -> writeMap_query_read k readPort wm
  T.UpdReadReq _ _ _ _ _ _ _ _ wm rm _ -> writeMap_query_read k readPort wm
  T.AsyncRead idxNum num readPort' dataArray idx pred _ m' ->
    if readPort == readPort' then ReadPort {
          rd_pred = pred
        , rd_addr = idx
      } else writeMap_query_read k readPort m'
  T.CompactRME m' -> writeMap_query_read k readPort m'

writeMap_query_write :: T.FullKind -> Name -> RME -> WritePort
writeMap_query_write k dataArray m = case m of
  T.VarRME rmt -> let i = (write_counters rmt) H.! dataArray in
    WritePort {
        wr_pred = var k (dataArray ++ "__pred__") i
      , wr_addr = var k (dataArray ++ "__addr__") i
      , wr_mask = if has_mask dataArray then Just $ var k (dataArray ++ "__mask__") i else Nothing
      , wr_data = var k (dataArray ++ "__data__") i
    }
  T.UpdReg _ _ _ _ m' -> writeMap_query_write k dataArray m'
  T.UpdRegFile idxNum num dataArray' idx k val mask pred wm rm _ ->
    if dataArray == dataArray' then WritePort {
        wr_pred = pred
      , wr_addr = idx
      , wr_mask = mask
      , wr_data = val
    } else writeMap_query_write (T.SyntaxKind k) dataArray wm
  T.UpdReadReq _ _ _ _ _ _ _ _ wm rm _ -> writeMap_query_write k dataArray wm
  T.AsyncRead _ _ _ _ _ _ _ m' -> writeMap_query_write k dataArray m'
  T.CompactRME m' -> writeMap_query_write k dataArray m'

readMap_query_read :: T.FullKind -> Name -> RME -> ReadPort
readMap_query_read k readPort m = case m of
  T.VarRME rmt -> let i = (async_read_counters rmt) H.! readPort in
    ReadPort {
        rd_pred = var k (readPort ++ "__pred__") i
      , rd_addr = var k (readPort ++ "__addr__") i
    }
  T.UpdReg _ _ _ _ m' -> readMap_query_read k readPort m'
  T.UpdRegFile _ _ _ _ _ _ _ _ wm rm _ -> readMap_query_read k readPort rm
  T.UpdReadReq _ _ _ _ _ _ _ _ wm rm _ -> readMap_query_read k readPort rm
  T.AsyncRead idxNum num readPort' dataArray idx pred _ m' ->
    if readPort == readPort' then ReadPort {
          rd_pred = pred
        , rd_addr = idx
      } else readMap_query_read k readPort m'
  T.CompactRME m' -> readMap_query_read k readPort m'

readMap_query_write :: T.FullKind -> Name -> RME -> WritePort
readMap_query_write k dataArray m = case m of
  T.VarRME rmt -> let i = (write_counters rmt) H.! dataArray in
    WritePort {
        wr_pred = var k (dataArray ++ "__pred__") i
      , wr_addr = var k (dataArray ++ "__addr__") i
      , wr_mask = if has_mask dataArray then Just $ var k (dataArray ++ "__mask__") i else Nothing
      , wr_data = var k (dataArray ++ "__data__") i
    }
  T.UpdReg _ _ _ _ m' -> readMap_query_write k dataArray m'
  T.UpdRegFile idxNum num dataArray' idx k val mask pred wm rm _ ->
    if dataArray == dataArray' then WritePort {
        wr_pred = pred
      , wr_addr = idx
      , wr_mask = mask
      , wr_data = val
    } else readMap_query_write (T.SyntaxKind k) dataArray rm
  T.UpdReadReq _ _ _ _ _ _ _ _ wm rm _ -> readMap_query_write k dataArray rm
  T.AsyncRead _ _ _ _ _ _ _ m' -> readMap_query_write k dataArray m'
  T.CompactRME m' -> readMap_query_write k dataArray m'

get_range_ptwise :: (T.RtlExpr' -> T.RtlExpr') -> T.RtlExpr' -> Int -> T.RtlExpr'
get_range_ptwise f idx num = undefined
  {- should produce the array { f idx, f (idx+1), ..., f (idx+num-1) } -}

between :: T.RtlExpr' -> T.RtlExpr' -> T.RtlExpr' -> T.RtlExpr'
between = undefined -- the boolean expr e1 < e2 < e3

readmap_query_resp :: T.FullKind -> Int -> Name -> Name -> RME -> T.RtlExpr'
readmap_query_resp k num dataArray readPort m =
  let wp = readMap_query_write k dataArray m in
  let rd_idx = rd_addr $ readMap_query_read k readPort m in
  let wr_idx = wr_addr wp in
  let pred = wr_pred wp in
  let mask = wr_mask wp in
  let val = wr_data wp in
    get_range_ptwise (\i -> T.ITE k (between rd_idx i undefined) undefined undefined) wr_idx num
    {- 
       I didn't get these written yet but the logic involving being in the correct range,
       the mask, and the pred should go here
    -}

type RME = T.RME_simple T.Coq_rtl_ty RegMapTy

data VerilogExprs = VerilogExprs {
    assign_exprs :: [(Name, T.RtlExpr')]
  , if_begin_end_exprs :: [(T.RtlExpr', [T.SysT T.Coq_rtl_ty])]
  , return_expr :: T.RtlExpr'
  , return_maps :: RME
}

{- monadic accessors which both return the current count and increment it -}

get_regs :: State ExprState [(Name, T.FullKind)]
get_regs = do
  s <- get
  return $ all_regs s

get_asyncs :: State ExprState [(Name,Name)]
get_asyncs = do
  s <- get
  return $ all_asyncs s

get_isAddrs :: State ExprState [(Name,Name)]
get_isAddrs = do
  s <- get
  return $ all_isAddrs s

get_not_isAddrs :: State ExprState [(Name,Name)]
get_not_isAddrs = do
  s <- get
  return $ all_not_isAddrs s

let_count :: State ExprState Int
let_count = do
  s <- get
  let n = let_counter s
  put $ s { let_counter = n+1 }
  return n

meth_count :: Name -> State ExprState Int
meth_count f = do
  s <- get
  let n = meth_counters s H.! f
  put $ s { meth_counters = H.insert f (n+1) $ meth_counters s }
  return n

reg_count :: Name -> State ExprState Int
reg_count r = do
  s <- get
  let rmc = regmap_counters s
  let rc = reg_counters rmc
  let n = rc H.! r
  put $ s { regmap_counters = rmc { reg_counters = H.insert r (n+1) rc } }
  return n

async_count :: (Name,Name) -> State ExprState Int
async_count p = do
  s <- get
  let rmc = regmap_counters s
  let arc = async_counters rmc
  let n = arc H.! p
  put $ s { regmap_counters = rmc { async_counters = H.insert p (n+1) arc } }
  return n

isAddr_count :: Name -> State ExprState Int
isAddr_count r = do
  s <- get
  let rmc = regmap_counters s
  let sic = isAddr_counters rmc
  let n = sic H.! r
  put $ s { regmap_counters = rmc { isAddr_counters = H.insert r (n+1) sic } }
  return n

not_isAddr_count :: Name -> State ExprState Int
not_isAddr_count r = do
  s <- get
  let rmc = regmap_counters s
  let snc = not_isAddr_counters rmc
  let n = snc H.! r
  put $ s { regmap_counters = rmc { not_isAddr_counters = H.insert r (n+1) snc} }
  return n

data MapType = ReadMap | WriteMap deriving (Eq)

{- normal registers -}

query_reg :: MapType -> T.FullKind -> Name -> RME -> T.RtlExpr'
query_reg x k reg (T.VarRME rmt) = T.Var k $ T.unsafeCoerce (reg, Just $ (reg_counters rmt) H.! reg)
query_reg x k reg (T.UpdReg r pred _ val m) = if reg == r then T.ITE k pred val (query_reg x k reg m) else query_reg x k reg m
query_reg ReadMap k reg (T.UpdRegFile _ _ _ _ _ _ _ _ writeMap readMap _) = query_reg ReadMap k reg readMap
query_reg WriteMap k reg (T.UpdRegFile _ _ _ _ _ _ _ _ writeMap readMap _) = query_reg WriteMap k reg writeMap
query_reg ReadMap k reg (T.UpdReadReq _ _ _ _ _ _ _ _ writeMap readMap _) = query_reg ReadMap k reg readMap
query_reg WriteMap k reg (T.UpdReadReq _ _ _ _ _ _ _ _ writeMap readMap _) = query_reg WriteMap k reg writeMap
query_reg x k reg (T.CompactRME m) = query_reg x k reg m

do_reg_upd :: RME -> T.FullKind -> Name -> State ExprState [(Name, T.RtlExpr')]
do_reg_upd m k r = case query_reg WriteMap k r m of
  T.Var _ _ -> return []
  e -> do
    i <- reg_count r
    return [(r ++ "__" ++ show i,e)]

get_reg_upds :: RME -> State ExprState [(Name, T.RtlExpr')]
get_reg_upds m = do
  rs <- get_regs
  monad_concat $ map (\(r,k) -> do_reg_upd m k r) rs

monad_concat :: Monad m => [m [a]] -> m [a]
monad_concat ms = fmap concat $ sequence ms

-}
