{-# OPTIONS_GHC -XStandaloneDeriving -XFlexibleInstances #-}

import Target
import Data.List
import Data.List.Split
import Control.Monad.State.Strict
import qualified Data.HashMap.Strict as H

import Debug.Trace

deriving instance Show T
deriving instance Show Target.Word
deriving instance Show UniBoolOp
deriving instance Show CABoolOp
deriving instance Show UniBitOp
deriving instance Show CABitOp

deriving instance Eq T

ppDealSize0 :: Kind -> String -> String -> String
ppDealSize0 ty def str = if size ty == 0 then def else str

ppVecLen :: Int -> String
ppVecLen n = "[" ++ show (n-1) ++ ":0]"

finToInt :: T -> Int
finToInt (F1 _) = 0
finToInt (FS _ x) = Prelude.succ (finToInt x)

intToFin :: Int -> Int -> T
intToFin m 0 = F1 (m-1)
intToFin m n = FS (m-1) (intToFin (m-1) (n-1))

getFins :: Int -> [T]
getFins m = foldr (\n l -> intToFin m n : l) [] [0 .. (m-1)]

instance Show Kind where
  show Bool = "Bool"
  show (Bit n) = "Bit " ++ show n
  show (Array n k) = "Array " ++ show n ++ " " ++ show k
  show (Struct n fk fs) = "Struct {" ++ concatMap (\i -> show (fs i) ++ ": " ++ show (fk i) ++ "; ") (getFins n) ++ "}"

instance Show ConstT where
  show (ConstBool b) = "ConstBool " ++ show b
  show (ConstBit n w) = "ConstBit " ++ show n ++ " " ++ show w
  show (ConstStruct n fk fs fv) = "ConstStruct {" ++ concatMap (\i -> show (fs i) ++ ": " ++ show (fk i) ++ " = " ++ show (fv i) ++ "; ") (getFins n) ++ "}"
  show (ConstArray n k fv) = "ConstArray " ++ show n ++ " " ++ show k ++ "{" ++ concatMap (\i -> show (fv i) ++ "; ") (getFins n) ++ "}"


deriving instance Show BinBitOp

instance Show RtlExpr where
  show (RtlReadReg k s) = "RtlReadReg " ++ show k ++ " " ++ show s
  show (RtlReadWire k s) = "RtlReadWire" ++ show k ++ " " ++ show s
  show (RtlConst k c) = "RtlConst " ++ show k ++ " " ++ show c
  show (RtlUniBool op e) = "RtlUniBool " ++ show op ++ " " ++ show e
  show (RtlCABool op e) = "RtlCABool " ++ show op ++ " " ++ show e
  show (RtlUniBit _ _ op e) = "RtlUniBit " ++ show op ++ " " ++ show e
  show (RtlCABit _ op e) = "RtlCABit " ++ show op ++ " " ++ show e
  show (RtlBinBit _ _ _ op e1 e2) = "RtlCABool " ++ show op ++ " " ++ show e1 ++ " " ++ show e2
  show (RtlBinBitBool _ _ op e1 e2) = "RtlCABool " ++ show op ++ " " ++ show e1 ++ " " ++ show e2
  show (RtlITE k p e1 e2) = "RtlITE " ++ show k ++ " " ++ show p ++ " " ++ show e1 ++ " " ++ show e2
  show (RtlEq k e1 e2) = "RtlEq " ++ show k ++ " " ++ show e1 ++ " " ++ show e2
  show (RtlBuildStruct n fk fs fv) = "RtlBuildStruct " ++ show n ++ "{" ++ concatMap (\i -> show (fs i) ++ ": " ++ show (fk i) ++ " = " ++ show (fv i) ++ "; ") (getFins n) ++ "}"
  show (RtlBuildArray n k fv) = "RtlBuildArray " ++ show n ++ " " ++ show k ++ "{" ++ concatMap (\i -> show (fv i) ++ "; ") (getFins n) ++ "}"
  show (RtlReadStruct n fk fs e i) = "RtlReadStruct " ++ show n ++ "{" ++ concatMap (\i -> show (fs i) ++ ": " ++ show (fk i) ++ "; ") (getFins n) ++ "}" ++
                                     " " ++ show e ++ " " ++ show i
  show (RtlReadArray n k e i) = "RtlReadArray " ++ show n ++ " " ++ show k ++
                                " " ++ show e ++ " " ++ show i
  show (RtlReadArrayConst n k e i) = "RtlReadArrayConst " ++ show n ++ " " ++ show k ++
                                     " " ++ show e ++ " " ++ show i

deriving instance Show BitFormat
instance Show RtlSysT where
  show (RtlDispString s) = "RtlDispString " ++ show s
  show (RtlDispBool e f) = "RtlDispBool " ++ show e ++ " " ++ show f
  show (RtlDispBit _ e f) = "RtlDispBool " ++ show e ++ " " ++ show f
  show (RtlDispStruct n fk fs e ff) = "RtlDispStruct " ++ show e ++  "{" ++ concatMap (\i -> show (fs i) ++ ": " ++ show (fk i) ++ " = " ++ show (ff i) ++ "; ") (getFins n) ++ "}"
  show (RtlDispArray n k fv ff) = "RtlDispArray " ++ show n ++ " " ++ show k ++ " " ++ show fv ++ " " ++ show ff

deriving instance Show RtlModule

wordToList :: Target.Word -> [Bool]
wordToList WO = []
wordToList (WS b _ w) = b : wordToList w

ppTypeVec :: Kind -> Int -> (Kind, [Int])
ppTypeVec k@(Array i' k') i =
  let (k'', is) = ppTypeVec k' i'
  in (k', i : is)
ppTypeVec k i = (k, i : [])

ppTypeName :: Kind -> String
ppTypeName k =
  case ppTypeVec k 0 of
    (Struct _ _ _, _) -> "struct packed"
    (_, _) -> "logic"

ppDeclType :: String -> Kind -> String
ppDeclType s k = ppTypeName k ++ ppType k ++ " " ++ s

ppName :: String -> String
ppName s = intercalate "$" (Data.List.map (\x -> ppDottedName x) (splitOneOf "$#" s))
  {-
  if elem '.' s
  then intercalate "$" (case splitOneOf ".#" s of
                          x : y : xs -> x : y : xs
                          ys -> ys)
  else Data.List.map (\x -> case x of
                         '#' -> '$'
                         c -> c) s
-}



ppType :: Kind -> String
ppType Bool = ""
ppType (Bit i) = "[" ++ show (i-1) ++ ":0]"
  -- if i > 0
  -- then "[" ++ show (i-1) ++ ":0]"
  -- else ""
ppType v@(Array i k) =
  let (k', is) = ppTypeVec k i
  in case k' of
       Struct _ _ _ -> ppType k' ++ concatMap ppVecLen is
       _ -> concatMap ppVecLen is ++ ppType k'
ppType (Struct n fk fs) =
  "{" ++ concatMap (\i -> ppDealSize0 (fk i) "" (' ' : ppDeclType (ppName $ fs i) (fk i) ++ ";")) (getFins n) ++ "}"

ppDottedName :: String -> String
ppDottedName s =
  case splitOn "." s of
    x : y : nil -> y ++ "$" ++ x
    x : nil -> x


ppPrintVar :: (String, [Int]) -> String
ppPrintVar (s, vs) = ppName $ s ++ concatMap (\v -> '#' : show v) vs

ppWord :: [Bool] -> String
ppWord [] = []
ppWord (b : bs) = (if b then '1' else '0') : ppWord bs

ppConst :: ConstT -> String
ppConst (ConstBool b) = if b then "1'b1" else "1'b0"
ppConst (ConstBit sz w) = show sz ++ "\'b" ++ ppWord (reverse $ wordToList w)
ppConst (ConstArray n k fv) = '{' : intercalate ", " (Data.List.map ppConst (Data.List.map fv (getFins n))) ++ "}"
ppConst (ConstStruct n fk fs fv) = '{' : intercalate ", " (Data.List.map ppConst (Data.List.map fv (getFins n))) ++ "}"

ppRtlExpr :: String -> RtlExpr -> State (H.HashMap String (Int, Kind)) String
ppRtlExpr who e =
  case e of
    RtlReadReg k s -> return $ ppDealSize0 k "0" (ppName s)
    RtlReadWire k var -> return $ ppDealSize0 k "0" (ppPrintVar var)
    RtlConst k c -> return $ ppDealSize0 k "0" (ppConst c)
    RtlUniBool Neg e -> uniExpr "~" e
    RtlCABool And es -> listExpr "&" es "1'b1"
    RtlCABool Or es -> listExpr "|" es "1'b0"
    RtlCABool Xor es -> listExpr "^" es "1'b0"
    RtlUniBit _ _ (Inv _) e -> uniExpr "~" e
    RtlUniBit _ _ (UAnd _) e -> uniExpr "&" e
    RtlUniBit _ _ (UOr _) e -> uniExpr "|" e
    RtlUniBit _ _ (UXor _) e -> uniExpr "^" e
    RtlUniBit sz retSz (TruncLsb lsb msb) e -> createTrunc (Bit sz) e (retSz - 1) 0
    RtlUniBit sz retSz (TruncMsb lsb msb) e -> createTrunc (Bit sz) e (sz - 1) lsb
    RtlCABit n Add es -> listExpr "+" es (show n ++ "'b0")
    RtlCABit n Mul es -> listExpr "*" es (show n ++ "'b1")
    RtlCABit n Band es -> listExpr "&" es (show n ++ "'b" ++ replicate n '1')
    RtlCABit n Bor es -> listExpr "|" es (show n ++ "'b0")
    RtlCABit n Bxor es -> listExpr "^" es (show n ++ "'b0")
    RtlBinBit _ _ _ (Sub _) e1 e2 -> binExpr e1 "-" e2
    RtlBinBit _ _ _ (Div _) e1 e2 -> binExpr e1 "/" e2
    RtlBinBit _ _ _ (Rem _) e1 e2 -> binExpr e1 "%" e2
    RtlBinBit _ _ _ (Sll _ _) e1 e2 -> binExpr e1 "<<" e2
    RtlBinBit _ _ _ (Srl _ _) e1 e2 -> binExpr e1 ">>" e2
    RtlBinBit _ _ _ (Sra _ _) e1 e2 ->
      do
        x1 <- ppRtlExpr who e1
        x2 <- ppRtlExpr who e2
        return $ "($signed(" ++ x1 ++ ") >>> " ++ x2 ++ ")"
    RtlBinBit _ _ _ (Concat _ n) e1 e2 ->
      if n /= 0
      then
        do
          x1 <- ppRtlExpr who e1
          x2 <- ppRtlExpr who e2
          return $ '{' : x1 ++ ", " ++ x2 ++ "}"
      else
        do
          x1 <- ppRtlExpr who e1
          return x1
    RtlBinBitBool _ _ (_) e1 e2 -> binExpr e1 "<" e2
    RtlITE _ p e1 e2 -> triExpr p "?" e1 ":" e2
    RtlEq _ e1 e2 -> binExpr e1 "==" e2
    RtlReadStruct num fk fs e i ->
      do
        new <- optionAddToTrunc (Struct num fk fs) e
        return $ new ++ '.' : (fs i)
    RtlBuildStruct num fk fs es ->
      do
        strs <- mapM (ppRtlExpr who) (Data.List.map es (getFins num))
        return $ '{': intercalate ", " strs ++ "}"
    RtlReadArray n k vec idx ->
      do
        xidx <- ppRtlExpr who idx
        xvec <- ppRtlExpr who vec
        new <- optionAddToTrunc (Array n k) vec
        return $ new ++ '[' : xidx ++ "]"
    RtlReadArrayConst n k vec idx ->
      do
        let xidx = finToInt idx
        xvec <- ppRtlExpr who vec
        new <- optionAddToTrunc (Array n k) vec
        return $ new ++ '[' : show xidx ++ "]"
    RtlBuildArray n k fv ->
      do
        strs <- mapM (ppRtlExpr who) (reverse $ Data.List.map fv (getFins n))
        return $ '{': intercalate ", " strs ++ "}"
  where
    optionAddToTrunc :: Kind -> RtlExpr -> State (H.HashMap String (Int, Kind)) String
    optionAddToTrunc k e =
      case e of
        RtlReadReg k s -> return $ case k of
                                     Bit 0 -> "0"
                                     _ -> ppName s
        RtlReadWire k var -> return $ case k of
                                        Bit 0 -> "0"
                                        _ -> ppPrintVar var
        _ -> do
          x <- ppRtlExpr who e
          new <- addToTrunc k x
          return new
    createTrunc :: Kind -> RtlExpr -> Int -> Int -> State (H.HashMap String (Int, Kind)) String
    createTrunc k e msb lsb =
      do
        new <- optionAddToTrunc k e
        return $ new ++ '[' : show msb ++ ':' : show lsb ++ "]"
    addToTrunc :: Kind -> String -> State (H.HashMap String (Int, Kind)) String
    addToTrunc kind s =
      do
        x <- get
        case H.lookup s x of
          Just (pos, _) -> return $ "_trunc$" ++ who ++ "$" ++ show pos
          Nothing ->
            do
              put (H.insert s (H.size x, kind) x)
              return $ "_trunc$" ++ who ++ "$" ++ show (H.size x)
    uniExpr op e =
      do
        x <- ppRtlExpr who e
        return $ '(' : " " ++ op ++ " " ++ x ++ ")"
    listExpr' op es init =
      case es of
        e : es' -> do
                     x <- ppRtlExpr who e
                     xs <- listExpr' op es' init
                     return $ x ++ " " ++ op ++ " " ++ xs
        [] -> return init
    listExpr op es init =
      do
        xs <- listExpr' op es init
        return $ '(' : xs ++ ")"
    binExpr e1 op e2 =
      do
        x1 <- ppRtlExpr who e1
        x2 <- ppRtlExpr who e2
        return $ '(' : x1 ++ " " ++ op ++ " " ++ x2 ++ ")"
    triExpr e1 op1 e2 op2 e3 =
      do
        x1 <- ppRtlExpr who e1
        x2 <- ppRtlExpr who e2
        x3 <- ppRtlExpr who e3
        return $ '(' : x1 ++ " " ++ op1 ++ " " ++ x2 ++ " " ++ op2 ++ " " ++ x3 ++ ")"

ppRfInstance :: (((String, [(String, Bool)]), String), (((Int, Kind)), ConstT)) -> IO ()
ppRfInstance (((name, reads), write), ((idxType, dataType), _)) =
  do
    putStrLn $
      "  " ++ ppName name ++ " " ++
      ppName name ++ "$inst(.CLK(CLK), .RESET_N(RESET_N), " ++
      concatMap (\(read, _) ->
                   ("." ++ ppName read ++ "$_guard(" ++ ppName read ++ "$_guard), ") ++
                  ("." ++ ppName read ++ "$_enable(" ++ ppName read ++ "$_enable), ") ++
                  ("." ++ ppName read ++ "$_argument(" ++ ppName read ++ "$_argument), ") ++
                  ppDealSize0 dataType "" ("." ++ ppName read ++ "$_return(" ++ ppName read ++ "$_return), ")) reads ++
      ("." ++ ppName write ++ "$_guard(" ++ ppName write ++ "$_guard), ") ++
      ("." ++ ppName write ++ "$_enable(" ++ ppName write ++ "$_enable), ") ++
      ("." ++ ppName write ++ "$_argument(" ++ ppName write ++ "$_argument)") ++
      ");\n"
      

ppRfModule :: (((String, [(String, Bool)]), String), ((Int, Kind), ConstT)) -> IO ()
ppRfModule (((name, reads), write), ((idxType, dataType), init)) =
  do
    putStrLn $ "module " ++ ppName name ++ "("
    mapM (\(read, _) ->
            do
              putStrLn ("  output " ++ ppDeclType (ppName read ++ "$_guard") Bool ++ ",")
              putStrLn ("  input " ++ ppDeclType (ppName read ++ "$_enable") Bool ++ ",")
              putStrLn ("  input " ++ ppDeclType (ppName read ++ "$_argument") (Bit idxType) ++ ",")
              putStrLn (ppDealSize0 dataType "" ("  output " ++ ppDeclType (ppName read ++ "$_return") dataType ++ ","))) reads
    putStrLn ("  output " ++ ppDeclType (ppName write ++ "$_guard") Bool ++ ",")
    putStrLn ("  input " ++ ppDeclType (ppName write ++ "$_enable") Bool ++ ",")
    putStrLn ("  input " ++ ppDeclType (ppName write ++ "$_argument")
       (Struct 2 (\i -> if i == F1 1 then (Bit idxType) else if i == FS 1 (F1 0) then dataType else (Bit 0)) (\i -> if i == F1 1 then "addr" else if i == FS 1 (F1 0) then "data" else "")) ++ ",")
    putStrLn "  input logic CLK,"
    putStrLn "  input logic RESET_N"
    putStrLn ");"
      --putStrLn ("  " ++ ppDeclType (ppName name ++ "$_data") dataType ++ "[0:" ++ show (2^idxType - 1) ++ "];")
    putStrLn ("  " ++ ppDeclType (ppName name ++ "$_data") (Bit (Target.size dataType)) ++ "[0:" ++ show (2^idxType - 1) ++ "];")
    putStrLn "  initial begin"
      -- putStrLn ("    " ++ ppName name ++ "$_data = " ++ '\'' : ppConst init ++ ";")
    putStrLn ("    $readmemb(" ++ "\"" ++ ppName name ++ ".mem" ++ "\", " ++ ppName name ++ "$_data, 0, " ++ show (2^idxType - 1) ++ ");")
    putStrLn ("  end")
    mapM (\(read, bypass) ->
             putStrLn ("  assign " ++ ppName read ++ "$_guard = 1'b1;\n" ++
                       ppDealSize0 dataType "" ("  assign " ++ ppName read ++ "$_return = " ++
                                                if bypass
                                                then ppName write ++ "$_enable && " ++ ppName write ++ "$_argument.addr == " ++
                                                ppName read ++ "$_argument ? " ++ ppName write ++ "$_data : "
                                                else "" ++ ppDealSize0 dataType "0" (ppName name ++ "$_data[" ++ ppName read ++ "$_argument];")))) reads
    putStrLn ("  assign " ++ ppName write ++ "$_guard = 1'b1;)")
    putStrLn ("  always@(posedge CLK) begin")
    putStrLn ("    if(" ++ ppName write ++ "$_enable) begin")
    putStrLn (ppDealSize0 dataType "" ("      " ++ ppName name ++ "$_data[" ++ ppName write ++ "$_argument.addr] <= " ++ ppName write ++ "$_argument.data;"))
    putStrLn ("    end")
    putStrLn ("  end)")
    putStrLn "endmodule\n"

removeDups :: Eq a => [(a, b)] -> [(a, b)]
removeDups = nubBy (\(a, _) (b, _) -> a == b)

ppRtlInstance :: RtlModule -> IO ()
ppRtlInstance m@(Build_RtlModule regFs ins' outs' regInits' regWrites' assigns' sys') =
  do
    putStr "  _design _designInst(.CLK(CLK), .RESET_N(RESET_N)"
    mapM (\(nm, ty) -> putStrLn $ ppDealSize0 ty "" (", ." ++ ppPrintVar nm ++ '(' : ppPrintVar nm ++ ")")) (removeDups ins' ++ removeDups outs')
    putStr ");\n"

ppBitFormat :: BitFormat -> String
ppBitFormat Binary = "b"
ppBitFormat Decimal = "d"
ppBitFormat Hex = "x"

ppFullBitFormat :: FullBitFormat -> String
ppFullBitFormat (sz, f) = "%" ++ show sz ++ ppBitFormat f

ppRtlSys :: RtlSysT -> State (H.HashMap String (Int, Kind)) String
ppRtlSys (RtlDispString s) = return $ "        $write(\"" ++ s ++ "\");\n"
ppRtlSys (RtlDispBool e f) = do
  s <- ppRtlExpr "sys" e
  return $ "        $write(\"" ++ ppFullBitFormat f ++ "\", " ++ s ++ ");\n"
ppRtlSys (RtlDispBit _ e f) = do
  s <- ppRtlExpr "sys" e
  return $ "        $write(\"" ++ ppFullBitFormat f ++ "\", " ++ s ++ ");\n"
ppRtlSys (RtlDispStruct n fk fs fv ff) = do
  rest <- mapM (\i -> ppRtlExpr "sys" (RtlReadStruct n fk fs fv i)) (getFins n)
  return $ "        $write(\"{" ++ Data.List.concat (Data.List.map (\i -> fs i ++ ":=" ++ ppFullBitFormat (ff i) ++ "; ") (getFins n)) ++ "}\", " ++ Data.List.concat rest ++ ");\n"
ppRtlSys (RtlDispArray n k v f) = do
  rest <- mapM (\i -> ppRtlExpr "sys" (RtlReadArray n k v (RtlConst k (ConstBit (log2_up n) (natToWord (log2_up n) i))))) [0 .. (n-1)]
  return $ "        $write(\"[" ++ Data.List.concat (Data.List.map (\i -> show i ++ ":=" ++ ppFullBitFormat f ++ "; ") [0 .. (n-1)]) ++ "]\", " ++ Data.List.concat rest ++ ");\n"

ppRtlModule :: RtlModule -> IO ()
ppRtlModule m@(Build_RtlModule regFs ins' outs' regInits' regWrites' assigns' sys') =
  do
    putStrLn ("module _design(")
    mapM (\(nm, ty) -> putStrLn (ppDealSize0 ty "" ("  input " ++ ppDeclType (ppPrintVar nm) ty ++ ","))) ins
    putStrLn ""
    mapM (\(nm, ty) -> putStrLn (ppDealSize0 ty "" ("  output " ++ ppDeclType (ppPrintVar nm) ty ++ ","))) outs
    putStrLn ""
    putStrLn ("  input CLK,")
    putStrLn ("  input RESET_N")
    putStrLn (");")
    mapM (\(nm, (ty, init)) -> putStrLn (ppDealSize0 ty "" ("  " ++ ppDeclType (ppName nm) ty ++ ";\n"))) regInits
  
    mapM (\(nm, (ty, expr)) -> putStrLn (ppDealSize0 ty "" ("  " ++ ppDeclType (ppPrintVar nm) ty ++ ";"))) assigns
    putStrLn ""
  
    mapM (\(sexpr, (pos, ty)) -> putStrLn (ppDealSize0 ty "" ("  " ++ ppDeclType ("_trunc$wire$" ++ show pos) ty ++ ";"))) assignTruncs
    -- putStrLn ""
    -- mapM (\(sexpr, (pos, ty)) -> putStrLn (ppDealSize0 ty "" ("  " ++ ppDeclType ("_trunc$reg$" ++ show pos) ty ++ ";"))) regTruncs
    -- putStrLn ""
    -- mapM (\(sexpr, (pos, ty)) -> putStrLn (ppDealSize0 ty "" ("  " ++ ppDeclType ("_trunc$sys$" ++ show pos) ty ++ ";"))) sysTruncs
    -- putStrLn ""
  
    -- mapM (\(sexpr, (pos, ty)) -> putStrLn (ppDealSize0 ty "" ("  assign " ++ "_trunc$wire$" ++ show pos ++ " = " ++ sexpr ++ ";"))) assignTruncs
    -- putStrLn ""
    -- mapM (\(sexpr, (pos, ty)) -> putStrLn (ppDealSize0 ty "" ("  assign " ++ "_trunc$reg$" ++ show pos ++ " = " ++ sexpr ++ ";\n"))) regTruncs
    -- putStrLn ""
    -- mapM (\(sexpr, (pos, ty)) -> putStrLn (ppDealSize0 ty "" ("  assign " ++ "_trunc$sys$" ++ show pos ++ " = " ++ sexpr ++ ";\n"))) sysTruncs
    -- putStrLn ""
    
    -- mapM (\(nm, (ty, sexpr)) -> putStrLn (ppDealSize0 ty "" ("  assign " ++ ppPrintVar nm ++ " = " ++ sexpr ++ ";\n"))) assignExprs
    putStrLn ""
    
    putStrLn ("  always @(posedge CLK) begin")
    putStrLn ("    if(!RESET_N) begin")
    mapM (\(nm, (ty, init)) -> case init of
             Nothing -> putStr ""
             Just init' -> putStrLn (ppDealSize0 ty "" ("      " ++ ppName nm ++ " <= " ++ ppConst init' ++ ";"))) regInits
    putStrLn "    end"
    putStrLn "    else begin"
    mapM (\(nm, (ty, sexpr)) -> putStrLn (ppDealSize0 ty "" ("      " ++ ppName nm ++ " <= " ++ sexpr ++ ";"))) regExprs
    putStrLn ""
    mapM (\(pred, sys) -> putStrLn $ "      if(" ++ pred ++ ") begin\n" ++ sys ++ "      end") sys
    putStrLn "    end"
    putStrLn "  end"
    putStrLn "endmodule\n"
      where
        ins = removeDups ins'
        outs = removeDups outs'
        regInits = removeDups regInits'
        regWrites = removeDups regWrites'
        assigns = removeDups assigns' -- (Data.List.map (\i -> let y = trace (show i) i in y) assigns')
        convAssigns =
          mapM (\(nm, (ty, expr)) ->
                  do
                    s <- ppRtlExpr "wire" expr
                    return (nm, (ty, s))) (Data.List.map (\i -> let y = trace (show i) i in y) assigns)
        convRegs =
          mapM (\(nm, (ty, expr)) ->
                  do
                    s <- ppRtlExpr "reg" expr
                    return (nm, (ty, s))) regWrites
        (assignExprs, assignTruncs') = runState convAssigns H.empty
        (regExprs, regTruncs') = runState convRegs H.empty
        assignTruncs = H.toList assignTruncs'
        regTruncs = H.toList regTruncs'
        convSys = mapM(\(pred, listSys) ->
                         do
                           predExpr <- ppRtlExpr "sys" pred
                           s <- mapM ppRtlSys listSys
                           return $ (predExpr, Data.List.concat s)) sys'
        (sys, sysTruncs') = runState convSys H.empty
        sysTruncs = H.toList sysTruncs'
  
ppGraph :: [(String, [String])] -> String
ppGraph x = case x of
              [] -> ""
              (a, b) : ys -> "(" ++ show a ++ ", " ++ show b ++ ", " ++ show (Data.List.length b) ++ "),\n" ++ ppGraph ys


maxOutEdge :: [(String, [String])] -> Int
maxOutEdge x = case x of
                 [] -> 0
                 (a, b) : ys -> Prelude.max (Data.List.length b) (maxOutEdge ys)

sumOutEdge :: [(String, [String])] -> Int
sumOutEdge x = case x of
                 [] -> 0
                 (a, b) : ys -> Data.List.length b + sumOutEdge ys

ppTopModule :: RtlModule -> IO ()
ppTopModule m@(Build_RtlModule regFs ins' outs' regInits' regWrites' assigns' sys') =
  do
    mapM ppRfModule regFs
    ppRtlModule m
    putStrLn "module top("
    mapM (\(nm, ty) -> putStrLn (ppDealSize0 ty "" ("  input " ++ ppDeclType (ppPrintVar nm) ty ++ ",\n"))) ins
    putStrLn ""
    mapM (\(nm, ty) -> putStrLn (ppDealSize0 ty "" ("  output " ++ ppDeclType (ppPrintVar nm) ty ++ ",\n"))) outs
    putStrLn ""
    putStrLn "  input CLK," 
    putStrLn "  input RESET_N"
    putStrLn ");"
    mapM (\(nm, ty) -> putStrLn (ppDealSize0 ty "" ("  " ++ ppDeclType (ppPrintVar nm) ty ++ ";\n"))) insAll
    putStrLn ""
    mapM (\(nm, ty) -> putStrLn (ppDealSize0 ty "" ("  " ++ ppDeclType (ppPrintVar nm) ty ++ ";\n"))) outsAll
    putStrLn ""
    mapM ppRfInstance regFs
    ppRtlInstance m
    putStrLn "endmodule"
      where
        insAll = removeDups ins'
        outsAll = removeDups outs'
        ins = Data.List.filter filtCond insAll
        outs = Data.List.filter filtCond outsAll
        badRead x read = x == read ++ "#_guard" || x == read ++ "#_enable" || x == read ++ "#_argument" || x == read ++ "#_return"
        badReads x reads = foldl (\accum (v, _) -> badRead x v || accum) False reads
        filtCond ((x, _), _) = case Data.List.find (\((((_, reads), write), (_, _))) ->
                                                       badReads x reads ||
                                                     {-
                                                     x == read ++ "#_guard" ||
                                                     x == read ++ "#_enable" ||
                                                     x == read ++ "#_argument" ||
                                                     x == read ++ "#_return" ||
                                                     -}
                                                     x == write ++ "#_guard" ||
                                                     x == write ++ "#_enable" ||
                                                     x == write ++ "#_argument" ||
                                                     x == write ++ "#_return") regFs of
                                 Nothing -> True
                                 _ -> False

printDiff :: [(String, [String])] -> [(String, [String])] -> IO ()
printDiff (x:xs) (y:ys) =
  do
    if x == y
    then printDiff xs ys
    else putStrLn $ (show x) ++ " " ++ (show y)
printDiff [] [] = return ()
printDiff _ _ = putStrLn "Wrong lengths"

ppConstMem :: ConstT -> String
ppConstMem (ConstBool b) = if b then "1" else "0"
ppConstMem (ConstBit sz w) = if sz == 0 then "0" else ppWord (reverse $ wordToList w)
ppConstMem (ConstStruct num fk fs fv) = Data.List.concatMap ppConstMem (Data.List.map fv (getFins num))
ppConstMem (ConstArray num k fv) = Data.List.concatMap ppConstMem (reverse $ Data.List.map fv (getFins num))

ppRfFile :: String -> (((String, [(String, Bool)]), String), ((Int, Kind), ConstT)) -> IO ()
ppRfFile fileName (((name, reads), write), ((idxType, dataType), ConstArray num k fv)) =
  do
    mapM (\v -> do
             writeFile fileName $ ppConstMem v
             writeFile fileName "\n") (reverse $ Data.List.map fv (getFins num))
    writeFile fileName "\n"
    
ppRfName :: (((String, [(String, Bool)]), String), ((Int, Kind), ConstT)) -> String
ppRfName (((name, reads), write), ((idxType, dataType), ConstArray num k fv)) = ppName name ++ ".mem"
  
main =
  putStrLn (show fpu)
  -- do
  --   let (Build_RtlModule regFs _ _ _ _ _ _) = fpu in
  --     mapM_ (\rf -> (ppRfFile (ppRfName rf) rf)) regFs
  --   ppTopModule fpu
