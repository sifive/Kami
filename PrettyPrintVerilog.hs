{-# OPTIONS_GHC -XStandaloneDeriving #-}

import Target hiding (map, concat, State, get, put)
import Data.List
import Data.List.Split
import Control.Monad.State.Lazy
import qualified Data.HashMap.Lazy as H
import Debug.Trace

instance Show Target.Word where
  show w = show (wordToNat 0 w)

intToFin :: Int -> Int -> T
intToFin m 0 = F1 (m-1)
intToFin m n = FS (m-1) (intToFin (m-1) (n-1))

deriving instance Eq T

ppDealSize0 :: Kind -> String -> String -> String
ppDealSize0 ty def str = if size ty == 0 then def else str

ppVecLen :: Int -> String
ppVecLen n = "[" ++ show (n-1) ++ ":0]"

finToInt :: T -> Int
finToInt (F1 _) = 0
finToInt (FS _ x) = Prelude.succ (finToInt x)

instance Show T where
  show f = show (finToInt f)

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
ppName s = intercalate "$" (Data.List.map (\x -> ppDottedName x) (splitOneOf "$#?" s))
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


ppPrintVar :: (String, Int) -> String
ppPrintVar (s, v) = ppName $ s ++ if v /= 0 then '#' : show v else []

ppWord :: [Bool] -> String
ppWord [] = []
ppWord (b : bs) = (if b then '1' else '0') : ppWord bs

ppConst :: ConstT -> String
ppConst (ConstBool b) = if b then "1'b1" else "1'b0"
ppConst (ConstBit sz w) = show sz ++ "\'b" ++ ppWord (reverse $ wordToList w)
ppConst (ConstArray n k fv) = '{' : intercalate ", " (Data.List.map ppConst (Data.List.map fv (getFins n))) ++ "}"
ppConst (ConstStruct n fk fs fv) = '{' : intercalate ", " (snd (unzip (Data.List.filter (\(k,e) -> size k /= 0) (zip (Data.List.map fk (getFins n)) (Data.List.map ppConst (Data.List.map fv (getFins n))))))) ++ "}"


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
    RtlCABit n Band es -> listExpr "&" es (show n ++ "'b" ++ Data.List.replicate n '1')
    RtlCABit n Bor es -> listExpr "|" es (show n ++ "'b0")
    RtlCABit n Bxor es -> listExpr "^" es (show n ++ "'b0")
    RtlBinBit _ _ _ (Sub _) e1 e2 -> binExpr e1 "-" e2
    RtlBinBit _ _ _ (Div _) e1 e2 -> binExpr e1 "/" e2
    RtlBinBit _ _ _ (Rem _) e1 e2 -> binExpr e1 "%" e2
    RtlBinBit _ _ _ (Sll _ _) e1 e2 -> binExpr e1 "<<" e2
    RtlBinBit _ _ _ (Srl _ _) e1 e2 -> binExpr e1 ">>" e2
    RtlBinBit _ _ _ (Sra n m) e1 e2 ->
      do
        x1 <- ppRtlExpr who e1
        x2 <- ppRtlExpr who e2
        new <- addToTrunc (Bit n) ("($signed(" ++ x1 ++ ") >>> " ++ x2 ++ ")")
        return $ new
        -- return $ "($signed(" ++ x1 ++ ") >>> " ++ x2 ++ ")"
    RtlBinBit _ _ _ (Concat m n) e1 e2 ->
      case (m, n) of
        (0, 0)   -> return $ "0"
        (m', 0)  -> do
          x1 <- ppRtlExpr who e1
          return x1
        (0, n')  -> do
          x2 <- ppRtlExpr who e2
          return x2
        (m', n') -> do
          x1 <- ppRtlExpr who e1
          x2 <- ppRtlExpr who e2
          return $ '{' : x1 ++ ", " ++ x2 ++ "}"
      -- if n /= 0
      -- then
      --   do
      --     x1 <- ppRtlExpr who e1
      --     x2 <- ppRtlExpr who e2
      --     return $ '{' : x1 ++ ", " ++ x2 ++ "}"
      -- else
      --   do
      --     x1 <- ppRtlExpr who e1
      --     return x1
    RtlBinBitBool _ _ (_) e1 e2 -> binExpr e1 "<" e2
    RtlITE _ p e1 e2 -> triExpr p "?" e1 ":" e2
    RtlEq _ e1 e2 -> binExpr e1 "==" e2
    RtlReadStruct num fk fs e i ->
      do
        new <- optionAddToTrunc (Struct num fk fs) e
        return $ new ++ '.' : ppName (fs i)
    RtlBuildStruct num fk fs es ->
      do
        strs <- mapM (ppRtlExpr who) (filterKind0 num fk es)  -- (Data.List.map es (getFins num))
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
        return $ if size k == 0 || n == 0 then "0" else '{': intercalate ", " strs ++ "}"
  where
    filterKind0 num fk es = snd (unzip (Data.List.filter (\(k,e) -> size k /= 0) (zip (Data.List.map fk (getFins num)) (Data.List.map es (getFins num)))))
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

ppRfInstance :: RtlRegFileBase -> String
ppRfInstance (rf@(Build_RtlRegFileBase isWrMask num name reads write idxNum dataType init)) =
  "  " ++ ppName name ++ " " ++
  ppName name ++ "$inst(.CLK(CLK), .RESET(RESET), " ++
ppRfInstance (_, rf@(RegFile name reads write idxNum dataType init)) =
  "  " ++ ppName name ++ " " ++
  (case reads of
     RtlAsync readLs ->
       concatMap (\(read, _) ->
                    ("." ++ ppName read ++ "$_enable(" ++ ppName read ++ "$_enable), ") ++
                    (ppDealSize0 (Bit (log2_up idxNum)) "" ("." ++ ppName read ++ "$_argument(" ++ ppName read ++ "$_argument), ")) ++
                    ppDealSize0 (Array num dataType) "" ("." ++ ppName read ++ "$_return(" ++ ppName read ++ "$_return), ")) readLs
     RtlSync isAddr readLs ->
       concatMap (\(Build_RtlSyncRead (Build_SyncRead readRq readRs _) _ _) ->
                    ("." ++ ppName readRq ++ "$_enable(" ++ ppName readRq ++ "$_enable), ") ++
                    (ppDealSize0 (Bit (log2_up idxNum)) "" ("." ++ ppName readRq ++ "$_argument(" ++ ppName readRq ++ "$_argument), ")) ++
                    ("." ++ ppName readRs ++ "$_enable(" ++ ppName readRs ++ "$_enable), ") ++
                    ppDealSize0 (Array num dataType) "" ("." ++ ppName readRs ++ "$_return(" ++ ppName readRs ++ "$_return), ")) readLs) ++
  ("." ++ ppName write ++ "$_enable(" ++ ppName write ++ "$_enable), ") ++
  ("." ++ ppName write ++ "$_argument(" ++ ppName write ++ "$_argument)") ++
  ");\n\n"

ppRfModule :: Build_RtlRegFileBase -> String
ppRfModule (rf@(Build_RtlRegFileBase isWrMask num name reads write idxNum dataType init)) =
  let writeType = if isWrMask then writeRqMask idxNum num dataType else writeRq idxNum (Array num dataType) in
  "module " ++ ppName name ++ "(\n" ++
  (case reads of
     RtlAsync readLs ->
       concatMap (\read ->
                    ("  input " ++ ppDeclType (ppName read ++ "$_enable") Bool ++ ",\n") ++
                   (ppDealSize0 (Bit (log2_up idxNum)) "" ("  input " ++ ppDeclType (ppName read ++ "$_argument") (Bit (log2_up idxNum)) ++ ",\n")) ++
                   ppDealSize0 (Array num dataType) "" ("  output " ++ ppDeclType (ppName read ++ "$_return") (Array num dataType) ++ ",\n")) readLs
     RtlSync isAddr readLs ->
       concatMap (\(Build_RtlSyncRead (Build_SyncRead readRq readRs _) _ _) ->
                    ("  input " ++ ppDeclType (ppName readRq ++ "$_enable") Bool ++ ",\n") ++
                   (ppDealSize0 (Bit (log2_up idxNum)) "" ("  input " ++ ppDeclType (ppName readRq ++ "$_argument") (Bit (log2_up idxNum)) ++ ",\n")) ++
                    ("  input " ++ ppDeclType (ppName readRs ++ "$_enable") Bool ++ ",\n") ++
                   ppDealSize0 (Array num dataType) "" ("  output " ++ ppDeclType (ppName readRs ++ "$_return") (Array num dataType) ++ ",\n")) readLs) ++
   ("  input " ++ ppDeclType (ppName write ++ "$_enable") Bool ++ ",\n") ++
  ppDealSize0 writeType "" (("  input " ++ ppDeclType (ppName write ++ "$_argument") writeType ++ ",\n")) ++
  "  input logic CLK,\n" ++
  "  input logic RESET\n" ++
  ");\n" ++
  ppDealSize0 dataType "" ("  " ++ ppDeclType (ppName name ++ "$_data") dataType ++ "[0:" ++ show (idxNum - 1) ++ "];\n") ++
  (case reads of
     RtlSync isAddr readLs ->
       concatMap (\(Build_RtlSyncRead (Build_SyncRead readRq readRs readReg) bypRqRs bypWrRd) ->
                    if isAddr
                    then ppDealSize0 (Bit (log2_up idxNum)) "" ("  " ++ ppDeclType (ppName readReg) (Bit (log2_up idxNum)) ++ ";\n")
                    else ppDealSize0 (Array num dataType) "" ("  " ++ ppDeclType (ppName readReg) (Array num dataType)) ++
                         ppDealSize0 (Array num dataType) "" ("  " ++ ppDeclType (ppName (readReg ++ "$_temp")) (Array num dataType))
                 ) readLs
     _ -> "") ++
  "\n" ++
  (case init of
     RFFile isAscii file ->
       "  initial begin\n" ++
       "    $readmem" ++ if isAscii then "h" else "b" ++ "(\"" ++ file ++ "\", " ++ ppName name ++ "$_data);\n" ++
       "  end\n\n"
     _ -> "") ++
  let writeByps readAddr i = 
        concatMap (\j -> "(" ++ 
                         "(" ++ ppName write ++ "$_enable && (" ++
                         "(" ++ ppDealSize0 (Bit (log2_up idxNum)) "0" (ppName write ++ "$_argument.addr + " ++ show j) ++ ") == " ++
                         "(" ++ ppDealSize0 (Bit (log2_up idxNum)) "0" (readAddr ++ " + " ++ show i) ++ "))" ++
                         (if isWrMask
                          then " && " ++ ppName write ++ "$_argument.mask[" ++ show j ++ "]"
                          else "") ++
                         ") ? " ++
                         ppDealSize0 dataType "0" (ppName write ++ "$_argument.data[" ++ show j ++ "]") ++ " : 0) | ")
        [0 .. (num-1)] in
    let readResponse readResp readAddr isByp =
          ppDealSize0 (Array num dataType) "" ("  assign " ++ ppName readResp ++ " = " ++ "{" ++
                                                intercalate ", " (map (\i ->
                                                                          ppDealSize0 (Bit (log2_up idxNum)) "0" (readAddr ++ " + " ++ show i ++ " >= " ++ show idxNum) ++ "?"
                                                                          if isByp then writeByps readAddr i else "") ++ ppDealSize0 dataType "0" (ppName name ++ "$_data[" ++ (ppDealSize0 (Bit (log2_up idxNum)) "0" (readAddr ++ " + " ++ show i)) ++ "]") ++ ": 0")
                                                [0 .. (num-1)] ++ "};\n") in
      (case reads of
         RtlAsync readLs -> concatMap (\(read, bypass) ->
                                         readResponse (read ++ "$_return") (ppName (read ++ "$_argument")) bypass) readLs
         RtlSync isAddr readLs ->
           concatMap (\(Build_RtlSyncRead (Build_SyncRead readRq readRs readReg) bypRqRs bypWrRd) ->
                        if isAddr
                        then readResponse (readRs ++ "$_return") (if bypRqRs then "(" ++ (ppName (readRq ++ "$_enable") ++ "? " ++ ppName (readRq ++ "$_argument") ++ ": " ++ ppName readReg) ++ ")" else ppName readReg) bypWrRd
                        else readResponse (readReg ++ "$_temp") readRq bypWrRd ++
                             ppDealSize0 (Array num dataType) "" ("  assign " ++ ppName readRs ++ " = " ++ if bypRqRs then "(" ++ (ppName (readRq ++ "$_enable") ++ "? " ++ ppName (readReg ++ "$_temp") ++ ": " ++ ppName readReg ++ ")"  else ppName readReg)
                     ) readLs) ++
  "  always@(posedge CLK) begin\n" ++
  "    if(RESET) begin\n" ++
  (case init of
     RFNonFile (Just initVal) ->
       "      for(int _i = 0; _i < " ++ show idxNum ++ "; _i=_i+1) begin\n" ++
       ppDealSize0 dataType "" ("        " ++ ppName name ++ "$_data[_i] = " ++ ppConst initVal ++ ";\n") ++
       "      end\n"
     _ -> "") ++
  "    end else begin\n" ++
  (case reads of
     RtlAsync readLs -> ""
     RtlSync isAddr readLs ->
       concatMap (\(Build_RtlSyncRead (Build_SyncRead readRq readRs readReg) bypRqRs bypWrRd) ->
                    if isAddr
                    then "      if(" ++ ppName (readRq ++ "$_enable") ++ ") begin\n" ++
                         "        " ++ ppName readReg ++ " <= " ++ ppName (readRq ++ "$_argument") ++ ";\n" ++
                         "      end\n"
                    else "      if(" ++ ppName (readRq ++ "$_enable") ++ ") begin\n" ++
                         "        " ++ ppName readReg ++ " <= " ++ ppName (readReg ++ "$_temp") ++ ";\n" ++
                         "      end\n"
                 ) readLs) ++
  "    end\n" ++
  "  end\n"
  "endmodule\n\n"

removeDups :: Eq a => [(a, b)] -> [(a, b)]
removeDups = nubBy (\(a, _) (b, _) -> a == b)

getAllMethodsRegFileList :: [RegFileBase] -> [(String, (Kind, Kind))]
getAllMethodsRegFileList ls = map (\(x, (y, z)) -> (x, y)) (concat (map (\x -> getMethods (BaseRegFile x)) ls))



ppRtlInstance :: RtlModule -> String
ppRtlInstance m@(Build_RtlModule hiddenWires regFs ins' outs' regInits' regWrites' assigns' sys') =
  "  _design _designInst(.CLK(CLK), .RESET(RESET)" ++
  concatMap (\(nm, ty) -> ppDealSize0 ty "" (", ." ++ ppPrintVar nm ++ '(' : ppPrintVar nm ++ ")")) (removeDups ins' ++ removeDups outs') ++
  concatMap (\(nm, ty) -> ppDealSize0 ty "" (", ." ++ ppPrintVar nm ++ '(' : ppPrintVar nm ++ ")")) rfMeths ++ ");\n"
  where
    rfMeths = Data.List.map (\x -> ((fst x ++ "#_argument", 0), fst (snd x)) ) (getAllMethodsRegFileList (map snd regFs)) ++
              Data.List.map (\x -> ((fst x ++ "#_return", 0), snd (snd x)) ) (getAllMethodsRegFileList (map snd regFs)) ++
              Data.List.map (\x -> ((fst x ++ "#_enable", 0), Bool) ) (getAllMethodsRegFileList (map snd regFs))
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
ppRtlSys (RtlFinish) = return $ "        $finish();\n"

ppRtlModule :: RtlModule -> String
ppRtlModule m@(Build_RtlModule hiddenWires regFs ins' outs' regInits' regWrites' assigns' sys') =
  "module _design(\n" ++
  concatMap (\(nm, ty) -> ppDealSize0 ty "" ("  input " ++ ppDeclType (ppPrintVar nm) ty ++ ",\n")) ins ++ "\n" ++
  concatMap (\(nm, ty) -> ppDealSize0 ty "" ("  output " ++ ppDeclType (ppPrintVar nm) ty ++ ",\n")) outs ++ "\n" ++
  concatMap (\(nm, ty) -> ppDealSize0 ty "" ("  input " ++ ppDeclType (ppPrintVar nm) ty ++ ",\n")) rfMethsIn ++ "\n" ++
  concatMap (\(nm, ty) -> ppDealSize0 ty "" ("  output " ++ ppDeclType (ppPrintVar nm) ty ++ ",\n")) rfMethsOut ++ "\n" ++

  "  input CLK,\n" ++
  "  input RESET\n" ++
  ");\n" ++
  concatMap (\(nm, (ty, init)) -> ppDealSize0 ty "" ("  " ++ ppDeclType (ppName nm) ty ++ ";\n")) regInits ++ "\n" ++

  concatMap (\(nm, (ty, expr)) -> ppDealSize0 ty "" ("  " ++ ppDeclType (ppPrintVar nm) ty ++ ";\n")) assigns ++ "\n" ++

  concatMap (\(sexpr, (pos, ty)) -> ppDealSize0 ty "" ("  " ++ ppDeclType ("_trunc$wire$" ++ show pos) ty ++ ";\n")) assignTruncs ++ "\n" ++
  concatMap (\(sexpr, (pos, ty)) -> ppDealSize0 ty "" ("  " ++ ppDeclType ("_trunc$reg$" ++ show pos) ty ++ ";\n")) regTruncs ++ "\n" ++
  concatMap (\(sexpr, (pos, ty)) -> ppDealSize0 ty "" ("  " ++ ppDeclType ("_trunc$sys$" ++ show pos) ty ++ ";\n")) sysTruncs ++ "\n" ++

  concatMap (\(sexpr, (pos, ty)) -> ppDealSize0 ty "" ("  assign " ++ "_trunc$wire$" ++ show pos ++ " = " ++ sexpr ++ ";\n")) assignTruncs ++ "\n" ++
  concatMap (\(sexpr, (pos, ty)) -> ppDealSize0 ty "" ("  assign " ++ "_trunc$reg$" ++ show pos ++ " = " ++ sexpr ++ ";\n")) regTruncs ++ "\n" ++
  concatMap (\(sexpr, (pos, ty)) -> ppDealSize0 ty "" ("  assign " ++ "_trunc$sys$" ++ show pos ++ " = " ++ sexpr ++ ";\n")) sysTruncs ++ "\n" ++
  
  concatMap (\(nm, (ty, sexpr)) -> ppDealSize0 ty "" ("  assign " ++ ppPrintVar nm ++ " = " ++ sexpr ++ ";\n")) assignExprs ++ "\n" ++

  "  initial begin\n" ++
  concatMap (\(nm, (ty, init)) -> case init of
                                    ArrayHex num k file -> "      $readmemh(\"" ++ file ++ "\", " ++ ppName nm ++ ");\n"
                                    ArrayBin num k file -> "      $readmemb(\"" ++ file ++ "\", " ++ ppName nm ++ ");\n"
                                    _ -> "") regInits ++
  "  end\n" ++
  
  "  always @(posedge CLK) begin\n" ++
  "    if(RESET) begin\n" ++
  concatMap (\(nm, (ty, init)) -> case init of
                                    SimpleInit v -> ppDealSize0 ty "" ("      " ++ ppName nm ++ " <= " ++ ppConst v ++ ";\n")
                                    ArrayInit num k val -> ppDealSize0 (Array num k) "" ("      " ++ ppName nm ++ " <= " ++
                                                                                         '{' : intercalate ", " (Data.List.replicate num (ppConst val)) ++ "}"
                                                                                          ++ ";\n")
                                    _ -> "") regInits ++
  "    end\n" ++
  "    else begin\n" ++
  concatMap (\(nm, (ty, sexpr)) -> ppDealSize0 ty "" ("      " ++ ppName nm ++ " <= " ++ sexpr ++ ";\n")) regExprs ++
  concatMap (\(pred, sys) -> "      if(" ++ pred ++ ") begin\n" ++ sys ++ "      end\n") sys ++
  "    end\n" ++
  "  end\n" ++
  "endmodule\n\n"
  where
    ins = removeDups ins'
    outs = removeDups outs'
    regInits = removeDups regInits'
    regWrites = removeDups regWrites'
    assigns = removeDups assigns'
    rfMethsIn = Data.List.map (\x -> ((fst x ++ "#_return", 0), snd (snd x)) ) (getAllMethodsRegFileList (map snd regFs))
    rfMethsOut = Data.List.map (\x -> ((fst x ++ "#_argument", 0), fst (snd x)) ) (getAllMethodsRegFileList (map snd regFs)) ++
                 Data.List.map (\x -> ((fst x ++ "#_enable", 0), Bool) ) (getAllMethodsRegFileList (map snd regFs))
    convAssigns =
      mapM (\(nm, (ty, expr)) ->
              do
                s <- ppRtlExpr "wire" expr
                return (nm, (ty, s))) assigns
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


-- ppRfInstance :: RegFileBase -> string
-- ppRfInstance rf@(RegFile dataArray reads write idxNum dataT init) =
--   "  RegFile " ++ dataArray ++ "#(.idxNum(" ++ idxNum ++ "), .dataSz(" ++ size dataT ++ ")) (" ++
  
  
-- ppRfInstance rf@(SyncRegFile isAddr dataArray reads write idxNum dataT init) =


ppTopModule :: RtlModule -> String
ppTopModule m@(Build_RtlModule hiddenWires regFs ins' outs' regInits' regWrites' assigns' sys') =
  concatMap ppRfModule regFs ++
  ppRtlModule m ++
  "module top(\n" ++
  concatMap (\(nm, ty) -> ppDealSize0 ty "" ("  input " ++ ppDeclType (ppPrintVar nm) ty ++ ",\n")) insFiltered ++ "\n" ++
  concatMap (\(nm, ty) -> ppDealSize0 ty "" ("  output " ++ ppDeclType (ppPrintVar nm) ty ++ ",\n")) outsFiltered ++ "\n" ++
  "  input CLK,\n" ++
  "  input RESET\n" ++
  ");\n" ++
  concatMap (\(nm, ty) -> ppDealSize0 ty "" ("  " ++ ppDeclType (ppPrintVar nm) ty ++ ";\n")) ins ++ "\n" ++
  concatMap (\(nm, ty) -> ppDealSize0 ty "" ("  " ++ ppDeclType (ppPrintVar nm) ty ++ ";\n")) outs ++ "\n" ++
  concatMap (\(nm, ty) -> ppDealSize0 ty "" ("  " ++ ppDeclType (ppPrintVar nm) ty ++ ";\n")) rfMeths ++ "\n" ++
  concatMap ppRfInstance regFs ++
  ppRtlInstance m ++
  "endmodule\n"
  where
    ins = removeDups ins'
    outs = removeDups outs'
    isHidden (x, _) = not (elem x hiddenWires)
    insFiltered = Data.List.filter isHidden ins
    outsFiltered = Data.List.filter isHidden outs
    rfMeths = Data.List.map (\x -> ((fst x ++ "#_argument", 0), fst (snd x)) ) (getAllMethodsRegFileList (map snd regFs)) ++
              Data.List.map (\x -> ((fst x ++ "#_return", 0), snd (snd x)) ) (getAllMethodsRegFileList (map snd regFs)) ++
              Data.List.map (\x -> ((fst x ++ "#_enable", 0), Bool) ) (getAllMethodsRegFileList (map snd regFs))
              
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

ppRfFile :: (((String, [(String, Bool)]), String), ((Int, Kind), ConstT)) -> String
ppRfFile (((name, reads), write), ((idxType, dataType), ConstArray num k fv)) =
  concatMap (\v -> ppConstMem v ++ "\n") (reverse $ Data.List.map fv (getFins num)) ++ "\n"

ppRfName :: (((String, [(String, Bool)]), String), ((Int, Kind), ConstT)) -> String
ppRfName (((name, reads), write), ((idxType, dataType), ConstArray num k fv)) = ppName name ++ ".mem"

main =
  -- do
  --   let !t = show rtlMod
  --   putStr t
  do
    putStrLn $ ppTopModule rtlMod
    --let (Build_RtlModule hiddenMeths regFs _ _ _ _ _ _) = rtlMod in
    --  mapM_ (\rf -> writeFile (ppRfName rf) (ppRfFile rf)) regFs

















{-

deriving instance Show UniBoolOp
deriving instance Show CABoolOp
deriving instance Show UniBitOp
deriving instance Show CABitOp


instance Show Kind where
  show Bool = "Bool"
  show (Bit n) = "Bit " ++ show n
  show (Array n k) = "Array " ++ show n ++ " " ++ show k
  show (Struct n fk fs) = "Struct " ++ "{" ++ concatMap (\i -> show (fs i) ++ ": " ++ show (fk i) ++ "; ") (getFins n) ++ "}"

instance Show ConstT where
  show (ConstBool b) = "ConstBool " ++ show b
  show (ConstBit n w) = "ConstBit " ++ show n ++ " " ++ show w
  show (ConstStruct n fk fs fv) = "ConstStruct " ++  "{" ++ concatMap (\i -> show (fv i) ++ "; ") (getFins n) ++ "}"
  show (ConstArray n k fv) = "ConstArray " ++ "{" ++ concatMap (\i -> show (fv i) ++ "; ") (getFins n) ++ "}"

deriving instance Show RegFileBase

deriving instance Show BinBitOp

instance Show RtlExpr where
  show (RtlReadReg k s) = "RtlReadReg " ++ show k ++ " " ++ show s
  show (RtlReadWire k s) = "RtlReadWire " ++ show k ++ " " ++ show s
  show (RtlConst k c) = "RtlConst " ++ show k ++ " " ++ show c
  show (RtlUniBool op e) = "RtlUniBool " ++ show op ++ " " ++ show e
  show (RtlCABool op e) = "RtlCABool " ++ show op ++ " " ++ show e
  show (RtlUniBit _ _ op e) = "RtlUniBit " ++ show op ++ " " ++ show e
  show (RtlCABit _ op e) = "RtlCABit " ++ show op ++ " " ++ show e
  show (RtlBinBit _ _ _ op e1 e2) = "RtlCABool " ++ show op ++ " " ++ show e1 ++ " " ++ show e2
  show (RtlBinBitBool _ _ op e1 e2) = "RtlCABool " ++ show op ++ " " ++ show e1 ++ " " ++ show e2
  show (RtlITE k p e1 e2) = "RtlITE " ++ show k ++ " " ++ show p ++ " " ++ show e1 ++ " " ++ show e2
  show (RtlEq k e1 e2) = "RtlEq " ++ show k ++ " " ++ show e1 ++ " " ++ show e2
  show (RtlBuildStruct n fk fs fv) = "RtlBuildStruct " ++ show n ++ " {" ++ concatMap (\i -> show (fv i) ++ "; ") (getFins n) ++ "}"
  show (RtlBuildArray n k fv) = "RtlBuildArray " ++ show n ++ " " ++ show k ++ " {" ++ concatMap (\i -> show (fv i) ++ "; ") (getFins n) ++ "}"
  show (RtlReadStruct n fk fs e i) = "RtlReadStruct " ++ show e ++ " " ++ show i
  show (RtlReadArray n k e i) = "RtlReadArray " ++ show e ++ " " ++ show i
  show (RtlReadArrayConst n k e i) = "RtlReadArrayConst " ++ show e ++ " " ++ show i

-- instance Show RtlExpr where
--   show e = show (sexp e)

deriving instance Show BitFormat
instance Show RtlSysT where
  show (RtlDispString s) = "RtlDispString " ++ show s
  show (RtlDispBool e f) = "RtlDispBool " ++ show e ++ " " ++ show f
  show (RtlDispBit _ e f) = "RtlDispBool " ++ show e ++ " " ++ show f
  show (RtlDispStruct n fk fs e ff) = "RtlDispStruct " ++ show e ++  "{" ++ concatMap (\i -> show (ff i) ++ "; ") (getFins n) ++ "}"
  show (RtlDispArray n k fv ff) = "RtlDispArray " ++ show fv ++ " " ++ show ff

-- deriving instance Show RtlModule

instance Show RtlModule where
  show (Build_RtlModule hiddenMeths regFiles inputs outputs regInits regWrites wires sys) =
    "REGFILES:\n" ++
    foldl (\s new -> s ++ show new ++ "\n") "" regFiles ++ "\n" ++
    "\nINPUTS:\n" ++
    foldl (\s new -> s ++ show new ++ "\n") "" inputs ++ "\n" ++
    "\nOUTPUTS:\n" ++
    foldl (\s new -> s ++ show new ++ "\n") "" outputs ++ "\n" ++
    "\nREGINITS:\n" ++
    foldl (\s new -> s ++ show new ++ "\n") "" regInits ++ "\n" ++
    "\nREGWRITES:\n" ++
    foldl (\s new -> s ++ show new ++ "\n") "" regWrites ++ "\n" ++
    "\nWIRES:\n" ++
    foldl (\s new -> s ++ show (fst new) ++ ": " ++ show (fst (snd new)) ++ "\n    " ++ show (snd (snd new)) ++ "\n") "" wires ++ "\n" ++
    "\nSYS:\n" ++
    foldl (\s new -> s ++ show new ++ "\n") "" sys ++ "\n"
-}  


