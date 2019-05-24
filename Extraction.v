Require Export List String Ascii.
Require Export Syntax Compile Rtl.

Require Coq.extraction.Extraction.

Require Export ExtrHaskellBasic ExtrHaskellNatInt ExtrHaskellString.

Extraction Language Haskell.

Set Extraction Optimize.
Set Extraction KeepSingleton.
Unset Extraction AutoInline.

Extract Inductive sigT => "(,)" ["(,)"].
Extract Inlined Constant fst => "Prelude.fst".
Extract Inlined Constant snd => "Prelude.snd".
Extract Inlined Constant projT1 => "Prelude.fst".
Extract Inlined Constant projT2 => "Prelude.snd".
Extract Inlined Constant map => "Prelude.map".
Extract Inlined Constant concat => "Prelude.concat".
Extract Inlined Constant mod2 => "Prelude.odd".
Extract Constant nat_cast => "(\_ _ x -> x)".
Extract Inlined Constant length => "Prelude.length".
Extract Inlined Constant Datatypes.length => "Prelude.length".
Extract Constant Nat.div2 => "(`Prelude.div` 2)".
Extract Constant Nat.log2 => "(\x -> Prelude.floor (Prelude.logBase 2 (Prelude.fromIntegral x)))".
Extract Constant Nat.log2_up => "(\x -> Prelude.ceiling (Prelude.logBase 2 (Prelude.fromIntegral x)))".
Extract Constant List.fold_left => "(\f bs a -> Prelude.foldl f a bs)".
Extract Constant natToWord => "(\sz n -> (sz, Prelude.toInteger n))".
Extract Constant Vector.nth => "(\_ xs (_,i) -> xs Prelude.!! i)".
Extract Constant sumSizes => "(\n f -> Prelude.sum (Prelude.map (\i -> f (n,i)) [0..(n Prelude.-1)]))".


Extract Inductive word => "(Prelude.Int,Prelude.Integer)" ["(0,0)" "(\b _ (n,v) -> let v' = Data.Bits.shiftL v 1 in if b then (n Prelude.+1,Data.Bits.setBit v' 0) else (n Prelude.+1,v'))"]
  "(\f0 fS (n,v) -> if n Prelude.== 0 then f0 () else fS (Data.Bits.testBit v 0) (n Prelude.-1) ((n Prelude.-1), Data.Bits.shiftR v 1))".

Extract Inductive Fin.t => "(Prelude.Int,Prelude.Int)" ["(\n -> (n,0))" "(\n (_,i) -> (n,Prelude.succ i))"]
  "(\f0 fS (n,i) -> if i Prelude.== 0 then f0 n else fS n (n Prelude.-1, i Prelude.-1))".

Extract Inductive Vector.t => "[]" ["[]" "(\x _ xs -> x : xs)"] "(\fnil fcons xs -> case xs of { [] -> fnil (); (x:xs) -> fcons x (Prelude.length xs) xs })".
