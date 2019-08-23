Require Export List String Ascii.
Require Export Kami.Syntax Kami.Compile Kami.Rtl.

Require Coq.extraction.Extraction.

Require Export ExtrHaskellBasic ExtrHaskellNatInt ExtrHaskellString.

Extraction Language Haskell.

Set Extraction Optimize.
Set Extraction KeepSingleton.
Unset Extraction AutoInline.

Extract Inductive sigT => "(,)" ["(,)"].
Extract Inductive word => "CustomExtract.EWord" ["CustomExtract.wordNil" "CustomExtract.wordCons"] "CustomExtract.wordRec".
Extract Inductive Fin.t => "CustomExtract.EFin" ["CustomExtract.fin0" "CustomExtract.finS"] "CustomExtract.finRec".
(* Extract Inductive Vector.t => "[]" ["[]" "(\x xs -> x : xs)"] "(\fnil fcons xs -> case xs of { [] -> fnil (); (x:xs) -> fcons x xs })".
Extract Inductive Vector.t => "[]" ["[]" "(:)"].
 *)

Extract Inlined Constant fst => "Prelude.fst".
Extract Inlined Constant snd => "Prelude.snd".
Extract Inlined Constant projT1 => "Prelude.fst".
Extract Inlined Constant projT2 => "Prelude.snd".
Extract Inlined Constant map => "Prelude.map".
Extract Inlined Constant List.concat => "Prelude.concat".
Extract Inlined Constant String.concat => "Data.List.intercalate".
Extract Inlined Constant mod2 => "Prelude.odd".
Extract Constant nat_cast => "(\_ _ x -> x)".
Extract Inlined Constant length => "Prelude.length".
Extract Inlined Constant Datatypes.length => "Prelude.length".
Extract Constant Nat.div2 => "(`Prelude.div` 2)".
Extract Constant Nat.log2 => "(\x -> Prelude.floor (Prelude.logBase 2 (Prelude.fromIntegral x)))".
Extract Constant Nat.log2_up => "(\x -> Prelude.ceiling (Prelude.logBase 2 (Prelude.fromIntegral x)))".
Extract Constant List.fold_left => "(\f bs a -> Data.List.foldl' f a bs)".
Extract Constant natToWord => "(\sz n -> (sz, Prelude.toInteger n))".
Extract Constant wordToNat => "(\_ (_,v) -> Prelude.fromIntegral v)".
Extract Constant sumSizes => "(\n f -> Prelude.sum (Prelude.map (\i -> f (n,i)) [0..(n Prelude.-1)]))".
Extract Constant nth_Fin => "(\xs (_,i) -> xs Prelude.!! i)".
Extract Constant nth_Fin_map2 => "(\_ _ _ x -> x)".
Extract Constant getFins => "(\x -> Prelude.map ((,) (x Prelude.-1)) [0..(x Prelude.- 1)])".
Extract Constant Fin.to_nat => "(\_ (_,i) -> i)".
Extract Constant Fin.cast => "(\_ x _ -> x)".
(* Extract Constant Fin.of_nat_lt => "(\i n -> (n,i))". *)
Extract Constant Fin_eq_dec => "(\_ x y -> x Prelude.== y)".
Extract Inlined Constant getBool => "Prelude.id".

(*
Extract Inlined Constant concat => "Prelude.concat".
*)

(*
Extract Inlined Constant filter => "Prelude.filter".
*)

(*
Extract Inlined Constant find => "Data.List.find".
*)

(*
Extract Constant seq => "(\x y -> [x..(x Prelude.+ y Prelude.- 1)])".
*)

(* Extract Constant getFinsBound => "(\bound n -> Prelude.map ((,) (n Prelude.- 1)) [0..(Prelude.min (n Prelude.- 1) (bound Prelude.-1))])". *)

(*
Extract Constant Nat.pow => "(\x y -> x Prelude.^ y)".

*)


(* Extraction Implicit Vector.cons [1].
Extract Constant Vector.caseS => "(\f n xs -> f (Prelude.head xs) n (Prelude.tail xs))".
Extraction Implicit Vector.map [4].
Extract Constant Vector.map => "Prelude.map".
Extraction Implicit Vector.nth [2].
Extract Constant Vector.nth => "(\xs (_,i) -> xs Prelude.!! i)".
Extraction Implicit Vector.to_list [2].
Extract Constant Vector.to_list => "Prelude.id".
 *)
