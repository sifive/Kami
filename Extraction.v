Require Export List String Ascii.
Require Export Kami.Syntax Kami.Compiler.CompilerSimple Kami.Compiler.Compiler Kami.Compiler.Rtl Kami.LibStruct Kami.Compiler.UnverifiedIncompleteCompiler.

Require Import Kami.Notations.

Require Coq.extraction.Extraction.

Require Export ExtrHaskellBasic ExtrHaskellNatInt ExtrHaskellString ExtrHaskellZInteger.

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
Extract Constant sumSizes => "(\n f -> Prelude.sum (Prelude.map (\i -> f (n Prelude.-1,i)) [0..(n Prelude.-1)]))".
Extract Constant nth_Fin => "(\xs (_,i) -> xs Prelude.!! i)".
Extract Constant nth_Fin_map2 => "(\_ _ _ x -> x)".
Extract Constant getFins => "(\n -> Prelude.map ((,) (n Prelude.- 1)) [0..(n Prelude.- 1)])".
Extract Constant Fin.to_nat => "(\_ (_,i) -> i)".
Extract Constant Fin.cast => "(\_ x _ -> x)".
Extract Constant Fin.of_nat_lt => "(\i n -> (n Prelude.- 1,i))".
Extract Constant Fin_eq_dec => "(\_ x y -> x Prelude.== y)".
Extract Inlined Constant getBool => "Prelude.id".

Section Ty.
  Variable ty: Kind -> Type.
  Local Open Scope kami_expr.
  Definition predPack k (pred: Bool @# ty) (val: k @# ty) :=
    (IF pred
     then pack val
     else $0).

  Definition orKind k (ls: list (Bit (size k) @# ty)) := unpack k (CABit Bor ls).

  Definition predPackOr k (ls: list ((Bool @# ty) * (k @# ty))) := (CABool Or (map fst ls), orKind k (map (fun '(p, v) => predPack p v) ls)).

  Definition createWriteRq ty (idxNum num: nat) (k: Kind) (idx: Bit (Nat.log2_up idxNum) @# ty) (val: Array num k @# ty): WriteRq (Nat.log2_up idxNum) (Array num k) @# ty :=
    STRUCT { "addr" ::= idx ;
             "data" ::= val }.

  Definition createWriteRqMask ty (idxNum num: nat) (k: Kind) (idx: Bit (Nat.log2_up idxNum) @# ty) (val: Array num k @# ty) (mask: Array num Bool @# ty): WriteRqMask (Nat.log2_up idxNum) num k @# ty :=
    STRUCT { "addr" ::= idx ;
             "data" ::= val ;
             "mask" ::= mask }.

  Definition pointwiseIntersectionNoMask (idxNum num: nat) (k: Kind)
             (readPred: Bool @# ty)
             (readAddr: Bit (Nat.log2_up idxNum) @# ty)
             (writePred: Bool @# ty) (writeRq: WriteRq (Nat.log2_up idxNum) (Array num k) @# ty)
    : Array num (Maybe k) @# ty
    := BuildArray
         (fun i =>
            let readAddr_i := readAddr + $(proj1_sig (Fin.to_nat i)) in
            STRUCT { "valid" ::= (readPred
                                    && writePred
                                    && (writeRq @% "addr" <= readAddr_i)
                                    && (readAddr_i < writeRq @% "addr" + $num));
                     "data" ::= (writeRq @% "data")@[readAddr - writeRq @% "addr" + $(proj1_sig (Fin.to_nat i))] } : Maybe k @# ty).
  
  Definition pointwiseIntersectionMask (idxNum num: nat) (k: Kind)
             (readPred: Bool @# ty)
             (readAddr: Bit (Nat.log2_up idxNum) @# ty)
             (writePred: Bool @# ty) (writeRq: WriteRqMask (Nat.log2_up idxNum) num k @# ty)
    : Array num (Maybe k) @# ty
    := BuildArray
         (fun i =>
            let readAddr_i := readAddr + $(proj1_sig (Fin.to_nat i)) in
            STRUCT { "valid" ::= (readPred
                                    && writePred
                                    && ((writeRq @% "mask")@[readAddr - writeRq @% "addr" + $(proj1_sig (Fin.to_nat i))])
                                    && (writeRq @% "addr" <= readAddr_i)
                                    && (readAddr_i < writeRq @% "addr" + $num));
                     "data" ::= (writeRq @% "data")@[readAddr - writeRq @% "addr" + $(proj1_sig (Fin.to_nat i))] } : Maybe k @# ty).
  
  Definition pointwiseIntersection (idxNum num: nat) (k: Kind) (isMask: bool)
             (readPred: Bool @# ty)
             (readAddr: Bit (Nat.log2_up idxNum) @# ty)
             (writePred: Bool @# ty) (writeRq: if isMask
                                               then WriteRqMask (Nat.log2_up idxNum) num k @# ty
                                               else WriteRq (Nat.log2_up idxNum) (Array num k) @# ty)
    : Array num (Maybe k) @# ty :=
    match isMask return (if isMask
                         then WriteRqMask (Nat.log2_up idxNum) num k @# ty
                         else WriteRq (Nat.log2_up idxNum) (Array num k) @# ty) -> Array num (Maybe k) @# ty
    with
    | true => fun writeRq =>
                pointwiseIntersectionMask idxNum readPred readAddr writePred writeRq
    | false => fun writeRq =>
                 pointwiseIntersectionNoMask idxNum readPred readAddr writePred writeRq
    end writeRq.

  Definition pointwiseBypass (num: nat) (k: Kind) (bypass: Array num (Maybe k) @# ty) (resp: Array num k @# ty)
    : Array num k @# ty :=
    BuildArray
      (fun i => (IF (ReadArrayConst bypass i) @% "valid"
                 then (ReadArrayConst bypass i) @% "data"
                 else ReadArrayConst resp i)).
  Local Close Scope kami_expr.
End Ty.

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
