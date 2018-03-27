Require Export List String.
Require Export Syntax Compile Rtl.

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

(* Extraction "Target.hs" RtlModule size. *)










(* Extract Inductive Vector.t => "Vtor" ["NilV" "ConsV"]. *)

(* Definition target := computeModule targetMod (map (@attrName _) (getRules targetMod)) nil. *)

(*
Open Scope string.
Eval vm_compute in (getCallGraph mod).
Eval vm_compute in (methPos mod (map (@attrName _) (getRules mod)) "enq.f2d").
Close Scope string.
*)
(* Extraction "Target.hs" target. *)

