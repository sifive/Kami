Require Import Kami.Syntax Kami.KamiNotations.

(* TODO: move to KamiStdLib? *)
Definition extractArbitraryRange ty sz (inst: Bit sz ## ty) (range: nat * nat):
  Bit (fst range + 1 - snd range) ## ty :=
  (LETE i <- inst ;
     RetE (ConstExtract (snd range) (fst range + 1 - snd range) (sz - 1 - fst range)
                        (ZeroExtendTruncLsb _ #i)))%kami_expr.

(* Useful Struct:
   TODO: move notation versions to StdLibKami*)
Definition Maybe k :=  STRUCT_TYPE {
                           "valid" :: Bool;
                           "data"  :: k }.

Definition Pair (A B: Kind) := STRUCT_TYPE {
                                   "fst" :: A;
                                   "snd" :: B }.

Definition Invalid {ty: Kind -> Type} {k} := (STRUCT { "valid" ::= $$ false ; "data" ::= $$ (getDefaultConst k) })%kami_expr.
