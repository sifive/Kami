Require Import Kami.Syntax Kami.Notations.

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

Local Open Scope kami_action.
Local Open Scope kami_expr.

Definition nullStruct: Kind :=
  (Struct (fun i => @Fin.case0 _ i) (fun i => @Fin.case0 _ i)).

Fixpoint BuildStructActionCont
         (ty: Kind -> Type) k
         n:
  forall (kinds : Fin.t n -> Kind)
                        (names : Fin.t n -> string)
                        (acts  : forall i, ActionT ty (kinds i))
                        (cont: (forall i, Expr ty (SyntaxKind (kinds i))) -> ActionT ty k),
    ActionT ty k :=
  match n return forall (kinds : Fin.t n -> Kind)
                        (names : Fin.t n -> string)
                        (acts  : forall i, ActionT ty (kinds i))
                        (cont  : (forall i, Expr ty (SyntaxKind (kinds i))) ->
                                 ActionT ty k), ActionT ty k with
  | 0 => fun kinds names acts cont =>
           cont (fun i => @Fin.case0 (fun _ => Expr ty (SyntaxKind (kinds i))) i)
  | S m => fun kinds names acts cont =>
             LETA next <- acts Fin.F1;
               @BuildStructActionCont
                 ty k m (fun i => kinds (Fin.FS i))
                 (fun i => names (Fin.FS i))
                 (fun i => acts (Fin.FS i))
                 (fun exps =>
                    cont (fun i =>
                            match i in Fin.t (S m) return
                                  forall (ks:
                                            Fin.t (S m) -> Kind),
                                    ty (ks Fin.F1) ->
                                    (forall i: Fin.t m, Expr ty (SyntaxKind (ks (Fin.FS i)))) ->
                                    Expr ty (SyntaxKind (ks i))
                            with
                            | Fin.F1 _ => fun ks next exps => #next
                            | Fin.FS _ j => fun ks next exps => exps j
                            end kinds next exps))
end.

Definition BuildStructAction ty n (kinds: Fin.t n -> Kind) (names: Fin.t n -> string) (acts: forall i, ActionT ty (kinds i)) :=
  BuildStructActionCont kinds names acts (fun x => Return (BuildStruct kinds names x)).

