Require Import Kami.Syntax Kami.Notations.
Require Import Kami.StdLib.Fin.

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
         {n}:
  forall (kinds : Fin n -> Kind)
                        (names : Fin n -> string)
                        (acts  : forall i, ActionT ty (kinds i))
                        (cont: (forall i, Expr ty (SyntaxKind (kinds i))) -> ActionT ty k),
    ActionT ty k :=
  match n return forall (kinds : Fin n -> Kind)
                        (names : Fin n -> string)
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
                            match i return
                              forall ks : Fin (S m) -> Kind,
                                ty (ks Fin.F1) ->
                                (forall j : Fin m, Expr ty (SyntaxKind (ks (Fin.FS j)))) ->
                                Expr ty (SyntaxKind (ks i)) with
                            | inl u => match u with tt => fun ks next exps => #next end
                            | inr j => fun ks next exps => exps j
                            end kinds next exps))
end.

Definition BuildStructAction ty n (kinds: Fin n -> Kind) (names: Fin n -> string) (acts: forall i, ActionT ty (kinds i)) :=
  BuildStructActionCont kinds names acts (fun x => Return (BuildStruct kinds names x)).

Lemma WfConcatActionT_BuildStructActionCont:
 forall m k n kinds names acts cont,
   (forall (i:Fin n), WfConcatActionT (acts i) m) ->
   (forall x, WfConcatActionT (cont x) m) ->
   @WfConcatActionT type k (@BuildStructActionCont type k
                                              n kinds names acts cont) m.
Proof.
  induction n; simpl; intros; auto.
  econstructor; [|intros; eapply IHn]; eauto.
Qed.
