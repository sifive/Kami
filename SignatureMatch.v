Require Import Kami.Syntax.
Require Import Kami.WfActionT.

Inductive SigFailure :=
| NativeMismatch : SigFailure
| SignatureMismatch : string -> SigFailure.

Fixpoint SigMatch_ActionT {k} (meths : list DefMethT) (a : ActionT (fun _ => unit) k)
  : list SigFailure :=
  match a with
  | MCall meth s e cont => match lookup String.eqb meth meths with
                           | Some (existT s' _) => if Signature_dec s s'
                                                   then []
                                                   else [SignatureMismatch meth]
                           | None => []
                           end ++ SigMatch_ActionT meths (cont tt)
  | LetExpr (SyntaxKind k') e cont => SigMatch_ActionT meths (cont tt)
  | LetExpr (NativeKind k' c) e cont => NativeMismatch :: SigMatch_ActionT meths (cont c)
  | LetAction k' a cont => SigMatch_ActionT meths a ++ SigMatch_ActionT meths (cont tt)
  | ReadNondet (SyntaxKind k') cont => SigMatch_ActionT meths (cont tt)
  | ReadNondet (NativeKind k' c) cont => NativeMismatch :: SigMatch_ActionT meths (cont c)
  | ReadReg r (SyntaxKind k') cont => SigMatch_ActionT meths (cont tt)
  | ReadReg r (NativeKind k' c) cont => NativeMismatch :: SigMatch_ActionT meths (cont c)
  | WriteReg r k' e cont => SigMatch_ActionT meths cont
  | IfElse b k' atrue afalse cont => SigMatch_ActionT meths atrue
                                                      ++ SigMatch_ActionT meths afalse
                                                      ++ SigMatch_ActionT meths (cont tt)
  | Sys l cont => SigMatch_ActionT meths cont
  | Return e => []
  end.

Definition SigMatch_rules (m : Mod) :=
  fold_right (fun rule sigfs => SigMatch_ActionT (getAllMethods m) rule ++ sigfs) nil
             (map (fun r => snd r _) (getAllRules m)).

Definition SigMatch_methods (m : Mod) :=
  fold_right (fun meth sigfs =>
                SigMatch_ActionT (getAllMethods m)
                (projT2 (action_from_MethodT meth)) ++ sigfs) nil (getAllMethods m).

Definition SigMatch_Mod (m : Mod) :=
  SigMatch_rules m ++ SigMatch_methods m.

Section Proofs.

  Section SFDefs.

    Variable ty : Kind -> Type.
    
    Section SFInd.
      Variable meths : list DefMethT.
      
      Inductive SFActionT :
        forall lret : Kind, ActionT ty lret -> Prop :=
      | SFMCall meth s e lret c : (forall v, SFActionT (c v)) ->
                                  (In meth (map fst meths) -> In (meth, s) (getKindAttr meths))
                                  -> @SFActionT lret (MCall meth s e c)
      | SFLetExpr k (e : Expr ty k) lret c : (forall v, SFActionT (c v))
                                             -> @SFActionT lret (LetExpr e c)
      | SFLetAction k (a : ActionT ty k) lret c : SFActionT a -> (forall v, SFActionT (c v)) ->
                                                  @SFActionT lret (LetAction a c)
      | SFReadNondet k lret c : (forall v, SFActionT (c v)) -> @SFActionT lret (ReadNondet k c)
      | SFReadReg r k lret c : (forall v, SFActionT (c v)) -> @SFActionT lret (ReadReg r k c)
      | SFWriteReg r k (e : Expr ty k) lret c : SFActionT c -> @SFActionT lret (WriteReg r e c)
      | SFIfElse p k (atrue : ActionT ty k) afalse lret c: (forall v, SFActionT (c v)) ->
                                                           SFActionT atrue ->
                                                           SFActionT afalse ->
                                                           @SFActionT lret (IfElse p atrue afalse c)
      | SFSys ls lret c : SFActionT c -> @SFActionT lret (Sys ls c)
      | SFReturn lret e : @SFActionT lret (Return e).
    End SFInd.
    
    Definition SFBaseModule (m : Mod) :=
      (forall rule, In rule (getAllRules m) -> SFActionT (getAllMethods m) (snd rule ty)) /\
      (forall meth, In meth (getAllMethods m) ->
                    forall v, SFActionT (getAllMethods m) (projT2 (snd meth) ty v)).
  End SFDefs.
  
  Lemma lookup_In' {A : Type}:
    forall (r : string) (ls : list (string * A)) (a : A),
      lookup String.eqb r ls = Some a -> In (r, a) ls.
  Proof.
    induction ls; intros; unfold lookup in H.
    - destruct find eqn:G; [|discriminate].
      apply find_some in G; dest; inv H0.
    - destruct find eqn:G; [|discriminate].
      apply find_some in G; dest.
      rewrite String.eqb_eq in H1; subst.
      inv H; destruct p.
      destruct H0; subst.
      + left; reflexivity.
      + right; simpl; assumption.
  Qed.
  
  Lemma lookup_None {A : Type}:
    forall (r : string) (ls : list (string * A)),
      lookup String.eqb r ls = None -> ~In r (map fst ls).
  Proof.
    induction ls; intros; unfold lookup in H.
    - intro P; inv P.
    - intro P; destruct P.
      + destruct find eqn:G; [discriminate|].
        cbn [find] in G.
        destruct String.eqb eqn:G0;[discriminate|].
        rewrite String.eqb_neq in G0.
        apply G0; rewrite H0; reflexivity.
      + cbn [find] in H.
        destruct String.eqb eqn:G0;[discriminate|].
        apply IHls; auto.
  Qed.
  
  Lemma SFActionT_correct :
    forall lret m (a : ActionT _ lret),
      SigMatch_ActionT (getMethods m) a = [] -> SFActionT (getMethods m) a.
  Proof.
    induction a; intros.
    - econstructor; intros.
      + destruct v.
        inv H0.
        apply app_eq_nil in H2; dest.
        apply (H _ H1).
      + apply app_eq_nil in H0; dest.
        destruct lookup eqn:G.
        * destruct s0.
          destruct Signature_dec; [|discriminate]; subst.
          apply lookup_In', (in_map (fun x => (fst x, projT1 (snd x)))) in G.
          assumption.
        * exfalso.
          apply lookup_None in G.
          contradiction.
    - destruct k; inv H0; econstructor; intros.
      simpl in v; destruct v; eauto.
    - inv H0.
      apply app_eq_nil in H2; dest.
      econstructor; intros; eauto.
      destruct v.
      apply H; assumption.
    - destruct k; inv H0; econstructor; intros.
      simpl in v; destruct v; eauto.
    - destruct k; inv H0; econstructor; intros.
      simpl in v; destruct v; eauto.
    - inv H; econstructor; eauto.
    - inv H0.
      apply app_eq_nil in H2; dest.
      apply app_eq_nil in H1; dest.
      econstructor; intros; eauto.
      destruct v; eauto.
    - inv H.
      econstructor; eauto.
    - econstructor.
  Qed.
End Proofs.
