Require Import Lib.EclecticLib Syntax Properties.

Ltac discharge_string_dec := destruct_string_dec; discharge_append.

Ltac discharge_NoSelfCall :=
  unfold NoSelfCallBaseModule, NoSelfCallRulesBaseModule, NoSelfCallMethsBaseModule; split; auto; simpl; intros;
  repeat match goal with
         | H: _ \/ _ |- _ => destruct H; subst
         | H: False |- _ => exfalso; apply H
         | |- NoCallActionT _ (convertLetExprSyntax_ActionT _) => apply LetExprNoCallActionT
         | _ => constructor; auto; simpl; try intro; discharge_DisjKey
         end.

Ltac discharge_SemAction :=
  repeat match goal with
         | |- SemAction _ (If ?p then _ else _ as _; _)%kami_action _ _ _ _ => eapply SemAction_if
         | |- if ?P then SemAction _ _ _ _ _ _ else SemAction _ _ _ _ _ _ =>
           case_eq P; let H := fresh in intros H; rewrite ?H in *; try discriminate
         | |- SemAction _ (convertLetExprSyntax_ActionT _) _ _ _ _ => eapply convertLetExprSyntax_ActionT_same
         | |- SemAction _ _ _ _ _ _ => econstructor
         end;
  rewrite ?key_not_In_fst; unfold not; simpl; try tauto; simpl; intros; discharge_DisjKey.








Local Ltac discharge_init :=
  repeat econstructor;
  try match goal with
      | |- match ?P in _ = Y return _ with
           | eq_refl => _
           end = _ => is_evar P; match type of P with
                                 | ?tp = _ => unify P (@eq_refl _ tp)
                                 end
      end; simpl; eauto.

Ltac clean_hyp :=
  simpl in *;
  repeat match goal with
         | |- NoSelfCallBaseModule _ => discharge_NoSelfCall
         | H: DisjKey _ _ |- _ => clear H
         | H: key_not_In _ _ |- _ => clear H
         | H: ?a = ?a |- _ => clear H
         | H: ?a <> ?b |- _ => clear H
         | H: False |- _ => exfalso; apply H
         | H: ?a <> ?a |- _ => exfalso; apply (H eq_refl)
         | H: _ \/ _ |- _ => destruct H; subst
         | H: _ /\ _ |- _ => destruct H; subst
         | H: exists x, _ |- _ => destruct H
         | H: (?A, ?B) = (?P, ?Q) |- _ =>
           apply inversionPair in H; destruct H as [? ?]; subst
         | H: existT ?a ?b ?c1 = existT ?a ?b ?c2 |- _ => apply Eqdep.EqdepTheory.inj_pair2 in H; subst
         | H: existT ?a ?b1 ?c1 = existT ?a ?b2 ?c2 |- _ => apply inversionExistT in H;
                                                            destruct H as [? ?]; subst
         | H: (?a ++ ?b)%string = (?a ++ ?c)%string |- _ =>
           apply append_remove_prefix in H; subst
         | H: ?a = ?b |- _ => discriminate
         | H: SemAction _ (convertLetExprSyntax_ActionT ?e) _ _ _ _ |- _ =>
           apply convertLetExprSyntax_ActionT_full in H
         | H: SemAction _ _ _ _ _ _ |- _ =>
           apply inversionSemAction in H
         | H: if ?P then _ else _ |- _ => case_eq P; let i := fresh in intros i; rewrite ?i in *
         | H: Forall2 _ _ _ |- _ => inv H; dest
         | H: RegT |- _ => destruct H as [? [? ?]];
                           repeat (unfold fst, snd, projT1, projT2 in *; subst)
         | H: In _ _ |- _ => simpl in H
         | |- exists rspec : list RegT,
             Forall2 _ _ _ /\ _ _ _ => discharge_init
         end.

Ltac discharge_CommonRegister disjReg :=
  match goal with
  | |- exists k: string, _ /\ _ =>
    exists disjReg; simpl; auto; tauto
  | _ => idtac
  end.

Ltac discharge_CommonRegisterAuto :=
  match goal with
  | |- exists k: string, _ /\ _ =>
    eexists; simpl; eauto; tauto
  | _ => idtac
  end.

Ltac discharge_simulationGeneral mySimRel :=
  apply simulationGeneral with (simRel := mySimRel); auto; simpl; intros;
  try match goal with
      | H: mySimRel _ _ |- _ => inv H
      end;
  clean_hyp; auto; clean_hyp.



Notation sz := 5.

Section Named.
  Variable name: string.
  Local Notation "^ x" := (name ++ "." ++ x)%string (at level 0).

    Definition IncrementerImpl :=
      MODULE_WF {
          Register ^"counter" : Bit sz <- Default
            with Register ^"counter1" : Bit sz <- Default
            with Register ^"isSending" : Bool <- true
                                             
            with Rule ^"send" :=
            ( Read isSending: Bool <- ^"isSending" ;
                Assert #isSending ;
                Read counter: Bit sz <- ^"counter" ;
                Call "counterVal"(#counter: _);
                Write ^"isSending" <- !#isSending ;
                Retv )

            with Rule ^"inc" :=
              ( Read isSending: Bool <- ^"isSending" ;
                  Assert !#isSending ;
                  Read counter: Bit sz <- ^"counter" ;
                  Write ^"counter" <- #counter + $1;
                  Write ^"isSending" <- !#isSending ;
                  Retv )
        }.

  Definition IncrementerSpec :=
    MODULE_WF {
        Register ^"counter" : Bit sz <- Default
          with Register ^"counter1" : Bit sz <- Default
                                         
          with Rule ^"send_and_inc" :=
          ( Read counter: Bit sz <- ^"counter" ;
              Call "counterVal"(#counter: _);
              Write ^"counter" <- #counter + $1;
              Retv)
      }.

  Record Incrementer_invariant (impl spec: RegsT) : Prop :=
    { counterImpl: word sz ;
      isSending: bool ;
      implEq : impl = (^"counter", existT _ (SyntaxKind (Bit sz)) counterImpl)
                        :: (^"counter1", existT _ (SyntaxKind (Bit sz)) $0)
                        :: (^"isSending", existT _ (SyntaxKind Bool) isSending) :: nil ;
      specEq : spec = (^"counter", existT _ (SyntaxKind (Bit sz))
                                         (if isSending then counterImpl else counterImpl ^+ $1))
                        :: (^"counter1", existT  _ (SyntaxKind (Bit sz)) $0)
                        :: nil
    }.
End Named.

Theorem Incrementer_TraceInclusion (name: string) :
  TraceInclusion (Base (IncrementerImpl name)) (Base (IncrementerSpec name)).
Proof.
  discharge_simulationGeneral (Incrementer_invariant name); discharge_CommonRegisterAuto.
  - right; do 2 (do 2 eexists; repeat split; eauto; simpl in * ).
    + discharge_SemAction; subst; auto.
    + repeat discharge_string_dec.
      repeat (econstructor; eauto; simpl; subst).
      rewrite wzero_wplus; auto.
  - left; split; auto; simpl in *.
    discharge_string_dec.
    repeat (econstructor; eauto; simpl; subst).
    rewrite negb_true_iff in *; subst.
    rewrite wzero_wplus; simpl; auto.
Qed.
