Require Import Kami.Lib.EclecticLib Kami.Syntax Kami.Properties Kami.Notations.

Lemma string_dec_refl {A} : forall (s: string) (T E: A),
  (if String.eqb s s then T else E) = T.
Proof.
  intros; rewrite String.eqb_refl; auto.
Qed.

Lemma string_dec_neq {A} : forall (s1 s2: string) (T E: A),
  s1 <> s2 ->
  (if String.eqb s1 s2 then T else E) = E.
Proof.
  intros.
  rewrite <- String.eqb_neq in H; rewrite H; auto.
Qed.

Ltac discharge_string_dec :=
  repeat (rewrite string_dec_refl || rewrite string_dec_neq by (intros ?; discharge_append)).

Ltac discharge_NoSelfCall :=
  unfold NoSelfCallBaseModule, NoSelfCallRulesBaseModule, NoSelfCallMethsBaseModule; split; auto; simpl; intros;
  repeat match goal with
         | H: _ \/ _ |- _ => destruct H; subst
         | H: False |- _ => exfalso; apply H
         | |- NoCallActionT _ (convertLetExprSyntax_ActionT _) => apply LetExprNoCallActionT
         | _ => constructor; auto; simpl; try intro; discharge_DisjKey
         end.

Ltac discharge_SemAction :=
  match goal with
  | |- SemAction _ _ _ _ ?meths _ =>
    repeat match goal with
           | |- SemAction _ (If ?p then _ else _ as _; _)%kami_action _ _ _ _ => eapply SemAction_if_split
           | |- if ?P then SemAction _ _ _ _ _ _ else SemAction _ _ _ _ _ _ =>
             case_eq P; let H := fresh in intros H; rewrite ?H in *; cbn [evalExpr] in *; try discriminate
           | |- SemAction _ (convertLetExprSyntax_ActionT _) _ _ _ _ => eapply convertLetExprSyntax_ActionT_same
           | |- SemAction _ _ _ _ _ _ => econstructor
           end;
    rewrite ?key_not_In_fst; unfold not; intros; cbn [evalExpr evalConstT] in *;
    repeat match goal with
           | |- In _ _ => simpl; auto
           | |- ?a = ?a => reflexivity
           | |- meths = _ => eauto
           end; simpl in *; try (discriminate || congruence); eauto; simpl in *; discharge_DisjKey
  end.

Ltac simplify_simulatingRule name :=
  right;
  exists name;
  eexists; split; [eauto| do 2 eexists; split; [discharge_SemAction|]].

Ltac simplify_nilStep :=
  left; split; auto; simpl in *;
  discharge_string_dec.

Local Ltac discharge_init :=
  repeat econstructor;
  try match goal with
      | |- match ?P in _ = Y return _ with
           | eq_refl => _
           end = _ => is_evar P; match type of P with
                                 | ?tp = _ => unify P (@eq_refl _ tp)
                                 end
      end; simpl; eauto.

Ltac clean_hyp_step :=
  match goal with
  | |- NoSelfCallBaseModule _ => discharge_NoSelfCall
  | H: DisjKey _ _ |- _ => clear H
  | H: key_not_In _ _ |- _ => clear H
  | H: ?a = ?a |- _ => clear H
  | H: False |- _ => exfalso; apply H
  | H: ?a <> ?a |- _ => exfalso; apply (H eq_refl)
  | H: _ \/ _ |- _ => destruct H; subst
  | H: _ /\ _ |- _ => destruct H; subst
  | H: exists x, _ |- _ => let y := fresh x in destruct H as [y ?]
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

Ltac clean_hyp := simpl in *; repeat clean_hyp_step.

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

Ltac discharge_simulationWf mySimRel :=
  apply simulationGeneral with (simRel := mySimRel); auto; simpl; intros;
  try match goal with
      | H: mySimRel _ _ |- _ => inv H
      end;
  clean_hyp; auto; clean_hyp.

Ltac discharge_simulation mySimRel :=
  apply simulation with (simRel := mySimRel); auto; simpl; intros;
  try match goal with
      | |- WfBaseModule _ => discharge_wf
      | H: mySimRel _ _ |- _ => inv H
      end;
  clean_hyp; auto; clean_hyp.
