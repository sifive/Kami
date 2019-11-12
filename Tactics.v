Require Import Kami.Lib.EclecticLib Kami.Syntax Kami.Properties.
Require Import List.

Ltac struct_get_field_ltac packet name :=
  let val := eval cbv in (struct_get_field_index packet name) in
      match val with
      | Some ?x => exact (ReadStruct packet x)
      | None =>
        let newstr := constr:(("get field not found in struct" ++ name)%string) in
        fail 0 newstr
      | _ =>
        let newstr := constr:(("major error - struct_get_field_index not reducing " ++ name)%string) in
        fail 0 newstr
      end.

Ltac struct_set_field_ltac packet name newval :=
  let val := eval cbv in (struct_get_field_index packet name) in
      match val with
      | Some ?x => exact (UpdateStruct packet x newval)
      | None =>
        let newstr := constr:(("set field not found in struct " ++ name)%string) in
        fail 0 newstr
      | _ =>
        let newstr := constr:(("major error - struct_set_field_index not reducing " ++ name)%string) in
        fail 0 newstr
      end.


Local Ltac constructor_simpl :=
  econstructor; eauto; simpl; unfold not; intros.

Ltac destruct_string_dec :=
  repeat match goal with
         | H: context[string_dec ?P%string ?Q%string] |- _ =>
           destruct (string_dec P Q)
         | |- context[string_dec ?P%string ?Q%string] =>
           destruct (string_dec P Q)
         end.

Local Ltac process_append :=
  repeat match goal with
         | H: (_ ++ _)%string = (_ ++ _)%string |- _ =>
           rewrite <- ?append_assoc in H; cbn [append] in H
         | |- (_ ++ _)%string = (_ ++ _)%string =>
           rewrite <- ?append_assoc; cbn [append]
         end;
  repeat match goal with
         | H: (?a ++ ?b)%string = (?a ++ ?c)%string |- _ =>
           apply append_remove_prefix in H; subst
         | H: (?a ++ ?b)%string = (?c ++ ?b)%string |- _ =>
           apply append_remove_suffix in H; subst
         | |- (?a ++ ?b)%string = (?a ++ ?c)%string =>
           apply append_remove_prefix
         | |- (?a ++ ?b)%string = (?c ++ ?b)%string =>
           apply append_remove_suffix
         | H: (?a ++ (String ?x ?b))%string = (?c ++ (String ?y ?d))%string |- _ =>
           apply (f_equal string_rev) in H;
           rewrite (string_rev_append a (String x b)), (string_rev_append c (String y d)) in H;
           cbn [string_rev] in H;
           rewrite <- ?append_assoc in H; cbn [append] in H
         end.

Local Ltac finish_append :=
  auto; try (apply InSingleton || discriminate || tauto || congruence).

Ltac discharge_append :=
  simpl; unfold getBool in *; process_append; finish_append.

Goal forall (a b c: string),
  (a ++ "a" <> a ++ "b"
  /\ a ++ "a" ++ b <> c ++ "b" ++ b
  /\ a ++ "a" ++ "b" <> a ++ "a" ++ "c"
  /\ "a" ++ a <> "b" ++ b
  /\ (a ++ "a") ++ b <> a ++ "b" ++ a
  /\ (a ++ (b ++ "b")) ++ "c" <> (a ++ b) ++ "d")%string.
Proof. intuition idtac; discharge_append. Qed.

Theorem DisjKey_nil2: forall A B (l: list (A*B)), DisjKey l List.nil.
Proof.
  intros.
  unfold DisjKey.
  intros.
  right.
  simpl.
  intro X.
  elim X.
Qed.

Theorem DisjKey_nil1: forall A B (l: list (A*B)), DisjKey List.nil l.
Proof.
  intros.
  unfold DisjKey.
  intros.
  left.
  simpl.
  intro X.
  elim X.
Qed.

Ltac trivialSolve :=
    match goal with
    | |- forall _, In _ (getAllRules (Base (BaseRegFile _))) -> _ => simpl;intros;trivialSolve
    | H: False |- _ => elim H
    (*| |- DisjKey _ List.nil => apply DisjKey_nil2 
    | |- DisjKey List.nil _ => apply DisjKey_nil1
    | |- DisjKeyWeak _ List.nil => rewrite <- DisjKeyWeak_same;[apply DisjKey_nil2 | repeat (decide equality)]
    | |- DisjKeyWeak List.nil _ => rewrite <- DisjKeyWeak_same;[apply DisjKey_nil1 | repeat (decide equality)]*)
    | |- ~ (List.In _ _) => progress(simpl);trivialSolve
    | |- ~ (_ \/ _) => let X := fresh in intro X;inversion X;subst;clear X;trivialSolve
    | |- _ /\ _ => split;trivialSolve
    | |- ~False => let X := fresh in intro X;inversion X
    (*| |- (_++_)%string <> (_++_)%string => let X := fresh in try (intro X;apply string_equal_prefix in X; inversion X)*)
    (*| |- ~((?P++_)%string = _ \/ False) \/ ~((?P++_)%string = _ \/ False) => let X := fresh in try (apply or_diff;intro X;inversion X)*)
    | |- NoDup (_::_) => econstructor; simpl; trivialSolve
    | |- NoDup [] => econstructor
    | H: _ \/ _ |- _ => inversion H;subst;clear H;trivialSolve
    (*| H: (?P++_)%string=(?P++_)%string |- _ => apply string_equal_prefix in H;inversion H;subst;clear H;trivialSolve*)
    | H: In _ (map fst _) |- _ => progress(simpl in H);trivialSolve
    | |- (?P = ?P) => reflexivity
    | |- _ => discharge_append
    | _ => idtac
    end.

  Theorem DisjKey_Cons1:
    forall T Q (a:(T*Q)) x z (W:forall (a1:T) (a2:T), {a1=a2}+{a1<>a2}),
           DisjKey (a::x) z <-> ((~(List.In (fst a) (List.map fst z))) /\ DisjKey x z).
  Proof.
    intros.
    rewrite ?DisjKeyWeak_same.
    split.
    + intros.
      split.
      - unfold DisjKeyWeak in H.
        assert (List.In (fst a) (List.map fst (a::x)) -> List.In (fst a) (List.map fst z) -> False).
        apply H.
        intro X.
        apply H0.
        simpl.
        left.
        reflexivity.
        apply X.
      - simpl.
        intros.
        unfold DisjKeyWeak in H.
        unfold DisjKeyWeak.
        intros.
        assert (List.In k (List.map fst (a::x)) -> List.In k (List.map fst z) -> False).
        apply H.
        apply H2.
        simpl.
        right.
        apply H0.
        apply H1.
    + intros.
      inversion H; subst; clear H.
      unfold DisjKeyWeak.
      unfold DisjKeyWeak in H1.
      intros.
      assert (List.In k (List.map fst x) -> List.In k (List.map fst z) -> False).
      apply H1.
      simpl in H.
      inversion H;subst;clear H.
      - apply H0.
        apply H2.
      - apply H3.
        apply H4.
        apply H2.
    + apply W.
    + apply W.
Qed.

Theorem DisjKey_Cons2:
    forall T Q (a:(T*Q)) x z (W:forall (a1:T) (a2:T), {a1=a2}+{a1<>a2}),
           DisjKey x (a::z) <-> ((~(List.In (fst a) (List.map fst x))) /\ DisjKey x z).
Proof.
    intros.
    rewrite ?DisjKeyWeak_same.
    split.
    + intros.
      split.
      - intros.
        unfold DisjKeyWeak in H.
        assert (List.In (fst a) (List.map fst x) -> List.In (fst a) (List.map fst (a::z)) -> False).
        apply H.
        intro X.
        apply H0.
        apply X.
        simpl.
        left.
        reflexivity.
      - simpl.
        intros.
        unfold DisjKeyWeak in H.
        unfold DisjKeyWeak.
        intros.
        assert (List.In k (List.map fst x) -> List.In k (List.map fst (a::z)) -> False).
        apply H.
        apply H2.
        apply H0.
        simpl.
        right.
        apply H1.
    + intros.
      inversion H; subst; clear H.
      unfold DisjKeyWeak.
      unfold DisjKeyWeak in H1.
      intros.
      inversion H2;subst;clear H2.
      - apply H0 in H.
        inversion H.
      - assert (List.In k (List.map fst x) -> List.In k (List.map fst z) -> False).
        apply H1.
        apply H2.
        apply H.
        apply H3.
    +  apply W.
    + apply W.
Qed.

Theorem DisjKey_NubBy1: forall T (x: list (string * T)) (y: list (string * T)), DisjKey x y -> DisjKey (nubBy (fun '(a,_) '(b,_) => String.eqb a b) x) y.
Proof.
    intros  T x y.
    generalize y.
    induction x.
    + simpl.
      intros.
      apply H.
    + simpl.
      remember (
        existsb (let '(a0, _) := a in fun '(b, _) => a0 =? b)
         (nubBy (fun '(a0, _) '(b, _) => a0 =? b) x)).
      destruct b.
      - simpl.
        intros.
        apply IHx.
        unfold DisjKey in H.
        simpl in H.
        unfold DisjKey.
        intros.
        assert(
          ~ (fst a = k \/ In k (map fst x)) \/ ~ In k (map fst y0)
        ).
        ++ apply H.
        ++ inversion H0;subst;clear H0.
           -- left.
              intro X. 
              apply H1.
              right.
              apply X.
           -- right.
              apply H1.
      - intros.
        rewrite DisjKey_Cons1.
        rewrite DisjKey_Cons1 in H.
        inversion H;subst;clear H.
        split.
        ++ apply H0.
        ++ apply IHx.
           apply H1.
        ++ repeat (decide equality).
        ++ repeat (decide equality).
Qed.

Theorem DisjKey_NubBy2: forall T (x: list (string * T)) (y: list (string * T)), DisjKey x y -> DisjKey x (nubBy (fun '(a,_) '(b,_) => String.eqb a b) y).
Proof.
    intros T x y.
    generalize x.
    induction y.
    + simpl.
      intros.
      apply H.
    + simpl.
      remember (
        existsb (let '(a0, _) := a in fun '(b, _) => a0 =? b)
          (nubBy (fun '(a0, _) '(b, _) => a0 =? b) y)).
      destruct b.
      - simpl.
        intros.
        apply IHy.
        unfold DisjKey in H.
        simpl in H.
        unfold DisjKey.
        intros.
        assert(
          ~ In k (map fst x0) \/ ~ (fst a = k \/ In k (map fst y))
        ).
        ++ apply H.
        ++ inversion H0; subst; clear H0.
           -- left.
              apply H1.
           -- right.
              intro X.
              apply H1.
              right.
              apply X.
      - intros.
        rewrite DisjKey_Cons2.
        rewrite DisjKey_Cons2 in H.
        inversion H;subst;clear H.
        split.
        ++ apply H0.
        ++ apply IHy.
           apply H1.
        ++ repeat (decide equality).
        ++ repeat (decide equality).
Qed.

Ltac discharge_DisjKey :=
  repeat match goal with
         | |- DisjKey _ (nubBy _) => apply DisjKey_NubBy2
         | |- DisjKey (nubBy _) _ => apply DisjKey_NubBy1
         | |- DisjKey _ _ =>
           rewrite (DisjKeyWeak_same string_dec); unfold DisjKeyWeak; let k := fresh in intro k; simpl; intros
         | H: _ \/ _ |- _ => destruct H; subst
         end; trivialSolve.

Ltac discharge_wf :=
  repeat match goal with
         | |- @WfMod _ => constructor_simpl
         | |- @WfConcat _ _ => constructor_simpl
         | |- _ /\ _ => constructor_simpl
         | |- @WfConcatActionT _ _ _ => constructor_simpl
         | |- @WfBaseModule _ => constructor_simpl
         | |- @WfActionT _ _ (convertLetExprSyntax_ActionT ?e) => apply WfLetExprSyntax
         | |- @WfActionT _ _ _ => constructor_simpl
         | |- NoDup _ => constructor_simpl
         | H: _ \/ _ |- _ => destruct H; subst; simpl
         | |- forall _, _ => intros
         | |- _ -> _ => intros 
         | H: In _ (getAllMethods _) |- _ => simpl in H;inversion H;subst;clear H;simpl
         end;
  discharge_DisjKey.

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

Ltac unfold_beta_head a :=
  let new :=
      lazymatch a with
      | ?h _ _ _ _ _ _ _ _ _ _ => eval cbv beta delta [h] in a
      | ?h _ _ _ _ _ _ _ _ _ => eval cbv beta delta [h] in a
      | ?h _ _ _ _ _ _ _ _ => eval cbv beta delta [h] in a
      | ?h _ _ _ _ _ _ _ => eval cbv beta delta [h] in a
      | ?h _ _ _ _ _ _ => eval cbv beta delta [h] in a
      | ?h _ _ _ _ _ => eval cbv beta delta [h] in a
      | ?h _ _ _ _ => eval cbv beta delta [h] in a
      | ?h _ _ _ => eval cbv beta delta [h] in a
      | ?h _ _ => eval cbv beta delta [h] in a
      | ?h _ => eval cbv beta delta [h] in a
      end in
    exact new.

Ltac discharge_SemAction :=
  match goal with
  | |- SemAction _ _ _ _ ?meths _ =>
    repeat match goal with
           | |- SemAction ?o ?act ?reads ?news ?calls ?retv =>
             let act' := constr:(ltac:(unfold_beta_head act)) in
             change (SemAction o act' reads news calls retv)
           | |- SemAction _ (@IfElse _ _ ?p _ _ _ _) _ _ _ _ => eapply SemAction_if_split
           | |- if ?P then SemAction _ _ _ _ _ _ else SemAction _ _ _ _ _ _ =>
             case_eq P;
             let H := fresh in
             intros H; rewrite ?H in *; cbn [evalExpr] in *; try discriminate
           | |- SemAction _ (convertLetExprSyntax_ActionT _) _ _ _ _ => eapply convertLetExprSyntax_ActionT_same
           | |- SemAction _ _ _ _ _ _ => econstructor
           end;
    rewrite ?key_not_In_fst; unfold not; intros; cbn [evalExpr evalConstT] in *;
    repeat match goal with
           | |- In _ _ => simpl; auto
           | |- ?a = ?a => reflexivity
           | |- meths = _ => eauto
           end;
    simpl in *; try (discriminate || congruence); eauto; simpl in *; discharge_DisjKey
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

