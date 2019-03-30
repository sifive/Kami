Require Import Lib.EclecticLib Syntax Properties.

Ltac discharge_appendage :=
  repeat match goal with
         | H: (?a ++ ?b)%string = (?a ++ ?c)%string |- _ =>
           rewrite append_remove_prefix in H; subst
         | H: (?a ++ ?b)%string = (?c ++ ?b)%string |- _ =>
           rewrite append_remove_suffix in H; subst
         | H: _ \/ _ |- _ => destruct H; subst
         end.

Ltac discharge_string_dec :=
  repeat match goal with
         | |- context[string_dec ?P ?Q] => destruct (string_dec P Q);
                                           discharge_appendage;
                                           try (tauto || congruence)
         end.

Ltac discharge_SemAction :=
  repeat match goal with
         | |- SemAction _ (If ?p then _ else _ as _; _)%kami_action _ _ _ _ => eapply SemAction_if
         | |- if ?P then SemAction _ _ _ _ _ _ else SemAction _ _ _ _ _ _ => case_eq P; let H := fresh in intros H; rewrite ?H in *; try discriminate
         | |- SemAction _ (convertLetExprSyntax_ActionT _) _ _ _ _ => eapply convertLetExprSyntax_ActionT_same
         | |- SemAction _ _ _ _ _ _ => econstructor
         end; rewrite ?key_not_In_fst in *; simpl in *; try tauto; simpl in *; unfold not; intros; rewrite ?DisjKeyWeak_same by apply string_dec;
  unfold DisjKeyWeak; intros; simpl in *;
  repeat match goal with
         | H: _ \/ _ |- _ => destruct H; discharge_appendage
         | H: False |- _ => exfalso; apply H
         | H: ?a = ?b |- _ => match type of a with
                              | string => try discriminate
                              end
         end.

Ltac discharge_DisjKey :=
  try match goal with
      | |- DisjKey ?P ?Q => rewrite DisjKeyWeak_same by apply string_dec;
                            unfold DisjKeyWeak; simpl; intros
      end;
  discharge_appendage;
  subst;
  auto;
  try discriminate.

Local Example test_normaldisj:
  DisjKey (map (fun x => (x, 1)) ("a" :: "b" :: "c" :: nil))%string
          (map (fun x => (x, 2)) ("d" :: "e" :: nil))%string.
Proof.
  simpl.
  discharge_DisjKey.
Qed.

Local Example test_prefix_disj a:
  DisjKey (map (fun x => ((a ++ x)%string, 1)) ("ab" :: "be" :: "cs" :: nil))%string
          (map (fun x => ((a ++ x)%string, 2)) ("de" :: "et" :: nil))%string.
Proof.
  simpl.
  discharge_DisjKey.
Qed.

Local Example test_suffix_disj a:
  DisjKey (map (fun x => ((x ++ a)%string, 1)) ("ab" :: "be" :: "cs" :: nil))%string
          (map (fun x => ((x ++ a)%string, 2)) ("de" :: "et" :: nil))%string.
Proof.
  simpl.
  discharge_DisjKey.
Qed.

Local Ltac clean_hyp :=
  repeat match goal with
         | H: @key_not_In _ _ _ _ |- _ => clear H
         end;
  repeat match goal with
         | H: DisjKey _ _ |- _ => apply DisjKeyWeak_same in H; [unfold DisjKeyWeak in H; simpl in H| apply string_dec]
         | H: In ?x ?ls |- _ =>
           apply (InFilter string_dec) in H; simpl in H; destruct H; [|exfalso; auto]
         | H: False |- _ => exfalso; apply H
         | H: (?A, ?B) = (?P, ?Q) |- _ =>
           let H1 := fresh in
           let H2 := fresh in
           pose proof (f_equal fst H) as H1;
           pose proof (f_equal snd H) as H2;
           simpl in H1, H2;
           clear H
         | H: ?A = ?A |- _ => clear H
         | H: (?a ++ ?b)%string = (?a ++ ?c)%string |- _ => rewrite append_remove_prefix in H; subst
         | H: (?a ++ ?b)%string = (?c ++ ?b)%string |- _ => rewrite append_remove_suffix in H; subst
         | H: existT ?a ?b ?c1 = existT ?a ?b ?c2 |- _ => apply Eqdep.EqdepTheory.inj_pair2 in H; subst
         | H: ?A = ?B |- _ => discriminate
         | H: SemAction _ (convertLetExprSyntax_ActionT ?e) _ _ _ _ |- _ =>
           apply convertLetExprSyntax_ActionT_full in H; dest; subst
         end.

Local Ltac destruct_RegT :=
  repeat match goal with
         | H: RegT |- _ =>
           destruct H as [? [? ?]]; simpl in *; repeat subst; simpl in *
         end.

Local Ltac destruct_Invariant mySimRel :=
  try match goal with
      | H: mySimRel _ _ |- _ => inv H
      end; clean_hyp.

Local Ltac discharge_init :=
  repeat econstructor; eauto; simpl;
  instantiate (1 := eq_refl); simpl; auto.

Ltac discharge_simulationZero mySimRel :=
  apply simulationZeroAction with (simRel := mySimRel); auto; simpl; intros; destruct_Invariant mySimRel; auto;
  (repeat match goal with
          | H: _ \/ _ |- _ => destruct H
          | H: False |- _ => exfalso; apply H
          | H: (?a, ?b) = (?c, ?d) |- _ =>
            let H2 := fresh in
            inversion H;
            pose proof (f_equal snd H) as H2;
            simpl in H2; subst; clear H; EqDep_subst
         | H: SemAction _ (convertLetExprSyntax_ActionT ?e) _ _ _ _ |- _ =>
           apply convertLetExprSyntax_ActionT_full in H; dest; subst
          | H: SemAction _ _ _ _ _ _ |- _ =>
            apply inversionSemAction in H; dest; subst
          | H: if ?P then _ else _ |- _ => case_eq P; let i := fresh in intros i; rewrite ?i in *; dest
          | H: Forall2 _ _ _ |- _ => inv H
          | H: ?a = ?a |- _ => clear H
          | H: match convertLetExprSyntax_ActionT ?P with
               | _ => _
               end |- _ =>
            case_eq P; intros;
            match goal with
            | H': P = _ |- _ => rewrite ?H' in *; simpl in *; try discriminate
            end
          end); dest; simpl in *; repeat subst; simpl in *; destruct_RegT;
  match goal with
  | |- exists rspec, _ => discharge_init
  | _ => idtac
  end.

Ltac discharge_NoSelfCall :=
  unfold NoSelfCallBaseModule, NoSelfCallRulesBaseModule, NoSelfCallMethsBaseModule; split; auto; simpl; intros;
  repeat match goal with
         | H: _ \/ _ |- _ => destruct H; subst; simpl in *
         | H: False |- _ => exfalso; apply H
         | |- NoCallActionT _ (convertLetExprSyntax_ActionT _) => apply LetExprNoCallActionT
         | _ => constructor; auto; simpl; try intro; discharge_DisjKey
         end.

Ltac discharge_simulationGeneral mySimRel disjReg :=
  apply simulationGeneral with (simRel := mySimRel); auto; simpl; intros; destruct_Invariant mySimRel; auto;
  (repeat match goal with
          | H: _ \/ _ |- _ => destruct H
          | H: False |- _ => exfalso; apply H
          | H: (?a, ?b) = (?c, ?d) |- _ =>
            let H2 := fresh in
            inversion H;
            pose proof (f_equal snd H) as H2;
            simpl in H2; subst; clear H; EqDep_subst
         | H: SemAction _ (convertLetExprSyntax_ActionT ?e) _ _ _ _ |- _ =>
           apply convertLetExprSyntax_ActionT_full in H; dest; subst
          | H: SemAction _ _ _ _ _ _ |- _ =>
            apply inversionSemAction in H; dest; subst
          | H: if ?P then _ else _ |- _ => case_eq P; let i := fresh in intros i; rewrite ?i in *; dest
          | H: Forall2 _ _ _ |- _ => inv H
          | |- exists k, In k _ /\ In k _ =>
            exists disjReg; rewrite ?map_app, ?in_app_iff; simpl; tauto
          | H: ?a = ?a |- _ => clear H
          | H: match convertLetExprSyntax_ActionT ?P with
               | _ => _
               end |- _ =>
            case_eq P; intros;
            match goal with
            | H': P = _ |- _ => rewrite ?H' in *; simpl in *; try discriminate
            end
          end); dest; simpl in *; repeat subst; simpl in *; destruct_RegT;
  match goal with
  | |- exists rspec, _ => discharge_init
  | _ => idtac
  end.





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

(*
Theorem Incrementer_TraceInclusion (name: string) :
  TraceInclusion (Base (IncrementerImpl name)) (Base (IncrementerSpec name)).
Proof.
  apply simulationZeroAction with (simRel := (Incrementer_invariant name)); auto; simpl; intros; destruct_Invariant (Incrementer_invariant name); auto.
  (repeat match goal with
          | H: _ \/ _ |- _ => destruct H
          | H: False |- _ => exfalso; apply H
          | H: (?a, ?b) = (?c, ?d) |- _ =>
            let H2 := fresh in
            inversion H;
            pose proof (f_equal snd H) as H2;
            simpl in H2; subst; clear H; EqDep_subst
         | H: SemAction _ (convertLetExprSyntax_ActionT ?e) _ _ _ _ |- _ =>
           apply convertLetExprSyntax_ActionT_full in H; dest; subst
          | H: SemAction _ _ _ _ _ _ |- _ =>
            apply inversionSemAction in H; dest; subst
          | H: if ?P then _ else _ |- _ => case_eq P; let i := fresh in intros i; rewrite ?i in *; dest
          | H: Forall2 _ _ _ |- _ => inv H
          | H: ?a = ?a |- _ => clear H
          | H: match convertLetExprSyntax_ActionT ?P with
               | _ => _
               end |- _ =>
            case_eq P; intros;
            match goal with
            | H': P = _ |- _ => rewrite ?H' in *; simpl in *; try discriminate
            end
          end); dest; simpl in *; repeat subst; simpl in *; destruct_RegT.
  match goal with
  | |- exists rspec: list RegT, _ => discharge_init
  | _ => idtac
  end.
  (repeat match goal with
          | H: In ?x ?ls |- _ =>
            apply (InFilter string_dec) in H; simpl in H; destruct H; [|exfalso; auto]
          | H: _ \/ _ |- _ => destruct H
          | H: False |- _ => exfalso; apply H
          | H: (?a, ?b) = (?c, ?d) |- _ =>
            let H2 := fresh in
            inversion H;
            pose proof (f_equal snd H) as H2;
            simpl in H2; subst; clear H; EqDep_subst
          | H: SemAction _ (convertLetExprSyntax_ActionT ?e) _ _ _ _ |- _ =>
           apply convertLetExprSyntax_ActionT_full in H; dest; subst
          | H: SemAction _ _ _ _ _ _ |- _ =>
            apply inversionSemAction in H; dest; subst
          | H: if ?P then _ else _ |- _ => case_eq P; let i := fresh in intros i; rewrite ?i in *; dest
          | H: Forall2 _ _ _ |- _ => inv H
          | H: ?a = ?a |- _ => clear H
          | H: match convertLetExprSyntax_ActionT ?P with
               | _ => _
               end |- _ =>
            case_eq P; intros;
            match goal with
            | H': P = _ |- _ => rewrite ?H' in *; simpl in *; try discriminate
            end
          end).
  match goal with
  | H: In ?x ?ls |- _ =>
    apply (InFilter string_dec) in H; simpl in H; try (destruct H; [|exfalso; auto])
  end.
  dest; simpl in *; repeat subst; simpl in *; destruct_RegT.
  
  - repeat econstructor; eauto; simpl;
    instantiate (1 := eq_refl); simpl; auto.
    repeat match goal with
           | |- match ?pf in _ = Y return (fullType type Y) with
                | eq_refl => ?P
                end = ?P => instantiate (1 := eq_refl)
           end.
    instantiate (1 := eq_refl); simpl; auto.
    econstructor; eauto; simpl; auto.
    econstructor; eauto; simpl; auto.
    econstructor; eauto; simpl; auto.
    econstructor; eauto; simpl; auto.
    Focus 2.
    match goal with
    | |- exists pf: _ = _, _ => exists eq_refl
    end.
            
    simpl.
    constructor.
    destruct x; simpl in *; subst.
    destruct x0; simpl in *; subst.
    destruct s0; simpl in *; repeat subst. subst.
    destruct x2.
    match goal with
    | H: match ?x in (_ = Y) return fullType type Y with
         | eq_refl => projT2 _
         end = _ |- _ => destruct x
    end.

    (* Initial values *)
    destruct x, x0, s0, s2; simpl in *; subst; subst.
    exists (("counter", existT _ (SyntaxKind (Bit sz)) (wzero 5)) :: nil); simpl in *.
    split.
    + repeat constructor; simpl.
      exists eq_refl; auto.
    + apply Build_Incrementer_invariant with (counterImpl := (wzero 5)) (isSending := true); auto.
  - (* Rule send - corresponds to rule send_and_inc in Spec, so "right" *)
    right; do 2 eexists; repeat split; eauto; simpl in *.
    inv H1.
    clean_hyp.
    do 2 eexists; repeat split; eauto; simpl in *.
    + discharge_SemAction.
    + econstructor; eauto; simpl.
      repeat f_equal.
      apply wzero_wplus.
  - (* Rule inc - corresponds to nothing in Spec, so "left" *)
    left; split; auto; simpl in *.
    inv H1.
    clean_hyp.
    discharge_string_dec.
    rewrite negb_true_iff in *; subst.
    econstructor; repeat (simpl; eauto).
    rewrite wzero_wplus; auto.
Qed.
*)