Require Import Lib.EclecticLib Syntax Properties.

Ltac discharge_NoSelfCall :=
  unfold NoSelfCallBaseModule, NoSelfCallRulesBaseModule, NoSelfCallMethsBaseModule; split; auto; simpl; intros;
  repeat match goal with
         | H: _ \/ _ |- _ => destruct H; subst; simpl in *
         | H: False |- _ => exfalso; apply H
         | |- NoCallActionT _ (convertLetExprSyntax_ActionT _) => apply LetExprNoCallActionT
         | _ => constructor; auto; simpl; try intro; discharge_DisjKey
         end.

Ltac discharge_simulationGeneral mySimRel disjReg :=
  apply simulationGeneral with (simRel := mySimRel); auto; simpl; intros;
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
          end); dest; simpl in *; repeat subst; simpl in *.

Ltac clean_hyp :=
  simpl in *;
  repeat match goal with
         | H: DisjKey _ _ |- _ => apply DisjKeyWeak_same in H; [unfold DisjKeyWeak in H; simpl in H| apply string_dec]
         (* | H: In ?x ?ls |- _ => *)
         (*   apply (InFilterPair string_dec) in H; simpl in H; destruct H; [|exfalso; auto] *)
         | H: _ \/ _ |- _ => destruct H; subst
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

(* Ltac discharge_SemAction := *)
(*   (repeat match goal with                              *)
(*           | H: SemAction _ (convertLetExprSyntax_ActionT ?e) _ _ _ _ |- _ => *)
(*             apply convertLetExprSyntax_ActionT_full in H; dest; subst *)
(*           | H: SemAction _ _ _ _ _ _ |- _ => *)
(*             apply inversionSemAction in H; dest; subst *)
(*           | H: if ?P then _ else _ |- _ => case_eq P; let i := fresh in intros i; rewrite ?i in *; dest *)
(*           | H: key_not_In _ _ |- _ => clear H *)
(*           | H: DisjKey _ _ |- _ => clear H *)
(*           end); *)
(*   repeat match goal with *)
(*          | H: In (?a, _) ?ls |- _ => *)
(*            let HF := fresh in *)
(*            rewrite (InFilterPair string_dec) in H; simpl in H; discharge_append; *)
(*            apply InSingleton_impl in H; subst *)
(*          | H: ?a = ?a |- _ => clear H *)
(*          | H: ?a <> ?a |- _ => exfalso; apply (H eq_refl) *)
(*          | H: (_, existT _ _ _) = (_, existT _ _ _) |- _ => *)
(*            apply inversionExistT in H; destruct H as [? ?] *)
(*          | H: existT ?a ?b ?c1 = existT ?a ?b ?c2 |- _ => apply Eqdep.EqdepTheory.inj_pair2 in H; subst *)
(*          | H: ?a <> ?b |- _ => clear H *)
(*          end. *)

(* Local Ltac clean_hyp := *)
(*   repeat match goal with *)
(*          | H: @key_not_In _ _ _ _ |- _ => clear H *)
(*          end; *)
(*   repeat match goal with *)
(*          | H: DisjKey _ _ |- _ => apply DisjKeyWeak_same in H; [unfold DisjKeyWeak in H; simpl in H| apply string_dec] *)
(*          | H: In ?x ?ls |- _ => *)
(*            apply (InFilterPair string_dec) in H; simpl in H; destruct H; [|exfalso; auto] *)
(*          | H: False |- _ => exfalso; apply H *)
(*          | H: (?A, ?B) = (?P, ?Q) |- _ => *)
(*            let H1 := fresh in *)
(*            let H2 := fresh in *)
(*            pose proof (f_equal fst H) as H1; *)
(*            pose proof (f_equal snd H) as H2; *)
(*            simpl in H1, H2; *)
(*            clear H *)
(*          | H: ?A = ?A |- _ => clear H *)
(*          | H: (?a ++ ?b)%string = (?a ++ ?c)%string |- _ => rewrite append_remove_prefix in H; subst *)
(*          | H: (?a ++ ?b)%string = (?c ++ ?b)%string |- _ => rewrite append_remove_suffix in H; subst *)
(*          | H: existT ?a ?b ?c1 = existT ?a ?b ?c2 |- _ => apply Eqdep.EqdepTheory.inj_pair2 in H; subst *)
(*          | H: ?A = ?B |- _ => discriminate *)
(*          | H: SemAction _ (convertLetExprSyntax_ActionT ?e) _ _ _ _ |- _ => *)
(*            apply convertLetExprSyntax_ActionT_full in H; dest; subst *)
(*          end. *)

(* Local Ltac destruct_RegT := *)
(*   repeat match goal with *)
(*          | H: RegT |- _ => *)
(*            destruct H as [? [? ?]]; simpl in *; repeat subst; simpl in * *)
(*          end. *)

(* Local Ltac discharge_init := *)
(*   repeat econstructor; eauto; simpl; *)
(*   instantiate (1 := eq_refl); simpl; auto. *)

(* Local Ltac simplify_Ins := *)
(*   repeat match goal with *)
(*          | H: In _ (getRules _) |- _ => simpl in H *)
(*          | H: In _ (getMethods _) |- _ => simpl in H *)
(*          | H: _ \/ _ |- _ => destruct H *)
(*          | H: False |- _ => exfalso; apply H *)
(*          | H: (_, _) = (_, _) |- _ => inv H *)
(*          | H: (_, _) = ?a |- _ => try subst a *)
(*          end. *)

(* Ltac discharge_NoSelfCall := *)
(*   unfold NoSelfCallBaseModule, NoSelfCallRulesBaseModule, NoSelfCallMethsBaseModule; split; auto; intros; *)
(*   simplify_Ins; *)
(*   repeat match goal with *)
(*          | |- NoCallActionT _ (convertLetExprSyntax_ActionT _) => apply LetExprNoCallActionT *)
(*          | _ => constructor; auto; cbn - [In]; try rewrite (InFilter string_dec); simpl; unfold getBool, not; intros; *)
(*                 try (rewrite (DisjKey_filter string_dec)); discharge_append *)
(*          end. *)
(*   (* unfold NoSelfCallBaseModule, NoSelfCallRulesBaseModule, NoSelfCallMethsBaseModule; split; auto; intros; *) *)
(*   (* simplify_Ins; *) *)
(*   (* repeat match goal with *) *)
(*   (*        | |- NoCallActionT _ (convertLetExprSyntax_ActionT _) => apply LetExprNoCallActionT *) *)
(*   (*        | _ => constructor; auto; simpl; try intro; try (rewrite (DisjKey_filter string_dec); discharge_append) *) *)
(*   (*        end. *) *)



(* Ltac discharge_simulation myRel := *)
(*   apply simulationGeneral with (simRel := myRel); intros; auto; *)
(*   repeat match goal with *)
(*          | H: Forall2 _ _ _ |- _ => inv H; dest *)
(*          | H: RegT |- _ => destruct H as [? [? ?]]; *)
(*                            repeat (unfold fst, snd, projT1, projT2 in *; subst) *)
(*          | _ => discharge_init *)
(*          | H: myRel _ _ |- _ => inv H; auto *)
(*          end; [discharge_NoSelfCall | simplify_Ins; discharge_SemAction | simplify_Ins; discharge_SemAction | simplify_Ins | simplify_Ins]. *)


(* Notation sz := 5. *)

(* Section Named. *)
(*   Variable name: string. *)
(*   Local Notation "^ x" := (name ++ "." ++ x)%string (at level 0). *)

(*     Definition IncrementerImpl := *)
(*       MODULE_WF { *)
(*           Register ^"counter" : Bit sz <- Default *)
(*             with Register ^"counter1" : Bit sz <- Default *)
(*             with Register ^"isSending" : Bool <- true *)
                                             
(*             with Rule ^"send" := *)
(*             ( Read isSending: Bool <- ^"isSending" ; *)
(*                 Assert #isSending ; *)
(*                 Read counter: Bit sz <- ^"counter" ; *)
(*                 Call "counterVal"(#counter: _); *)
(*                 Write ^"isSending" <- !#isSending ; *)
(*                 Retv ) *)

(*             with Rule ^"inc" := *)
(*               ( Read isSending: Bool <- ^"isSending" ; *)
(*                   Assert !#isSending ; *)
(*                   Read counter: Bit sz <- ^"counter" ; *)
(*                   Write ^"counter" <- #counter + $1; *)
(*                   Write ^"isSending" <- !#isSending ; *)
(*                   Retv ) *)
(*         }. *)

(*   Definition IncrementerSpec := *)
(*     MODULE_WF { *)
(*         Register ^"counter" : Bit sz <- Default *)
(*           with Register ^"counter1" : Bit sz <- Default *)
                                         
(*           with Rule ^"send_and_inc" := *)
(*           ( Read counter: Bit sz <- ^"counter" ; *)
(*               Call "counterVal"(#counter: _); *)
(*               Write ^"counter" <- #counter + $1; *)
(*               Retv) *)
(*       }. *)

(*   Record Incrementer_invariant (impl spec: RegsT) : Prop := *)
(*     { counterImpl: word sz ; *)
(*       isSending: bool ; *)
(*       implEq : impl = (^"counter", existT _ (SyntaxKind (Bit sz)) counterImpl) *)
(*                         :: (^"counter1", existT _ (SyntaxKind (Bit sz)) $0) *)
(*                         :: (^"isSending", existT _ (SyntaxKind Bool) isSending) :: nil ; *)
(*       specEq : spec = (^"counter", existT _ (SyntaxKind (Bit sz)) *)
(*                                          (if isSending then counterImpl else counterImpl ^+ $1)) *)
(*                         :: (^"counter1", existT  _ (SyntaxKind (Bit sz)) $0) *)
(*                         :: nil *)
(*     }. *)
(* End Named. *)

(* Theorem Incrementer_TraceInclusion (name: string) : *)
(*   TraceInclusion (Base (IncrementerImpl name)) (Base (IncrementerSpec name)). *)
(* Proof. *)
(*   discharge_simulation (Incrementer_invariant name). *)
(*   - right; do 2 (do 2 eexists; repeat split; eauto; simpl in * ). *)
(*     * repeat (econstructor; eauto; simpl; subst). *)
(*       unfold key_not_In; unfold not; intros; simpl in *; auto. *)
(*     * repeat (econstructor; eauto; simpl; subst). *)
(*       discharge_append. *)
(*       rewrite wzero_wplus; auto. *)
(*   - left; split; auto; simpl in *. *)
(*     repeat (econstructor; eauto; simpl; subst). *)
(*     rewrite negb_true_iff in *; subst. *)
(*     rewrite wzero_wplus; simpl; auto. *)
(* Qed. *)
