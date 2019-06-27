Require Import Kami.Syntax.
Require Import Kami.Properties Kami.PProperties.
Import ListNotations.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.PermutEq.
Require Import RelationClasses Setoid Morphisms.
Require Import ZArith Lib.EclecticLib.

Local Notation PPT_execs := (fun x => fst (snd x)).
Local Notation PPT_calls := (fun x => snd (snd x)).

Local Open Scope Z_scope.

Section NeverCallBaseModule.
  Inductive NeverCallActionT: forall k, ActionT type k -> Prop :=
  | NeverCallMCall meth s e lretT c: False -> @NeverCallActionT lretT (MCall meth s e c)
  | NeverCallLetExpr k (e: Expr type k) lretT c: (forall v, NeverCallActionT (c v)) -> @NeverCallActionT lretT (LetExpr e c)
  | NeverCallLetAction k (a: ActionT type k) lretT c: NeverCallActionT a -> (forall v, NeverCallActionT (c v)) -> @NeverCallActionT lretT (LetAction a c)
  | NeverCallReadNondet k lretT c: (forall v, NeverCallActionT (c v)) -> @NeverCallActionT lretT (ReadNondet k c)
  | NeverCallReadReg r k lretT c: (forall v, NeverCallActionT (c v)) -> @NeverCallActionT lretT (ReadReg r k c)
  | NeverCallWriteReg r k (e: Expr type k) lretT c: NeverCallActionT c  -> @NeverCallActionT lretT (WriteReg r e c)
  | NeverCallIfElse p k (atrue: ActionT type k) afalse lretT c: (forall v, NeverCallActionT (c v)) -> NeverCallActionT atrue -> NeverCallActionT afalse -> @NeverCallActionT lretT (IfElse p atrue afalse c)
  | NeverCallSys ls lretT c: NeverCallActionT c -> @NeverCallActionT lretT (Sys ls c)
  | NeverCallReturn lretT e: @NeverCallActionT lretT (Return e).

  Variable m : BaseModule.
  
  Definition NeverCallBaseModule :=
    (forall rule, In rule (getRules m) -> NeverCallActionT (snd rule type)) /\
    (forall meth, In meth (getMethods m) ->
                  forall v, NeverCallActionT (projT2 (snd meth) type v)).
End NeverCallBaseModule.


Inductive NeverCallMod: Mod -> Prop :=
| BaseNeverCall m (HNCBaseModule: NeverCallBaseModule m): NeverCallMod (Base m)
| HideMethNeverCall m s  (HNCModule: NeverCallMod m): NeverCallMod (HideMeth m s)
| ConcatModNeverCall m1 m2 (HNCModule1: NeverCallMod m1) (HNCModule2: NeverCallMod m2)
  : NeverCallMod (ConcatMod m1 m2).

(*
  Proves that the number of method calls returned
  by [getNumCalls] is always greater than or
  equal to 0.
*)
Lemma num_method_calls_positive
  : forall (method : MethT) (labels : list FullLabel),
      0 <= getNumCalls method labels.
Proof 
fun method
  => list_ind _
       (ltac:(discriminate) : 0 <= getNumCalls method [])
       (fun (label : FullLabel) (labels : list FullLabel)
         (H : 0 <= getNumFromCalls method (concat (map PPT_calls labels)))
         => list_ind _ H
              (fun (method0 : MethT) (methods : MethsT)
                (H0 : 0 <= getNumFromCalls method (methods ++ concat (map PPT_calls labels)))
                => sumbool_ind
                     (fun methods_eq
                       => 0 <=
                            if methods_eq
                              then 1 + getNumFromCalls method (methods ++ concat (map PPT_calls labels))
                              else getNumFromCalls method (methods ++ concat (map PPT_calls labels)))
                     (fun _ => Z.add_nonneg_nonneg 1 _ (Zle_0_pos 1) H0)
                     (fun _ => H0)
                     (MethT_dec method method0))
              (snd (snd label))).

(*
  Proves that the number of method executions
  counted by [getNumExecs] is always greater
  than or equal to 0.
*)
Lemma num_method_execs_positive
  : forall (method : MethT) (labels : list FullLabel),
      0 <= getNumExecs method labels.
Proof.
  induction labels; unfold getNumExecs in *; simpl; try lia.
  destruct a; simpl; auto.
  destruct p; simpl; auto.
  destruct r0; simpl; auto.
  destruct (MethT_dec method f); simpl; auto; subst.
  destruct (getNumFromExecs f (map PPT_execs labels)); simpl; auto; try lia.
Defined.

Local Close Scope Z_scope.


Section PPlusTraceInclusion.

  Definition getListFullLabel_diff_flat f (t : (RegsT *((list RuleOrMeth)*MethsT))) : Z:=
    (getNumFromExecs f (PPT_execs t) - getNumFromCalls f (PPT_calls t))%Z. 
  
  Definition WeakInclusion_flat (t1 t2 : (RegsT *((list RuleOrMeth) * MethsT))) :=
    (forall (f : MethT), (getListFullLabel_diff_flat f t1 = getListFullLabel_diff_flat f t2)%Z) /\
    ((exists rle, In (Rle rle) (PPT_execs t2)) ->
     (exists rle, In (Rle rle) (PPT_execs t1))).


  Inductive WeakInclusions_flat : list (RegsT * ((list RuleOrMeth) * MethsT)) -> list (RegsT *((list RuleOrMeth) * MethsT)) -> Prop :=
  |WIf_Nil : WeakInclusions_flat nil nil
  |WIf_Cons : forall (lt1 lt2 : list (RegsT *((list RuleOrMeth) * MethsT))) (t1 t2 : RegsT *((list RuleOrMeth) * MethsT)),
      WeakInclusions_flat lt1 lt2 -> WeakInclusion_flat t1 t2 -> WeakInclusions_flat (t1::lt1) (t2::lt2).

  Definition PPlusTraceList (m : BaseModule)(lt : list (RegsT * ((list RuleOrMeth) * MethsT))) :=
    (exists (o : RegsT), PPlusTrace m o lt).

  Definition PPlusTraceInclusion (m m' : BaseModule) :=
    forall (o : RegsT)(tl : list (RegsT *((list RuleOrMeth) * MethsT))),
      PPlusTrace m o tl -> exists (tl' : list (RegsT * ((list RuleOrMeth) * MethsT))),  PPlusTraceList m' tl' /\ WeakInclusions_flat tl tl'.

  Definition StrongPPlusTraceInclusion (m m' : BaseModule) :=
    forall (o : RegsT)(tl : list (RegsT *((list RuleOrMeth) * MethsT))),
      PPlusTrace m o tl -> exists (tl' : list (RegsT * ((list RuleOrMeth) * MethsT))), PPlusTrace m' o tl' /\ WeakInclusions_flat tl tl'.
End PPlusTraceInclusion.

Section BaseModule.
  Variable m: BaseModule.
  Variable o: RegsT.

  Definition getLabelUpds (ls: list FullLabel) :=
    concat (map (fun x => fst x) ls).
  
  Definition getLabelExecs (ls: list FullLabel) :=
    map (fun x => fst (snd x)) ls.
  
  Definition getLabelCalls (ls: list FullLabel) :=
    concat (map (fun x => (snd (snd x))) ls).


  Lemma getLabelCalls_perm_rewrite l l' :
    l [=] l' ->
    getLabelCalls l [=] getLabelCalls l'.
  Proof.
    induction 1.
    - reflexivity.
    - unfold getLabelCalls; simpl; fold (getLabelCalls l); fold (getLabelCalls l').
      rewrite IHPermutation; reflexivity.
    - unfold getLabelCalls; simpl; fold (getLabelCalls l).
      repeat rewrite app_assoc.
      apply Permutation_app_tail, Permutation_app_comm.
    - rewrite IHPermutation1, IHPermutation2.
      reflexivity.
  Qed.

  Global Instance getLabelCalls_perm_rewrite' :
    Proper (@Permutation (FullLabel) ==> @Permutation (MethT)) (@getLabelCalls) | 10.
  Proof.
    repeat red; intro; eauto using getLabelCalls_perm_rewrite.
  Qed.

  Lemma getLabelExecs_perm_rewrite l l' :
    l [=] l' ->
    getLabelExecs l [=] getLabelExecs l'.
  Proof.
    induction 1; auto.
    - unfold getLabelExecs in *; simpl.
      apply perm_skip; assumption.
    - unfold getLabelExecs in *; simpl.
      apply perm_swap.
    - rewrite IHPermutation1, IHPermutation2; reflexivity.
  Qed.

  Lemma getLabelUpds_perm_rewrite l l' :
    l [=] l' ->
    getLabelUpds l [=] getLabelUpds l'.
  Proof.
    induction 1; auto; unfold getLabelUpds in *; simpl in *.
    - apply Permutation_app_head; assumption.
    - repeat rewrite app_assoc; apply Permutation_app_tail, Permutation_app_comm.
    - rewrite IHPermutation1, IHPermutation2; reflexivity.
  Qed.

  Global Instance getLabelExecs_perm_rewrite' :
    Proper (@Permutation (FullLabel) ==> @Permutation (RuleOrMeth)) (@getLabelExecs) | 10.
  Proof.
    repeat red; intro; eauto using getLabelExecs_perm_rewrite.
  Qed.
  
  Global Instance getLabelUpds_perm_rewrite' :
    Proper (@Permutation (FullLabel) ==> @Permutation (string * {x : FullKind & fullType type x})) (@getLabelUpds) | 10.
  Proof.
    repeat red; intro; eauto using getLabelUpds_perm_rewrite.
  Qed.

  Lemma InCall_getLabelCalls f l:
    InCall f l ->
    In f (getLabelCalls l).
  Proof.
    induction l; unfold InCall,getLabelCalls in *; intros; simpl; dest; auto.
    destruct H; subst;apply in_app_iff; [left; assumption|right; apply IHl].
    exists x; auto.
  Qed.

  Lemma getLabelCalls_InCall f l:
    In f (getLabelCalls l) ->
    InCall f l.
  Proof.
    induction l; unfold InCall, getLabelCalls in *; intros; simpl in *;[contradiction|].
    rewrite in_app_iff in H; destruct H;[exists a; auto|specialize (IHl H);dest].
    exists x; auto.
  Qed.

  Corollary InCall_getLabelCalls_iff f l:
    InCall f l <->
    In f (getLabelCalls l).
  Proof.
    split; intro; eauto using InCall_getLabelCalls, getLabelCalls_InCall.
  Qed.
  
  Lemma PPlusSubsteps_PSubsteps:
    forall upds execs calls,
      PPlusSubsteps m o upds execs calls ->
      exists l,
        PSubsteps m o l /\
        upds [=] getLabelUpds l /\
        execs [=] getLabelExecs l /\
        calls [=] getLabelCalls l.
  Proof.
    unfold getLabelUpds, getLabelExecs, getLabelCalls.
    induction 1; dest.
    - exists nil.
      repeat split; auto; constructor; auto.
    - exists ((u, (Rle rn, cs)) :: x).
      repeat split; auto; try constructor; auto; simpl.
      + econstructor; eauto; intros.
        * clear - H1 H4 HUpds HExecs HCalls HDisjRegs.
          intro.
          destruct (HDisjRegs k); auto.
          left; intro.
          clear - H1 H4 H H0.
          rewrite H1 in H.
          rewrite <- flat_map_concat_map in H.
          rewrite in_map_iff in H.
          setoid_rewrite in_flat_map in H.
          rewrite in_map_iff in *; dest; subst.
          firstorder fail.
        * clear - H2 H4 HExecs HNoRle.
          apply HNoRle.
          rewrite H2.
          rewrite in_map_iff.
          firstorder fail.
      + rewrite H1 in HUpds; auto.
      + rewrite HExecs.
        constructor; auto.
      + rewrite H3 in HCalls; auto.
    - exists ((u, (Meth (fn, existT SignT (projT1 fb) (argV, retV)), cs)) :: x).
      repeat split; auto; try constructor; auto; simpl.
      + econstructor 3; eauto; intros.
        * clear - H1 H4 HUpds HExecs HCalls HDisjRegs.
          intro.
          destruct (HDisjRegs k); auto.
          left; intro.
          clear - H1 H4 H H0.
          rewrite H1 in H.
          rewrite <- flat_map_concat_map in H.
          rewrite in_map_iff in H.
          setoid_rewrite in_flat_map in H.
          rewrite in_map_iff in *; dest; subst.
          firstorder fail.
      + rewrite H1 in HUpds; auto.
      + rewrite HExecs.
        constructor; auto.
      + rewrite H3 in HCalls; auto.
  Qed.
End BaseModule.

Section PPlusSubsteps_rewrite.
  
  Lemma PPlusSubsteps_rewrite_regs m o1 o2 upds execs calls:
    (o1 [=] o2) ->
    PPlusSubsteps m o1 upds execs calls ->
    PPlusSubsteps m o2 upds execs calls.
  Proof.
    induction 2.
    - econstructor 1.
      rewrite <- H; assumption.
    - econstructor 2;(rewrite <- H || apply (PSemAction_rewrite_state H) in HPAction); eauto.
    - econstructor 3;(rewrite <- H || apply (PSemAction_rewrite_state H) in HPAction); eauto.
  Qed.

  Lemma PPlusSubsteps_rewrite_upds m o execs calls upds1 upds2:
    (upds1 [=] upds2) ->
    PPlusSubsteps m o upds1 execs calls ->
    PPlusSubsteps m o upds2 execs calls.
  Proof.
    induction 2.
    - apply Permutation_nil in H; rewrite H.
      econstructor 1; assumption.
    - econstructor 2; eauto.
      rewrite H in HUpds.
      assumption.
    - econstructor 3; eauto.
      rewrite H in HUpds.
      assumption.
  Qed.

  Lemma PPlusSubsteps_rewrite_execs m o upds calls execs1 execs2:
    (execs1 [=] execs2) ->
    PPlusSubsteps m o upds execs1 calls ->
    PPlusSubsteps m o upds execs2 calls.
  Proof.
    induction 2.
    - apply Permutation_nil in H; rewrite H.
      econstructor 1; assumption.
    - econstructor 2; eauto.
      rewrite H in HExecs.
      assumption.
    - econstructor 3; eauto.
      rewrite H in HExecs.
      assumption.
  Qed.

  Lemma PPlusSubsteps_rewrite_calls m o upds execs calls1 calls2:
    (calls1 [=] calls2) ->
    PPlusSubsteps m o upds execs calls1 ->
    PPlusSubsteps m o upds execs calls2.
  Proof.
    induction 2.
    - apply Permutation_nil in H; rewrite H.
      econstructor 1; assumption.
    - econstructor 2; eauto.
      rewrite H in HCalls.
      assumption.
    - econstructor 3; eauto.
      rewrite H in HCalls.
      assumption.
  Qed.

  Lemma PPlusSubsteps_rewrite_all m o1 o2 upds1 execs1 calls1 upds2 execs2 calls2 :
    o1 [=] o2 ->
    upds1 [=] upds2 ->
    execs1 [=] execs2 ->
    calls1 [=] calls2 ->
    PPlusSubsteps m o1 upds1 execs1 calls1 ->
    PPlusSubsteps m o2 upds2 execs2 calls2.
  Proof.
    intros.
    apply (PPlusSubsteps_rewrite_regs H) in H3;
      apply (PPlusSubsteps_rewrite_upds H0) in H3;
      apply (PPlusSubsteps_rewrite_execs H1) in H3;
      apply (PPlusSubsteps_rewrite_calls H2) in H3;
      assumption.
  Qed.
  
  Global Instance PPlusSubsteps_rewrite' :
    Proper (Logic.eq ==>
                     @Permutation (string * {x : FullKind & fullType type x}) ==>
                     @Permutation (string * {x : FullKind & fullType type x}) ==>
                     @Permutation RuleOrMeth ==>
                     @Permutation MethT ==>
                     iff) (@PPlusSubsteps)| 10.
  Proof.
    repeat red; intros; split; intros; subst; eauto using Permutation_sym, PPlusSubsteps_rewrite_all.
    symmetry in H0.
    symmetry in H1.
    symmetry in H2.
    symmetry in H3.
    eapply PPlusSubsteps_rewrite_all; eauto.
  Qed.
End PPlusSubsteps_rewrite.

Lemma Permutation_flat_map_rewrite (A B : Type) (l1 l2 : list A) (f : A -> list B) :
  l1 [=] l2 ->
  flat_map f l1 [=] flat_map f l2.
Proof.
  induction 1; simpl in *; auto.
  - apply Permutation_app_head; assumption.
  - repeat rewrite app_assoc; apply Permutation_app_tail.
    rewrite Permutation_app_comm; reflexivity.
  - rewrite IHPermutation1, IHPermutation2; reflexivity.
Qed.

Global Instance Permutation_flat_map_rewrite' (A B : Type)(f : A -> list B):
  Proper (@Permutation A ==> @Permutation B) (@flat_map A B f) | 10.
repeat red; intros; intros; eauto using Permutation_flat_map_rewrite.
Qed.

Lemma PSubsteps_PPlusSubsteps:
  forall m o l,
    PSubsteps m o l ->
    PPlusSubsteps m o (getLabelUpds l) (getLabelExecs l) (getLabelCalls l).
Proof.
  induction 1; unfold getLabelUpds, getLabelExecs, getLabelCalls in *; try setoid_rewrite <- flat_map_concat_map.
  - econstructor; eauto.
  - rewrite HLabel; simpl; setoid_rewrite <-flat_map_concat_map in IHPSubsteps.
    econstructor 2; intros; eauto.
    + clear - HDisjRegs.
      induction ls.
      * firstorder.
      * intro; simpl in *; rewrite map_app, in_app_iff, DeM1.
        assert (DisjKey (flat_map (fun x : FullLabel => fst x) ls) u);[eapply IHls; eauto|].
        specialize (HDisjRegs a (or_introl _ eq_refl) k); specialize (H k).
        firstorder fail.
    + rewrite in_map_iff in H0; dest; rewrite <- H0.
      eapply HNoRle; eauto.
  - rewrite HLabel; simpl; setoid_rewrite <- flat_map_concat_map in IHPSubsteps.
    econstructor 3; intros; eauto.
    + clear - HDisjRegs.
      induction ls.
      * firstorder.
      * intro; simpl in *; rewrite map_app, in_app_iff, DeM1.
        assert (DisjKey (flat_map (fun x : FullLabel => fst x) ls) u);[eapply IHls; eauto|].
        specialize (HDisjRegs a (or_introl _ eq_refl) k); specialize (H k).
        firstorder fail.
Qed.

Section PPlusStep.
  Variable m: BaseModule.
  Variable o: RegsT.
  
  Lemma PPlusStep_PStep:
    forall upds execs calls,
      PPlusStep m o upds execs calls ->
      exists l,
        PStep (Base m) o l /\
        upds [=] getLabelUpds l /\
        execs [=] getLabelExecs l /\
        calls [=] getLabelCalls l.
  Proof.
    induction 1.
    apply PPlusSubsteps_PSubsteps in H; dest.
    exists x; repeat split; eauto.
    econstructor 1; eauto.
    intros f HInDef; specialize (H0 f HInDef).
    unfold getNumCalls, getNumExecs, getLabelExecs, getLabelCalls in *.
    rewrite <-H3, <-H2; assumption.
  Qed.

  Lemma PStep_PPlusStep :
  forall l,
    PStep (Base m) o l ->
    PPlusStep m o (getLabelUpds l) (getLabelExecs l) (getLabelCalls l).
  Proof.
    intros; inv H; econstructor.
    - apply PSubsteps_PPlusSubsteps in HPSubsteps; assumption.
    - intros f HInDef; specialize (HMatching f).
      apply HMatching; auto.
  Qed.
End PPlusStep.

Section PPlusTrace.
  Variable m: BaseModule.
  
  Lemma PPlusTrace_PTrace o ls :
    PPlusTrace m o ls ->
    exists ls',
      PTrace (Base m) o ls' /\
      PermutationEquivLists (map fst ls) (map getLabelUpds ls') /\
      PermutationEquivLists (map PPT_execs ls) (map getLabelExecs ls') /\
      PermutationEquivLists (map PPT_calls ls) (map getLabelCalls ls').
  Proof.
    induction 1; subst; dest.
    - exists nil; repeat split; econstructor; eauto.
    - apply PPlusStep_PStep in HPPlusStep; dest.
      exists (x0::x); repeat split; eauto; simpl in *; econstructor 2; eauto.
      + unfold PPlusUpdRegs in HUpdRegs; dest.
        repeat split; eauto.
        intros; destruct (H9 _ _ H10).
        * rewrite H5 in H11; unfold getLabelUpds in H11.
          rewrite <- flat_map_concat_map, in_flat_map in *; dest.
          left; exists (fst x1); split; auto.
          apply (in_map fst) in H11; assumption.
        * destruct H11; right; split; auto.
          intro; apply H11; dest.
          unfold getLabelUpds in *.
          rewrite H5, <- flat_map_concat_map, in_map_iff.
          setoid_rewrite in_flat_map.
          rewrite in_map_iff in H13,H14; dest.
          exists x2; split; auto.
          exists x3; subst; auto.
  Qed.

  Definition extractTriple (lfl : list FullLabel) : (RegsT * ((list RuleOrMeth) * MethsT)) :=
    (getLabelUpds lfl, (getLabelExecs lfl, getLabelCalls lfl)).

  Fixpoint extractTriples (llfl : list (list FullLabel)) : list (RegsT * ((list RuleOrMeth) * MethsT)) :=
    match llfl with
    |lfl::llfl' => (extractTriple lfl)::(extractTriples llfl')
    |nil => nil
    end.

  Lemma extractTriples_nil l :
    extractTriples l = nil -> l = nil.
  Proof.
    destruct l; intros; auto.
    inv H.
  Qed.
  
  Lemma PTrace_PPlusTrace o ls:
    PTrace (Base m) o ls ->
      PPlusTrace m o (extractTriples ls).
  Proof.
    induction 1; subst; intros.
    - econstructor; eauto.
    - simpl; econstructor 2; eauto.
      + apply PStep_PPlusStep; apply HPStep.
      + unfold PUpdRegs,PPlusUpdRegs in *; dest; repeat split; eauto.
        intros; destruct (H1 _ _ H2);[left|right]; unfold getLabelUpds; dest.
        * rewrite <- flat_map_concat_map, in_flat_map.
          rewrite (in_map_iff fst) in H3; dest; rewrite <- H3 in H4.
          firstorder.
        * split; auto; intro; apply H3.
          rewrite <- flat_map_concat_map, in_map_iff in H5; dest.
          rewrite in_flat_map in H6; dest.
          exists (fst x0); split.
          -- rewrite in_map_iff; exists x0; firstorder.
          -- rewrite <- H5, in_map_iff; exists x; firstorder.
      + unfold extractTriple; reflexivity.
  Qed.
End PPlusTrace.

Section PPlusTraceInclusion.
  Lemma  InExec_rewrite f l:
    In (Meth f) (getLabelExecs l) <-> InExec f l.
  Proof.
    split; unfold InExec; induction l; simpl in *; intros; auto.
  Qed.

  Lemma InCall_rewrite f l :
    In f (getLabelCalls l) <-> InCall f l.
  Proof.
    split; unfold InCall; induction l; simpl in *; intros; dest; try contradiction.
    - unfold getLabelCalls in H. rewrite <- flat_map_concat_map, in_flat_map in H.
      assumption.
    -  unfold getLabelCalls; rewrite <- flat_map_concat_map, in_flat_map.
       firstorder fail.
  Qed.

  Lemma WeakInclusion_flat_WeakInclusion (l1 l2 : list FullLabel) :
    WeakInclusion_flat (extractTriple l1) (extractTriple l2) <->
    WeakInclusion l1 l2.
  Proof.
    split; auto.
  Qed.
  
  Lemma WeakInclusions_flat_WeakInclusions (ls1 ls2 : list (list FullLabel)) :
    WeakInclusions_flat (extractTriples ls1) (extractTriples ls2) ->
    WeakInclusions ls1 ls2.
  Proof.
    revert ls2; induction ls1; intros; simpl in *; inv H.
    - symmetry in H0; apply extractTriples_nil in H0; subst; econstructor.
    - destruct ls2; inv H2.
      econstructor 2.
      + eapply IHls1; eauto.
      + apply WeakInclusion_flat_WeakInclusion; assumption.
  Qed.
  
  Lemma StrongPPlusTraceInclusion_PPlusTraceInclusion m m' :
    StrongPPlusTraceInclusion m m' ->
    PPlusTraceInclusion m m'.
  Proof.
    unfold StrongPPlusTraceInclusion, PPlusTraceInclusion, PPlusTraceList; intros.
    specialize (H _ _ H0); dest.
    exists x; split; auto.
    exists o; auto.
  Qed.
  
  Lemma WeakInclusions_flat_PermutationEquivLists_r ls1:
    forall l ls2,
      WeakInclusions_flat (extractTriples ls1) l ->
      PermutationEquivLists (map fst l) (map getLabelUpds ls2) ->
      PermutationEquivLists (map PPT_execs l) (map getLabelExecs ls2) ->
      PermutationEquivLists (map PPT_calls l) (map getLabelCalls ls2) ->
      WeakInclusions_flat (extractTriples ls1) (extractTriples ls2).
  Proof.
    induction ls1; intros; inv H; simpl in *.
    - destruct ls2; simpl in *.
      + econstructor.
      + inv H2.
    - destruct ls2; inv H2; inv H1; inv H0; simpl in *.
      econstructor.
      + eapply IHls1; eauto.
      + unfold WeakInclusion_flat in *; dest; simpl in *.
        split; intros;
          [unfold getListFullLabel_diff_flat in *; simpl in *; rewrite <-H9, <-H10; apply H|].
        apply H0; setoid_rewrite H10; assumption.
  Qed.
  
  Lemma PPlusTraceInclusion_PTraceInclusion (m m' : BaseModule) :
    PPlusTraceInclusion m m' ->
    PTraceInclusion (Base m) (Base m').
  Proof.
    repeat intro.
    apply (PTrace_PPlusTrace) in H0.
    specialize (H o _ H0); dest.
    destruct  H.
    apply (PPlusTrace_PTrace) in H; dest.
    exists x1; split.
    - exists x0; assumption.
    - apply WeakInclusions_flat_WeakInclusions.
      apply (WeakInclusions_flat_PermutationEquivLists_r _ _ H1 H2 H3 H4).
  Qed.

  Lemma PPlusTraceInclusion_TraceInclusion (m m' : BaseModule) (Wfm: WfMod (Base m)) (Wfm': WfMod (Base m')):
    PPlusTraceInclusion m m' ->
    TraceInclusion (Base m) (Base m').
  Proof.
    intros; apply PTraceInclusion_TraceInclusion, PPlusTraceInclusion_PTraceInclusion; auto.
  Qed.
End PPlusTraceInclusion.

Lemma NoDup_app_iff (A : Type) (l1 l2 : list A) :
  NoDup (l1++l2) <->
  NoDup l1 /\
  NoDup l2 /\
  (forall a, In a l1 -> ~In a l2) /\
  (forall a, In a l2 -> ~In a l1).
Proof.
  repeat split; intros; dest.
  - induction l1; econstructor; inv H; firstorder.
  - induction l2; econstructor; apply NoDup_remove in H; dest; firstorder.
  - induction l1; auto.
    simpl in H; rewrite NoDup_cons_iff in H; dest; firstorder.
    subst; firstorder.
  - induction l2; auto.
    apply NoDup_remove in H; dest; firstorder.
    subst; firstorder.
  -  induction l1; simpl; eauto.
     constructor.
     + rewrite in_app_iff, DeM1; split; firstorder.
       inv H; assumption.
     + inv H; eapply IHl1; eauto; firstorder.
Qed.

Lemma NoDup_app_Disj (A : Type) (dec : forall (a1 a2 : A), {a1 = a2}+{a1 <> a2}) :
    forall (l1 l2 : list A),
      NoDup (l1++l2) ->
      (forall a, ~In a l1 \/ ~In a l2).
Proof.
  intros.
  rewrite NoDup_app_iff in H; dest.
  destruct (in_dec dec a l1); auto.
Qed.

Notation remove_calls := (fun x y => negb (getBool (string_dec (fst x) (fst y)))).
Notation keep_calls := (fun x y => (getBool (string_dec (fst x) (fst y)))).

Definition methcmp (m1 m2 : MethT) : bool := getBool (MethT_dec m1 m2).

Definition remove_execs (calls : MethsT) (exec : RuleOrMeth) : bool :=
  match exec with
  | Rle _ => false
  | Meth f => existsb (methcmp f) calls
  end.

Lemma key_not_In_filter (f : DefMethT) (calls : MethsT) :
  key_not_In (fst f) calls ->
  filter (remove_calls f) calls = calls.
Proof.
  induction calls; unfold key_not_In in *; simpl in *; intros; auto.
  destruct string_dec; pose proof (H (snd a)); simpl in *.
  - apply False_ind; apply H0; left.
    destruct a; simpl in *; rewrite e; reflexivity.
  - rewrite IHcalls; auto.
    repeat intro; specialize (H v); apply H; right; assumption.
Qed.

Lemma PSemAction_inline_notIn (f : DefMethT) o k (a : ActionT type k)
      readRegs newRegs calls (fret : type k) :
  PSemAction o a readRegs newRegs calls fret ->
  ~In (fst f) (map fst calls) ->
  PSemAction o (inlineSingle f a) readRegs newRegs calls fret.
Proof.
  induction 1; simpl; intros.
  - destruct string_dec; subst.
    + apply False_ind; apply H0; rewrite HAcalls; simpl; left; reflexivity.
    + econstructor 1; eauto.
      apply IHPSemAction; intro; apply H0; rewrite HAcalls; simpl; right; assumption.
  - econstructor 2; eauto.
  - econstructor 3; eauto;[eapply IHPSemAction1|eapply IHPSemAction2];
      intro; apply H1; rewrite HUCalls, map_app, in_app_iff;[left|right]; assumption.
  - econstructor 4; eauto.
  - econstructor 5; eauto.
  - econstructor 6; eauto.
  - econstructor 7; eauto; [eapply IHPSemAction1|eapply IHPSemAction2];
      intro; apply H1; rewrite HUCalls, map_app, in_app_iff;[left|right]; assumption.
  - econstructor 8; eauto; [eapply IHPSemAction1|eapply IHPSemAction2];
      intro; apply H1; rewrite HUCalls, map_app, in_app_iff;[left|right]; assumption.
  - econstructor 9; eauto.
  - econstructor 10; eauto.
Qed.

Inductive PSemAction_meth_collector (f : DefMethT) (o : RegsT) : RegsT -> RegsT -> MethsT -> MethsT -> Prop :=
|NilCalls : PSemAction_meth_collector f o nil nil nil nil
|ConsCalls reads1 reads2 reads upds1 upds2
           upds calls1 calls2 calls calls'
           calls'' argV retV:
   PSemAction_meth_collector f o reads1 upds1 calls1 calls' ->
   DisjKey upds1 upds2 ->
   reads [=] reads1 ++ reads2 ->
   upds [=] upds1 ++ upds2 ->
   calls [=] calls1 ++ calls2 ->
   calls'' [=] ((fst f, (existT _ (projT1 (snd f)) (argV, retV)))::calls') ->
   PSemAction o (projT2 (snd f) type argV) reads2 upds2 calls2 retV ->
   PSemAction_meth_collector f o reads upds calls calls''.

Lemma Produce_action_from_collector (f : DefMethT) (o : RegsT) reads upds calls calls' call:
  In call calls' ->
  PSemAction_meth_collector f o reads upds calls calls' ->
  exists reads1 reads2 upds1 upds2 calls1 calls2 calls'' argV retV,
    DisjKey upds1 upds2 /\
    upds [=] upds2++upds1 /\
    calls [=] calls2++calls1 /\
    reads [=] reads2 ++ reads1 /\
    call = (fst f, (existT _ (projT1 (snd f)) (argV, retV))) /\
    calls' [=] call::calls'' /\
    PSemAction o (projT2 (snd f) type argV) reads2 upds2 calls2 retV /\
    PSemAction_meth_collector f o reads1 upds1 calls1 calls''.
Proof.
  induction 2.
  - contradiction.
  - rewrite H5 in H.
    destruct H.
    + exists reads1, reads2, upds1, upds2, calls1, calls2, calls', argV, retV; subst.
      repeat split; auto; (rewrite H2 || rewrite H3 || rewrite H4 || rewrite H5); subst; auto; apply Permutation_app_comm.
    + specialize (IHPSemAction_meth_collector H); dest.
      rewrite H8, H9, H10, H12 in *.
      exists (reads2++x), x0, (upds2++x1), x2, (calls2++x3), x4, ((fst f, existT _ (projT1 (snd f)) (argV, retV))::x5), x6, x7.
      repeat split; auto.
      * intro; destruct (H7 k), (H1 k); rewrite map_app,in_app_iff in *; dest; firstorder fail.
      * rewrite H3, <-app_assoc; apply Permutation_app_head, Permutation_app_comm.
      * rewrite H4, <-app_assoc; apply Permutation_app_head, Permutation_app_comm.
      * rewrite H2, <-app_assoc; apply Permutation_app_head, Permutation_app_comm.
      * rewrite H5; apply perm_swap.
      * econstructor.
        -- apply H14.
        -- assert (DisjKey x1 upds2).
           ++ intro; destruct (H1 k);[rewrite map_app,in_app_iff,DeM1 in *; dest; left; assumption|right; assumption].
           ++ apply H15.
        -- apply Permutation_app_comm.
        -- apply Permutation_app_comm.
        -- apply Permutation_app_comm.
        -- reflexivity.
        -- assumption.
Qed.

Lemma collector_perm_rewrite f o reads upds calls calls1':
  PSemAction_meth_collector f o reads upds calls calls1' ->
  forall calls2',
    calls1' [=] calls2' ->
    PSemAction_meth_collector f o reads upds calls calls2'.
Proof.
  induction 1; intros.
  - apply Permutation_nil in H; subst.
    constructor.
  - rewrite H6 in H4.
    econstructor; eauto.
Qed.

Global Instance collector_perm_rewrite' :
  Proper (eq ==> eq ==> eq ==> eq ==> eq ==> (@Permutation MethT) ==> iff) (@PSemAction_meth_collector) | 10.
Proof.
  repeat red; intro; split; intros; subst; eauto using collector_perm_rewrite, Permutation_sym.
Qed.

Lemma collector_split (f : DefMethT) o calls1' calls2' :
  forall  reads upds calls,
  PSemAction_meth_collector f o reads upds calls (calls1'++calls2') ->
  exists reads1 reads2 upds1 upds2 calls1 calls2,
    reads [=] reads1 ++ reads2 /\
    upds [=] upds1 ++ upds2 /\
    calls [=] calls1 ++ calls2 /\
    DisjKey upds1 upds2 /\
    PSemAction_meth_collector f o reads1 upds1 calls1 calls1' /\
    PSemAction_meth_collector f o reads2 upds2 calls2 calls2'.
Proof.
  induction calls1'; simpl; intros.
  - exists nil, reads, nil, upds, nil, calls.
    repeat split; auto.
    + intro; auto.
    + constructor.
  - specialize (Produce_action_from_collector _ (in_eq _ _) H) as TMP; dest.
    apply Permutation_cons_inv in H5.
    rewrite <- H5 in H7.
    specialize (IHcalls1' _ _ _ H7) as TMP; dest.
    exists (x0++x8), x9, (x2++x10), x11, (x4++x12), x13.
    repeat split.
    + rewrite H8, app_assoc in H3; assumption.
    + rewrite H9, app_assoc in H1; assumption.
    + rewrite H10, app_assoc in H2; assumption.
    + intro; specialize (H11 k); specialize (H0 k); clear - H0 H11 H9; rewrite H9,map_app, in_app_iff in *; firstorder fail.
    + econstructor.
      * apply H12.
      * rewrite H9 in H0; assert (DisjKey x10  x2);[intro; specialize (H0 k);
                                                     rewrite map_app, in_app_iff in *;clear - H0; firstorder fail| apply H14].
      * apply Permutation_app_comm.
      * apply Permutation_app_comm.
      * apply Permutation_app_comm.
      * rewrite H4; reflexivity.
      * assumption.
    + assumption.
Qed.

Lemma collector_correct_fst f o reads upds calls calls' call :
  In call calls' ->
  PSemAction_meth_collector f o reads upds calls calls' ->
  fst call = fst f.
Proof.
  intros.
  specialize (Produce_action_from_collector _ H H0) as TMP; dest.
  destruct call; inv H5; simpl; reflexivity.
Qed.

Definition called_by (f : DefMethT) (call :MethT) : bool :=
  (getBool (string_dec (fst f) (fst call))).

Local Notation complement f := (fun x => negb (f x)).

Definition called_execs (calls : MethsT) (exec : RuleOrMeth) : bool :=
  match exec with
  | Rle _ => false
  | Meth f => existsb (methcmp f) calls
  end.

Lemma separate_calls_by_filter (A : Type) (l : list A) (f : A -> bool):
  l [=] (filter f l) ++ (filter (complement f) l).
Proof.
  induction l; auto; simpl.
  destruct (f a); simpl; rewrite IHl at 1;[reflexivity|apply Permutation_middle].
Qed.

Lemma reduce_called_execs_list execs c :
  ~In (Meth c) execs ->
  forall calls,
    (filter (called_execs (c::calls)) execs) = (filter (called_execs calls) execs).
Proof.
  induction execs; intros; auto.
  unfold called_execs, methcmp in *; destruct a; simpl in *.
  - eapply IHexecs.
    intro; apply H.
    right; assumption.
  - destruct MethT_dec; simpl.
    + apply False_ind; apply H.
      rewrite e; left; reflexivity.
    + rewrite IHexecs;[reflexivity|].
      intro; apply H; right; assumption.
Qed.

Corollary collector_called_by_filter_irrel f o calls' :
  forall reads upds calls,
  PSemAction_meth_collector f o reads upds calls calls' ->
  (filter (called_by f) calls') = calls'.
Proof.
  induction calls'; intros; auto.
  specialize (collector_correct_fst _ (in_eq _ _) H); intro.
  unfold called_by; simpl; destruct string_dec;[simpl;fold (called_by f)|symmetry in H0; contradiction].
  specialize (Produce_action_from_collector _ (in_eq _ _ ) H) as TMP; dest.
  apply Permutation_cons_inv in H6.
  rewrite <- H6 in H8.
  erewrite IHcalls'; eauto.
Qed.

Corollary collector_complement_called_by_filter_nil f o calls' :
  forall reads upds calls,
    PSemAction_meth_collector f o reads upds calls calls' ->
    (filter (complement (called_by f)) calls') = nil.
Proof.
  intros.
  specialize (separate_calls_by_filter calls' (called_by f)) as parti.
  rewrite (collector_called_by_filter_irrel H) in parti.
  rewrite <- app_nil_r in parti at 1.
  apply Permutation_app_inv_l in parti.
  apply Permutation_nil in parti; assumption.
Qed.

Lemma collector_correct_snd f o reads upds calls calls' call :
  In call calls' ->
  PSemAction_meth_collector f o reads upds calls calls' ->
  exists argV retV,
    snd call = (existT _ (projT1 (snd f)) (argV, retV)).
Proof.
  intros.
  specialize (Produce_action_from_collector _ H H0) as TMP; dest.
  destruct call; inv H5; simpl; exists x6, x7; reflexivity.
Qed.

Lemma notIn_filter_nil (f : DefMethT) (calls : MethsT) :
  ~In (fst f) (map fst calls) ->
  filter (called_by f) calls = nil.
Proof.
  induction calls; auto; simpl.
  intro; dest.
  unfold called_by; destruct string_dec; simpl; auto.
  apply False_ind, H; auto.
Qed.

Lemma notIn_complement_filter_irrel (f : DefMethT) (calls : MethsT) :
  ~In (fst f) (map fst calls) ->
  filter (complement (called_by f)) calls = calls.
Proof.
  induction calls; auto; simpl; intros.
  unfold called_by in *; destruct string_dec; simpl in *;
    [apply False_ind, H|rewrite IHcalls];auto.
Qed.

Lemma filter_complement_disj (A : Type) (dec : forall (a1 a2 : A), {a1=a2}+{a1<>a2}) (f : A -> bool) (l : list A) :
  forall x, ~In x (filter f l) \/ ~In x (filter (complement f) l).
Proof.
  intros.
  destruct (in_dec dec x (filter f l)).
  - rewrite filter_In in i; dest.
    right; intro.
    rewrite filter_In in H1; dest.
    rewrite H0 in H2; discriminate.
  - left; assumption.
Qed.

Lemma PSemAction_NoDup_Key_Writes k o (a : ActionT type k) readRegs newRegs calls (fret : type k) :
  PSemAction o a readRegs newRegs calls fret ->
  NoDup (map fst newRegs).
Proof.
  induction 1;
    eauto;[|
           rewrite HANewRegs; simpl; econstructor; eauto; intro;
           specialize (fst_produce_snd _ _ H0) as TMP; dest; specialize (HDisjRegs x);
           contradiction| | |subst; econstructor];
    rewrite HUNewRegs; rewrite map_app,NoDup_app_iff; repeat split; eauto;
        repeat intro; specialize (HDisjRegs a0); firstorder.
Qed.

Corollary PSemAction_NoDup_Writes k o (a : ActionT type k) readRegs newRegs calls (fret : type k) :
  PSemAction o a readRegs newRegs calls fret ->
  NoDup newRegs.
Proof.
  intros; apply PSemAction_NoDup_Key_Writes in H; apply NoDup_map_inv in H; assumption.
Qed.

Lemma collector_NoDupRegs1 (f : DefMethT) o reads upds calls calls' :
  PSemAction_meth_collector f o reads upds calls calls' ->
  NoDup (map fst upds).
Proof.
  induction 1.
  - constructor.
  - rewrite H2, map_app, NoDup_app_iff.
    specialize (PSemAction_NoDup_Key_Writes H5) as ND2.
    repeat split; auto; repeat intro; specialize (H0 a); firstorder.
Qed.

Lemma PSemAction_inline_In (f : DefMethT) o:
  forall {retK2} a calls1 calls2 readRegs newRegs (retV2 : type retK2),
    PSemAction o a readRegs newRegs (calls1++calls2) retV2 ->
    ~In (fst f) (map fst calls2) ->
    forall readRegs' newRegs' calls',
      DisjKey newRegs' newRegs ->
      PSemAction_meth_collector f o readRegs' newRegs' calls' calls1 ->      
      PSemAction o (inlineSingle f a) (readRegs' ++ readRegs) (newRegs' ++ newRegs) (calls'++calls2) retV2.
Proof.
  induction a; intros.
  - simpl; destruct string_dec;[destruct Signature_dec|]; subst.
    + inv H0; EqDep_subst.
      assert (In (fst f, existT SignT (projT1 (snd f)) (evalExpr e, mret)) calls1);
        [case (in_app_or _ _ _ (Permutation_in _ (Permutation_sym (HAcalls)) (in_eq _ _))); auto; intros TMP;apply (in_map fst) in TMP; contradiction|].
      specialize (Produce_action_from_collector _ H0 H3) as TMP; destruct TMP as [creads1 [creads2 [cupds1 [cupds2 [ccalls1 [ccalls2 [ccalls'' [cargV [cretV decomp]]]]]]]]].
      destruct decomp as [HDisju12 [HNr21 [HC21 [HRr21 [Hceq [HC1 [HSa HSac]]]]]]].
      inv Hceq; EqDep_subst.
      econstructor.
      * rewrite HNr21 in H2.
        assert (DisjKey cupds2 (cupds1++newRegs)) as HDjk21n;[|apply HDjk21n].
        intro; specialize (H2 k); specialize (HDisju12 k); rewrite map_app,in_app_iff, DeM1 in *.
        clear - H2 HDisju12; firstorder fail.
      * econstructor; eauto.
      * rewrite HRr21, <-app_assoc.
        apply Permutation_app_head.
        reflexivity.
      * rewrite HNr21, <-app_assoc; reflexivity.
      * rewrite HC21, <-app_assoc; reflexivity.
      * eapply H; auto.
        -- rewrite HC1 in HAcalls; simpl in *.
           apply Permutation_cons_inv in HAcalls.
           symmetry in HAcalls.
           apply (PSemAction_rewrite_calls HAcalls HPSemAction).
        -- rewrite HNr21 in H2.
           intro; specialize (H2 k); rewrite map_app, in_app_iff in *.
           clear - H2; firstorder fail.
        -- assumption.
    + inv H0; EqDep_subst.
      specialize (Permutation_in _ (Permutation_sym HAcalls) (in_eq _ _)); rewrite in_app_iff; intro TMP.
      destruct TMP as [H0|H0];[|apply (in_map fst) in H0; contradiction].
      specialize (collector_correct_snd _ H0 H3) as TMP; dest; simpl in *.
      inv H4; EqDep_subst.
      apply False_ind; apply n; reflexivity.
    + inv H0; EqDep_subst.
      specialize (Permutation_in _ (Permutation_sym HAcalls) (in_eq _ _)); intro TMP.
      rewrite in_app_iff in TMP; destruct TMP as [H0|H0];[apply (collector_correct_fst _ H0) in H3; symmetry in H3; contradiction|].
      apply in_split in H0; dest.
      rewrite H0, <-Permutation_middle, Permutation_app_comm in HAcalls; simpl in *.
      apply Permutation_cons_inv in HAcalls.
      rewrite Permutation_app_comm in HAcalls.
      econstructor.
      * rewrite H0, app_assoc,Permutation_app_comm; simpl.
        apply perm_skip.
        setoid_rewrite Permutation_app_comm.
        rewrite <-app_assoc.
        reflexivity.
      * eapply H; auto.
        -- apply (PSemAction_rewrite_calls (Permutation_sym HAcalls) HPSemAction).
        -- rewrite H0 in H1.
           rewrite map_app, in_app_iff in *.
           simpl in *; repeat rewrite DeM1 in *; clear - H1; firstorder fail.
        -- assumption.
  - inv H0; EqDep_subst.
    econstructor 2; eauto.
  - inv H0; EqDep_subst.
    specialize (Permutation_filter (called_by f) HUCalls) as HC1.
    rewrite filter_app, (collector_called_by_filter_irrel H3), notIn_filter_nil, app_nil_r in HC1; auto.
    specialize (Permutation_filter (complement (called_by f)) HUCalls) as HC2.
    rewrite filter_app, (collector_complement_called_by_filter_nil H3), (notIn_complement_filter_irrel) in HC2; auto; simpl in *.
    rewrite filter_app in *.
    rewrite HC1 in H3.
    specialize (collector_split _ _ H3) as TMP; destruct TMP as [sreads1 [sreads2 [supds1 [supds2 [scalls1 [scalls2 TMP]]]]]].
    destruct TMP as [HRr12 [HNr12 [HC12 [HDisjs12 [HCol1 HCol2]]]]].
    econstructor 3.
    + rewrite HNr12, HUNewRegs in H2.
      specialize (collector_NoDupRegs1 H3); rewrite HNr12, map_app; intros TMP.
      assert (DisjKey (supds1++newRegs0) (supds2++newRegsCont));[|apply H0].
      intro; specialize (H2 k0); specialize (HDisjRegs k0);specialize (NoDup_app_Disj string_dec _ _ TMP k0) as TMP2.
      repeat rewrite map_app, in_app_iff in *.
      clear - H2 HDisjRegs TMP2; firstorder fail.
    + eapply IHa.
      * apply (PSemAction_rewrite_calls (separate_calls_by_filter calls (called_by f))) in HPSemAction.
        apply HPSemAction.
      * intro; apply H1; rewrite HC2, map_app, in_app_iff; left; assumption.
      *rewrite HNr12, HUNewRegs in H2.
       intro; specialize (H2 k0); repeat rewrite map_app, in_app_iff in *.
       clear - H2; firstorder fail.
      * apply HCol1.
    + rewrite HRr12, HUReadRegs.
      repeat rewrite <-app_assoc.
      apply Permutation_app_head.
      rewrite app_assoc,Permutation_app_comm.
      rewrite app_assoc.
      rewrite Permutation_app_comm.
      apply Permutation_app_head.
      apply Permutation_app_comm.
    + rewrite HNr12, HUNewRegs.
      repeat rewrite <-app_assoc.
      apply Permutation_app_head.
      repeat rewrite app_assoc.
      apply Permutation_app_tail.
      apply Permutation_app_comm.
    + rewrite HC2, HC12.
      repeat rewrite <-app_assoc.
      apply Permutation_app_head.
      rewrite app_assoc, Permutation_app_comm.
      rewrite app_assoc.
      rewrite Permutation_app_comm; apply Permutation_app_head.
      apply Permutation_app_comm.
    + eapply H; eauto.
      * apply (PSemAction_rewrite_calls (separate_calls_by_filter callsCont (called_by f)) HPSemActionCont).
      * rewrite HC2, map_app,in_app_iff in H1; dest; clear - H1; tauto.
      * rewrite HNr12, HUNewRegs in H2.
        intro k0; specialize (H2 k0).
        repeat rewrite map_app, in_app_iff in H2.
        clear - H2; firstorder fail.
  - inv H0; EqDep_subst.
    simpl; econstructor 4; eauto.
  - inv H0; EqDep_subst.
    simpl; econstructor 5.
    + apply HRegVal.
    + eapply H; eauto.
    + rewrite HNewReads.
      symmetry.
      apply Permutation_middle.
  - inv H; EqDep_subst.
    simpl; econstructor 6; auto.
    + assert (key_not_In r (newRegs'++newRegs0));[|apply H].
      intro; rewrite in_app_iff.
      specialize (HDisjRegs v).
      intro; destruct H; auto.
      apply (in_map fst) in H; simpl in *.
      rewrite HANewRegs in H1; specialize (H1 r).
      destruct H1;[contradiction|apply H1; left; reflexivity].
    + rewrite HANewRegs.
      rewrite Permutation_app_comm; simpl.
      apply perm_skip, Permutation_app_comm.
    + eapply IHa; eauto.
      rewrite HANewRegs in H1; intro k0; specialize (H1 k0); simpl in *.
      clear - H1; firstorder fail.
  - inv H0; EqDep_subst; simpl.
    + specialize (Permutation_filter (called_by f) HUCalls) as HC1.
      rewrite filter_app, (collector_called_by_filter_irrel H3), notIn_filter_nil, app_nil_r in HC1; auto.
      specialize (Permutation_filter (complement (called_by f)) HUCalls) as HC2.
      rewrite filter_app, (collector_complement_called_by_filter_nil H3), (notIn_complement_filter_irrel) in HC2; auto; simpl in *.
      rewrite filter_app in *.
      rewrite HC1 in H3.
      specialize (collector_split _ _ H3) as TMP; destruct TMP as [sreads1 [sreads2 [supds1 [supds2 [scalls1 [scalls2 TMP]]]]]].
      destruct TMP as [HRr12 [HNr12 [HC12 [HDisjs12 [HCol1 HCol2]]]]].
      econstructor 7.
      * rewrite HNr12, HUNewRegs in H2.
        specialize (collector_NoDupRegs1 H3); rewrite HNr12, map_app; intros TMP.
        assert (DisjKey (supds1++newRegs1) (supds2++newRegs2));[|apply H0].
        intro; specialize (H2 k0); specialize (HDisjRegs k0);specialize (NoDup_app_Disj string_dec _ _ TMP k0) as TMP2.
        repeat rewrite map_app, in_app_iff in *.
        clear - H2 HDisjRegs TMP2; firstorder fail.
      * assumption.
      * eapply IHa1.
        -- apply (PSemAction_rewrite_calls (separate_calls_by_filter calls0 (called_by f))) in HAction.
           apply HAction.
        -- intro; apply H1; rewrite HC2, map_app, in_app_iff; left; assumption.
        -- rewrite HNr12, HUNewRegs in H2.
           intro; specialize (H2 k0); repeat rewrite map_app, in_app_iff in *.
           clear - H2; firstorder fail.
        -- apply HCol1.
      * eapply H.
        -- apply (PSemAction_rewrite_calls (separate_calls_by_filter calls3 (called_by f)) HPSemAction).
        -- rewrite HC2, map_app,in_app_iff in H1; clear -H1; firstorder fail.
        -- rewrite HNr12, HUNewRegs in H2.
           intro k0; specialize (H2 k0).
           repeat rewrite map_app, in_app_iff in H2.
           clear - H2; firstorder fail.
        --apply HCol2.
      * rewrite HRr12, HUReadRegs.
        repeat rewrite <-app_assoc.
        apply Permutation_app_head.
        rewrite app_assoc,Permutation_app_comm.
        rewrite app_assoc.
        rewrite Permutation_app_comm.
        apply Permutation_app_head.
        apply Permutation_app_comm.
      * rewrite HNr12, HUNewRegs.
        repeat rewrite <-app_assoc.
        apply Permutation_app_head.
        repeat rewrite app_assoc.
        apply Permutation_app_tail.
        apply Permutation_app_comm.
      * rewrite HC2, HC12.
        repeat rewrite <-app_assoc.
        apply Permutation_app_head.
        repeat rewrite app_assoc.
        apply Permutation_app_tail.
        apply Permutation_app_comm.
    + specialize (Permutation_filter (called_by f) HUCalls) as HC1.
      rewrite filter_app, (collector_called_by_filter_irrel H3), notIn_filter_nil, app_nil_r in HC1; auto.
      specialize (Permutation_filter (complement (called_by f)) HUCalls) as HC2.
      rewrite filter_app, (collector_complement_called_by_filter_nil H3), (notIn_complement_filter_irrel) in HC2; auto; simpl in *.
      rewrite filter_app in *.
      rewrite HC1 in H3.
      specialize (collector_split _ _ H3) as TMP; destruct TMP as [sreads1 [sreads2 [supds1 [supds2 [scalls1 [scalls2 TMP]]]]]].
      destruct TMP as [HRr12 [HNr12 [HC12 [HDisjs12 [HCol1 HCol2]]]]].
      econstructor 8.
      * rewrite HNr12, HUNewRegs in H2.
        specialize (collector_NoDupRegs1 H3); rewrite HNr12, map_app; intros TMP.
        assert (DisjKey (supds1++newRegs1) (supds2++newRegs2));[|apply H0].
        intro; specialize (H2 k0); specialize (HDisjRegs k0);specialize (NoDup_app_Disj string_dec _ _ TMP k0) as TMP2.
        repeat rewrite map_app, in_app_iff in *.
        clear - H2 HDisjRegs TMP2; firstorder fail.
      * assumption.
      * eapply IHa2.
        -- apply (PSemAction_rewrite_calls (separate_calls_by_filter calls0 (called_by f))) in HAction.
           apply HAction.
        -- intro; apply H1; rewrite HC2, map_app, in_app_iff; left; assumption.
        -- rewrite HNr12, HUNewRegs in H2.
           intro; specialize (H2 k0); repeat rewrite map_app, in_app_iff in *.
           clear - H2; firstorder fail.
        -- apply HCol1.
      * eapply H.
        -- apply (PSemAction_rewrite_calls (separate_calls_by_filter calls3 (called_by f)) HPSemAction).
        -- rewrite HC2, map_app,in_app_iff in H1; dest; clear -H1; firstorder fail.
        -- rewrite HNr12, HUNewRegs in H2.
           intro k0; specialize (H2 k0).
           repeat rewrite map_app, in_app_iff in H2.
           clear - H2; firstorder fail.
        --apply HCol2.
      * rewrite HRr12, HUReadRegs.
        repeat rewrite <-app_assoc.
        apply Permutation_app_head.
        rewrite app_assoc,Permutation_app_comm.
        rewrite app_assoc.
        rewrite Permutation_app_comm.
        apply Permutation_app_head.
        apply Permutation_app_comm.
      * rewrite HNr12, HUNewRegs.
        repeat rewrite <-app_assoc.
        apply Permutation_app_head.
        repeat rewrite app_assoc.
        apply Permutation_app_tail.
        apply Permutation_app_comm.
      * rewrite HC2, HC12.
        repeat rewrite <-app_assoc.
        apply Permutation_app_head.
        repeat rewrite app_assoc.
        apply Permutation_app_tail.
        apply Permutation_app_comm.
  - inv H; EqDep_subst.
    econstructor 9; eauto.
  - inv H; EqDep_subst.
    apply app_eq_nil in HCalls; dest; subst.
    inv H2; simpl in *.
    + econstructor 10; eauto.
    + apply Permutation_nil in H7; discriminate.
Qed.

Lemma Substeps_permutation_invariant m o l l' :
  l [=] l' ->
  Substeps m o l ->
  Substeps m o l'.
Proof.
  induction 1; intros; auto.
  - inv H0.
    + inv HLabel.
      econstructor 2; eauto; setoid_rewrite <- H; auto.
    + inv HLabel.
      econstructor 3; eauto; setoid_rewrite <- H; auto.
  - inv H.
    + inv HLabel.
      inv HSubstep; inv HLabel.
      * specialize (HNoRle _ (in_eq _ _)); simpl in *; contradiction.
      * econstructor 3; eauto; intros.
        -- destruct H; subst.
           ++ simpl.
              specialize (HDisjRegs _ (in_eq _ _)); simpl in *.
              apply DisjKey_Commutative; assumption.
           ++ eapply HDisjRegs0; auto.
        -- econstructor 2; eauto; intros.
           ++ eapply HDisjRegs; right; assumption.
           ++ eapply HNoRle; right; assumption.
    + inv HLabel.
      inv HSubsteps; inv HLabel.
      * econstructor 2; eauto; intros.
        -- destruct H; subst.
           ++ simpl.
              specialize (HDisjRegs _ (in_eq _ _)); simpl in *.
              apply DisjKey_Commutative; assumption.
           ++ eapply HDisjRegs0; auto.
        -- destruct H; subst; simpl in *; auto.
           eapply HNoRle; eauto.
        -- econstructor 3; eauto; intros.
           ++ eapply HDisjRegs; right; assumption.
      * econstructor 3; eauto; intros.
        -- destruct H; subst; simpl.
           ++ specialize (HDisjRegs _ (in_eq _ _)); simpl in *.
              apply DisjKey_Commutative; assumption.
           ++ eapply HDisjRegs0; eauto.
        -- econstructor 3; auto; auto;[apply HAction | | ]; auto; intros.
           ++ eapply HDisjRegs; right; assumption.
Qed.

Global Instance Substeps_perm_rewrite' :
  Proper (eq ==> eq ==> @Permutation FullLabel ==> iff) (@Substeps) | 10.
Proof.
  repeat red; intros; split; intro; subst; eauto using Permutation_sym, Substeps_permutation_invariant.
Qed.

Lemma KeyMatching2 (l : list DefMethT) (a b : DefMethT):
  NoDup (map fst l) -> In a l -> In b l -> fst a = fst b -> a = b.
Proof.
  induction l; intros.
  - inv H0.
  - destruct H0, H1; subst; auto; simpl in *.
    + inv H.
      apply False_ind, H4.
      rewrite H2, in_map_iff.
      exists b; firstorder.
    + inv H.
      apply False_ind, H4.
      rewrite <- H2, in_map_iff.
      exists a; firstorder.
    + inv H.
      eapply IHl; eauto.
Qed.

Lemma extract_exec (f : DefMethT) m o l u cs fb:
  NoDup (map fst (getMethods m)) ->
  In f (getMethods m) ->
  Substeps m o ((u, (Meth ((fst f), fb), cs))::l) ->
  exists reads e mret,
    fb =  existT SignT (projT1 (snd f)) (e, mret) /\
    DisjKey u (getLabelUpds l) /\
    SemAction o ((projT2 (snd f) type) e) reads u cs mret /\
    SubList (getKindAttr u) (getKindAttr (getRegisters m)) /\
    SubList (getKindAttr reads) (getKindAttr (getRegisters m)) /\
    Substeps m o l.
Proof.
  intros.
  inv H1.
  - inv HLabel.
  - inv HLabel.
    destruct f, s0, fb0; simpl in *; subst;EqDep_subst.
    specialize (KeyMatching2 _ _ _ H HInMeths H0 (eq_refl)) as TMP.
    inv TMP; EqDep_subst.
    exists reads, argV, retV; repeat split; auto.
    + apply DisjKey_Commutative.
      clear - HDisjRegs.
      induction ls.
      * intro; left; auto.
      * unfold getLabelUpds in *; simpl.
        intro; rewrite map_app, in_app_iff, DeM1.
        specialize (HDisjRegs a (in_eq _ _) k) as TMP; simpl in *.
        assert (forall x, In x ls -> DisjKey (fst x) u0);[intros; eapply HDisjRegs; eauto|].
        specialize (IHls H k) as TMP2; destruct TMP, TMP2; firstorder fail.
Qed.

Lemma List_FullLabel_perm_getLabelUpds_perm l1 l2:
  List_FullLabel_perm l1 l2 ->
  getLabelUpds l1 [=] getLabelUpds l2.
Proof.
  induction 1.
  - reflexivity.
  - unfold getLabelUpds in *; inv H; simpl in *.
    rewrite H1, IHList_FullLabel_perm; reflexivity.
  - unfold getLabelUpds in *; inv H; inv H0; simpl in *.
    rewrite H2, H, IHList_FullLabel_perm; repeat rewrite app_assoc.
    apply Permutation_app_tail.
    apply Permutation_app_comm.
  - rewrite IHList_FullLabel_perm1, IHList_FullLabel_perm2; reflexivity.
Qed.

Lemma List_FullLabel_perm_getLabelCalls_perm l1 l2:
  List_FullLabel_perm l1 l2 ->
  getLabelCalls l1 [=] getLabelCalls l2.
Proof.
  induction 1.
  - reflexivity.
  - unfold getLabelCalls in *; inv H; simpl in *.
    rewrite H3, IHList_FullLabel_perm; reflexivity.
  - unfold getLabelCalls in *; inv H; inv H0; simpl in *.
    rewrite H4, H5, IHList_FullLabel_perm; repeat rewrite app_assoc.
    apply Permutation_app_tail.
    apply Permutation_app_comm.
  - rewrite IHList_FullLabel_perm1, IHList_FullLabel_perm2; reflexivity.
Qed.

Lemma List_FullLabel_perm_getLabelExecs_perm l1 l2:
  List_FullLabel_perm l1 l2 ->
  getLabelExecs l1 [=] getLabelExecs l2.
Proof.
  induction 1.
  - reflexivity.
  - unfold getLabelExecs in *; inv H; simpl in *.
    rewrite IHList_FullLabel_perm; reflexivity.
  - unfold getLabelExecs in *; inv H; inv H0; simpl in *.
    rewrite IHList_FullLabel_perm.
    apply perm_swap.
  - rewrite IHList_FullLabel_perm1, IHList_FullLabel_perm2; reflexivity.
Qed.

Lemma extract_exec_P (f : DefMethT) m o l u cs fb:
  NoDup (map fst (getMethods m)) ->
  In f (getMethods m) ->
  PSubsteps m o ((u, (Meth ((fst f),fb), cs))::l) ->
  exists reads e mret,
    fb = existT SignT (projT1 (snd f)) (e, mret) /\
    DisjKey u (getLabelUpds l) /\
    PSemAction o ((projT2 (snd f) type) e) reads u cs mret /\
    SubList (getKindAttr u) (getKindAttr (getRegisters m)) /\
    SubList (getKindAttr reads) (getKindAttr (getRegisters m)) /\
    PSubsteps m o l.
Proof.
  intros.
  apply (PSubsteps_Substeps) in H1; dest.
  specialize (List_FullLabel_perm_in H2 _ (in_eq _ _)) as TMP; dest.
  specialize (in_split _ _ H6) as TMP; dest.
  rewrite H7, <- Permutation_middle in H2.
  specialize (List_FullLabel_perm_cons_inv H5 H2) as P2.
  inv H5.
  apply (Substeps_permutation_invariant (Permutation_sym (Permutation_middle _ _ _))) in H4.
  apply (extract_exec f) in H4; auto; dest.
  exists x0, x1, x4; repeat split; auto.
  + rewrite H11.
    rewrite (List_FullLabel_perm_getLabelUpds_perm P2).
    assumption.
  + symmetry in H1, H11, H14.
    apply (PSemAction_rewrite_state H1).
    apply (PSemAction_rewrite_newRegs H11).
    apply (PSemAction_rewrite_calls H14).
    apply SemAction_PSemAction; assumption.
  + rewrite H11; assumption.
  + rewrite P2, H1.
    apply Substeps_PSubsteps; assumption.
Qed.

Corollary extract_exec_PPlus (f : DefMethT) m o upds execs calls fb:
  NoDup (map fst (getMethods m)) ->
  In f (getMethods m) ->
  PPlusSubsteps m o upds ((Meth ((fst f),fb))::execs) calls ->
  exists reads upds1 upds2 calls1 calls2 e mret,
    fb = existT SignT (projT1 (snd f)) (e, mret) /\
    PSemAction o ((projT2 (snd f) type) e) reads upds1 calls1 mret /\
    upds [=] upds1++upds2 /\
    calls [=] calls1++calls2 /\
    DisjKey upds1 upds2 /\
    SubList (getKindAttr upds1) (getKindAttr (getRegisters m)) /\
    SubList (getKindAttr reads) (getKindAttr (getRegisters m)) /\
    PPlusSubsteps m o upds2 execs calls2.
Proof.
  intros.
  apply (PPlusSubsteps_PSubsteps) in H1; dest.
  unfold getLabelExecs, getLabelUpds, getLabelCalls in *.
  specialize (Permutation_in _ H3 (in_eq _ _)) as H3'.
  rewrite (in_map_iff) in H3'; dest; destruct x0, p.
  apply in_split in H6; dest; rewrite H6,map_app in H4, H3, H2;rewrite concat_app in *; simpl in *.
  rewrite H5 in *;rewrite H6, <-Permutation_middle in H1.
  rewrite <- Permutation_middle, <- map_app in H3.
  apply Permutation_cons_inv in H3.
  apply extract_exec_P in H1; eauto; dest.
  exists x2, r, (getLabelUpds (x0++x1)), m0, (getLabelCalls (x0++x1)), x3, x4; repeat split; auto;
    [rewrite H2; unfold getLabelUpds| rewrite H4; unfold getLabelCalls | rewrite H3; apply PSubsteps_PPlusSubsteps; assumption];
    rewrite map_app, concat_app; repeat rewrite app_assoc; apply Permutation_app_tail; rewrite Permutation_app_comm; reflexivity.
Qed.

Lemma SubList_app_l_iff (A : Type) (l1 l2 l : list A) :
  SubList (l1++l2) l <-> SubList l1 l /\ SubList l2 l.
Proof.
  split; intros;[apply SubList_app_l; auto|].
  destruct H; repeat intro; rewrite in_app_iff in H1; destruct H1; eauto.
Qed.

Corollary extract_execs_PPlus (f : DefMethT) m o execs fcalls:
  NoDup (map fst (getMethods m)) ->
  In f (getMethods m) ->
  (forall g, In g fcalls -> (fst g = fst f)) ->
  forall upds calls, 
    PPlusSubsteps m o upds ((map Meth fcalls)++execs) calls ->
    exists reads upds1 upds2 calls1 calls2,
      PSemAction_meth_collector f o reads upds1 calls1 fcalls /\
      calls [=] calls1++calls2 /\
      upds [=] upds1++upds2 /\
      DisjKey upds1 upds2 /\
      SubList (getKindAttr upds1) (getKindAttr (getRegisters m)) /\
      SubList (getKindAttr reads) (getKindAttr (getRegisters m)) /\
      PPlusSubsteps m o upds2 execs calls2.
Proof.
  induction fcalls; simpl; intros.
  - exists nil, nil, upds, nil, calls.
    repeat split; auto.
    + constructor.
    + intro; left; intro; contradiction.
    + repeat intro; contradiction.
    + repeat intro; contradiction.
  - assert (forall g, In g fcalls -> fst g = fst f) as P1;[auto|].
    destruct a; specialize (H1 (s, s0) (or_introl _ eq_refl)) as P2; simpl in P2; rewrite P2 in H2.
    specialize (extract_exec_PPlus _ H H0 H2) as TMP; dest.
    specialize (IHfcalls H H0 P1 _ _ H10); dest.
    exists (x++x6), (x0++x7), x8, (x2++x9), x10.
    repeat split.
    + econstructor 2.
      * apply H11.
      * assert (DisjKey x7 x0) as goal;[|apply goal].
        intro k; specialize (H7 k); rewrite H13, map_app, in_app_iff in H7; clear -H7; firstorder fail.
      * apply Permutation_app_comm.
      * apply Permutation_app_comm.
      * apply Permutation_app_comm.
      * rewrite P2, H3; reflexivity.
      * assumption.
    + rewrite H6, H12, app_assoc; reflexivity.
    + rewrite H5, H13, app_assoc; reflexivity.
    + intro k; specialize (H14 k); specialize (H7 k).
      rewrite H13 in H7.
      rewrite map_app, in_app_iff in *.
      clear -H14 H7; firstorder fail.
    + rewrite map_app, SubList_app_l_iff; auto.
    + rewrite map_app, SubList_app_l_iff; auto.
    + assumption.
Qed.

Lemma getNumFromExecs_gt_0 f execs :
  (0 < getNumFromExecs f execs)%Z ->
  In (Meth f) execs.
Proof.
  induction execs; intros;[inv H|].
  destruct a;[|destruct (MethT_dec f f0)].
  - rewrite getNumFromExecs_Rle_cons in H.
    specialize (IHexecs H).
    right; assumption.
  - subst; left; reflexivity.
  - rewrite getNumFromExecs_neq_cons in H; auto.
    specialize (IHexecs H).
    right; assumption.
Qed.

Lemma getNumFromCalls_gt_0 f calls :
  (0 < getNumFromCalls f calls)%Z ->
  In f calls.
  induction calls; intros;[inv H|].
  destruct (MethT_dec f a).
  - subst; left; reflexivity.
  - rewrite getNumFromCalls_neq_cons in H; auto.
    specialize (IHcalls H).
    right; assumption.
Qed.

Lemma rewrite_called_execs:
  forall calls execs,
    (forall f, getNumFromCalls f calls <= getNumFromExecs f execs)%Z ->
    exists execs',
      execs [=] ((map Meth (calls))++execs').
Proof.
  induction calls; intros.
  - exists execs; reflexivity.
  - specialize (H a) as P1.
    rewrite getNumFromCalls_eq_cons in P1; auto.
    assert ((0 < getNumFromExecs a execs)%Z) as P2;[specialize (getNumFromCalls_nonneg a calls) as TMP1;Omega.omega|].
    specialize (in_split _ _ (getNumFromExecs_gt_0 _ _ P2)) as TMP; dest.
    rewrite H0 in H; setoid_rewrite <-Permutation_middle in H.
    assert (forall f, (getNumFromCalls f calls <= getNumFromExecs f (x++x0))%Z).
    + intros; specialize (H f); destruct (MethT_dec f a);[rewrite getNumFromCalls_eq_cons, getNumFromExecs_eq_cons in H
                                                         |rewrite getNumFromCalls_neq_cons, getNumFromExecs_neq_cons in H];auto;Omega.omega.
    + specialize (IHcalls _ H1); dest.
      exists x1; rewrite H0, <-Permutation_middle.
      simpl; rewrite H2; reflexivity.
Qed.

Lemma MatchingExecCalls_flat_surjective f calls execs m :
  In f (getMethods m) ->
  MatchingExecCalls_flat calls execs m ->
  forall g,
    In g (filter (called_by f) calls) -> In (Meth g) execs.
Proof.
  unfold MatchingExecCalls_flat.
  induction calls; intros.
  - contradiction.
  - unfold called_by in H1; simpl in H1.
    destruct string_dec; subst; simpl in H1.
    + destruct H1; subst.
      * apply (in_map fst) in H; rewrite e in H.
        specialize (H0 _ H).
        rewrite getNumFromCalls_eq_cons in H0; auto.
        specialize (getNumFromCalls_nonneg g calls) as P1.
        apply getNumFromExecs_gt_0; Omega.omega.
      * apply IHcalls; auto.
        intros f0 P1; specialize (H0 _ P1).
        destruct (MethT_dec f0 a);[rewrite getNumFromCalls_eq_cons in H0
                                  |rewrite getNumFromCalls_neq_cons in H0]; auto; Omega.omega.
    + apply IHcalls; auto.
      intros f0 P1; specialize (H0 _ P1).
        destruct (MethT_dec f0 a);[rewrite getNumFromCalls_eq_cons in H0
                                  |rewrite getNumFromCalls_neq_cons in H0]; auto; Omega.omega.
Qed.

Lemma MatchingExecCalls_flat_surjective_split f calls m :
  In f (getMethods m) ->
  forall execs,
    MatchingExecCalls_flat calls execs m ->
    exists execs',
      execs [=] (map Meth (filter (called_by f) calls))++execs'.
Proof.
  unfold MatchingExecCalls_flat.
  induction calls; intros.
  - simpl; exists execs; reflexivity.
  - destruct a, (string_dec (fst f) s).
    + specialize (in_map fst _ _ H) as P1; rewrite e in P1.
      specialize (H0 (s, s0) P1) as P2.
      rewrite getNumFromCalls_eq_cons in P2; auto.
      specialize (getNumFromCalls_nonneg (s, s0) calls) as P3.
      assert (0 < getNumFromExecs (s, s0) execs)%Z as P4;[Omega.omega|].
      specialize (getNumFromExecs_gt_0 _ _ P4) as P5; apply in_split in P5; dest.
      setoid_rewrite H1 in H0; setoid_rewrite <-Permutation_middle in H0.
      assert (forall f, In (fst f) (map fst (getMethods m)) -> (getNumFromCalls f calls <= getNumFromExecs f (x++x0))%Z) as P5.
      * intros f0 HInDef; specialize (H0 _ HInDef).
        destruct (MethT_dec f0 (s, s0));[rewrite getNumFromCalls_eq_cons, getNumFromExecs_eq_cons in H0
                                        |rewrite getNumFromCalls_neq_cons, getNumFromExecs_neq_cons in H0]; auto; Omega.omega.
      * specialize (IHcalls H _ P5); dest.
        exists x1.
        unfold called_by; simpl; destruct string_dec;[simpl|contradiction].
        rewrite H1, <-Permutation_middle, H2; unfold called_by; reflexivity.
    + unfold called_by in *; simpl; destruct string_dec;[contradiction|simpl].
      apply IHcalls; auto.
      intros f0 HInDef; specialize (H0 _ HInDef).
      destruct (MethT_dec f0 (s, s0));[rewrite getNumFromCalls_eq_cons in H0
                                      |rewrite getNumFromCalls_neq_cons in H0]; auto; Omega.omega.
Qed.

Lemma filter_preserves_NoDup A (f : A -> bool) l :
  NoDup l ->
  NoDup (filter f l).
Proof.
  induction 1.
  - simpl; constructor.
  - unfold filter; destruct (f x); fold (filter f l); auto.
    + econstructor; eauto.
      intro; apply H.
      rewrite filter_In in H1; dest; assumption.
Qed.

Lemma InRule_In_inlined f rn rb m:
  In (rn, rb) (getRules m) ->
  In (rn, (fun ty => (inlineSingle f (rb ty)))) (getRules (inlineSingle_Rule_BaseModule f rn m)).
Proof.
  destruct m; simpl in *.
  - intro; contradiction.
  - induction rules.
    + intro; contradiction.
    + intros.
      destruct H; subst.
      * simpl in *.
        destruct string_dec;[|apply False_ind; apply n; reflexivity].
        left; reflexivity.
      * specialize (IHrules H).
        simpl; destruct string_dec; right; assumption.
Qed.

Lemma InRule_In_inlined_neq f rn1 rn2 rb m:
  rn1 <> rn2 ->
  In (rn2, rb) (getRules m) ->
  In (rn2, rb) (getRules (inlineSingle_Rule_BaseModule f rn1 m)).
Proof.
  destruct m; simpl in *.
  - intro; contradiction.
  - induction rules.
    + intro; contradiction.
    + intros.
      destruct H0; subst.
      * simpl; destruct string_dec;[contradiction|].
        left; reflexivity.
      * simpl; destruct string_dec; right; apply (IHrules H H0).
Qed.

Lemma PSubsteps_inlineRule_notIn f m o rn l:
  PSubsteps m o l ->
  ~In (fst f) (map fst (getLabelCalls l)) ->
  PSubsteps (inlineSingle_Rule_BaseModule f rn m) o l.
Proof.
  induction 1; intros.
  - econstructor 1; simpl; assumption.
  - rewrite HLabel in H0.
    pose proof H0 as H0'; unfold getLabelCalls in H0.
    simpl in H0; rewrite map_app, in_app_iff, DeM1 in H0; dest.
    fold (getLabelCalls ls) in H1.
    destruct (string_dec rn rn0).
    + subst.
      specialize (InRule_In_inlined f _ _ _ HInRules) as P1.
      econstructor 2 with(u:=u)(reads:=reads); simpl in *; eauto.
      simpl; apply PSemAction_inline_notIn; auto.
    + specialize (InRule_In_inlined_neq f _ _ n HInRules) as P1.
      econstructor 2 with (u:=u)(reads:=reads); simpl in *; eauto.
  - econstructor 3; simpl; eauto.
    rewrite HLabel in H0.
    unfold getLabelCalls in H0; simpl in H0;
      rewrite map_app, in_app_iff, DeM1 in H0; dest.
    apply (IHPSubsteps H1).
Qed.

Lemma Substeps_inline_Rule_NoExec_PSubsteps f m o rn (l : list FullLabel) :
  NoDup (map fst (getMethods m)) ->
  In f (getMethods m) ->
  ~In (Rle rn) (map getRleOrMeth l) ->
  Substeps m o l ->
  PSubsteps (inlineSingle_Rule_BaseModule f rn m) o l.
Proof.
  induction 4.
  - econstructor 1; simpl; rewrite HRegs; reflexivity.
  - econstructor 2 with (u:= u) (reads:=reads); simpl; eauto.
    + rewrite HRegs; reflexivity.
    + assert (rn <> rn0);
        [intro; subst; apply H1; simpl; left; reflexivity|].
      apply InRule_In_inlined_neq; eauto.
    + apply (SemAction_PSemAction HAction).
    + rewrite HLabel; reflexivity.
    + apply IHSubsteps; auto.
      rewrite HLabel in H1; simpl in H1.
      intro; apply H1; right; assumption.
  - econstructor 3 with (u:=u) (reads:=reads); subst; eauto.
    + rewrite HRegs; reflexivity.
    + apply (SemAction_PSemAction HAction).
    + apply IHSubsteps; auto.
      intro; apply H1; right; assumption.
Qed.

Lemma List_FullLabel_perm_getRleOrMeth l l' :
  List_FullLabel_perm l l' ->
  (map getRleOrMeth l) [=] (map getRleOrMeth l').
Proof.
  induction 1; auto.
  - inv H; simpl; rewrite IHList_FullLabel_perm; reflexivity.
  - inv H; inv H0; simpl.
    rewrite perm_swap; repeat apply perm_skip; assumption.
  - rewrite IHList_FullLabel_perm1, IHList_FullLabel_perm2; reflexivity.
Qed.

Corollary PSubsteps_inline_Rule_NoExec_PSubsteps f m o rn (l : list FullLabel) :
  NoDup (map fst (getMethods m)) ->
  In f (getMethods m) ->
  ~In (Rle rn) (map getRleOrMeth l) ->
  PSubsteps m o l ->
  PSubsteps (inlineSingle_Rule_BaseModule f rn m) o l.
Proof.
  intros.
  apply (PSubsteps_Substeps) in H2; dest.
  rewrite (List_FullLabel_perm_getRleOrMeth H3) in H1.
  rewrite H2, H3.
  apply Substeps_inline_Rule_NoExec_PSubsteps; auto.
Qed.

Corollary PPlusSubsteps_inline_Rule_NoExec_PPlusSubsteps f m o rn upds execs calls :
  NoDup (map fst (getMethods m)) ->
  In f (getMethods m) ->
  ~In (Rle rn) execs ->
  PPlusSubsteps m o upds execs calls ->
  PPlusSubsteps (inlineSingle_Rule_BaseModule f rn m) o upds execs calls.
Proof.
  intros.
  apply PPlusSubsteps_PSubsteps in H2; dest.
  rewrite H3, H4, H5.
  apply PSubsteps_PPlusSubsteps.
  rewrite H4 in H1; unfold getLabelExecs in H1.
  apply PSubsteps_inline_Rule_NoExec_PSubsteps; auto.
Qed.

Lemma Substeps_inline_Rule_NoCall_PSubsteps f m o rn u cs (l : list FullLabel) :
  NoDup (map fst (getMethods m)) ->
  In f (getMethods m) ->
  ~In (fst f) (map fst cs) ->
  Substeps m o ((u, (Rle rn, cs))::l) ->
  PSubsteps (inlineSingle_Rule_BaseModule f rn m) o ((u, (Rle rn, cs))::l).
Proof.
  intros.
  inv H2; inv HLabel.
  econstructor 2 with (u:=u0) (reads:=reads); eauto.
  - rewrite HRegs; reflexivity.
  - apply (InRule_In_inlined f _ _ _ HInRules).
  - apply PSemAction_inline_notIn; auto.
    apply (SemAction_PSemAction HAction).
  - apply Substeps_inline_Rule_NoExec_PSubsteps; auto.
    intro; rewrite in_map_iff in H2; dest.
    specialize (HNoRle _ H3).
    rewrite H2 in HNoRle; contradiction.
Qed.

Lemma PSubsteps_inline_Rule_NoCall_PSubsteps f m o rn u cs (l : list FullLabel) :
  NoDup (map fst (getMethods m)) ->
  In f (getMethods m) ->
  ~In (fst f) (map fst cs) ->
  PSubsteps m o ((u, (Rle rn, cs))::l) ->
  PSubsteps (inlineSingle_Rule_BaseModule f rn m) o ((u, (Rle rn, cs))::l).
Proof.
  intros.
  apply PSubsteps_Substeps in H2; dest.
  rewrite H2, H3.
  specialize (List_FullLabel_perm_in H3 _ (in_eq _ _)) as TMP; dest.
  inv H6; apply in_split in H7; dest; subst.
  rewrite <-Permutation_middle in *.
  rewrite H14 in H1.
  apply Substeps_inline_Rule_NoCall_PSubsteps; auto.
Qed.

Lemma KeyMatching3 A B:
  forall (ab1 ab2 : A*B)(l : list (A*B)),
    NoDup (map fst l) ->
    In ab1 l ->
    In ab2 l ->
    (fst ab1 = fst ab2) ->
    ab1 = ab2.
Proof.
  induction l; intros.
  - inv H0.
  - destruct H0, H1; subst; simpl in *; auto.
    + inv H; apply (in_map fst) in H1; rewrite <-H2 in H1; contradiction.
    + inv H; apply (in_map fst) in H0; rewrite H2 in H0; contradiction.
    + inv H; apply IHl; auto.
Qed.

Lemma ExtractRuleAction m o (rle : RuleT) upds execs calls :
  NoDup (map fst (getRules m)) ->
  In rle (getRules m) ->
  In (Rle (fst rle)) execs ->
  PPlusSubsteps m o upds execs calls ->
  exists reads execs' upds1 upds2 calls1 calls2 retV,
    PSemAction o (snd rle type) reads upds1 calls1 retV /\
    upds [=] upds1++upds2 /\
    calls [=] calls1++calls2 /\
    DisjKey upds2 upds1 /\
    SubList (getKindAttr upds1) (getKindAttr (getRegisters m)) /\
    SubList (getKindAttr reads) (getKindAttr (getRegisters m)) /\
    execs [=] ((Rle (fst rle))::execs') /\
    (forall s, ~In (Rle s) execs') /\
    PPlusSubsteps m o upds2 execs' calls2.
Proof.
  induction 4.
  - inv H1.
  - rewrite HExecs in H1.
    destruct H1;[| specialize (HNoRle _ H1); contradiction].
    inv H1.
    specialize (KeyMatching3 _ _ _ H H0 HInRules (eq_refl)) as P1.
    destruct rle; simpl in *; inv P1; subst.
    exists reads, oldExecs, u, oldUpds, cs, oldCalls, WO.
    repeat split; auto.
    repeat intro; apply (HNoRle _ H1).
  - rewrite HExecs in H1.
    destruct H1;[discriminate|].
    specialize (IHPPlusSubsteps H1); dest.
    exists x, ((Meth (fn, existT _ (projT1 fb) (argV, retV))):: x0), x1, (u++x2), x3, (cs++x4), x5.
    repeat split; auto.
    + rewrite HUpds, H4.
      repeat rewrite app_assoc; apply Permutation_app_tail, Permutation_app_comm.
    + rewrite HCalls, H5.
      repeat rewrite app_assoc; apply Permutation_app_tail, Permutation_app_comm.
    + rewrite H4 in HDisjRegs; intro k; specialize (HDisjRegs k); specialize (H6 k).
      clear - HDisjRegs H6.
      rewrite map_app, in_app_iff in *; firstorder fail.
    + rewrite HExecs, H9; apply perm_swap.
    + repeat intro; destruct H12;[discriminate|eapply H10; eauto].
    + econstructor 3; eauto.
      intro k; specialize (HDisjRegs k);rewrite H4, map_app, in_app_iff in HDisjRegs.
      clear - HDisjRegs; firstorder fail.
Qed.

Lemma PPlus_inline_Rule_with_action f m o rn rb upds1 upds2 execs calls1 calls2 reads:
  In (rn, rb) (getRules m) ->
  In f (getMethods m) ->
  NoDup (map fst (getMethods m)) ->
  (forall rn', ~In (Rle rn') execs) ->
  SubList (getKindAttr reads) (getKindAttr (getRegisters m)) ->
  SubList (getKindAttr upds1) (getKindAttr (getRegisters m)) ->
  DisjKey upds2 upds1 ->
  PSemAction o (inlineSingle f (rb type)) reads upds1 calls1 WO ->
  PPlusSubsteps m o upds2 execs calls2 ->
  PPlusSubsteps (inlineSingle_Rule_BaseModule f rn m) o (upds1++upds2) ((Rle rn)::execs) (calls1++calls2).
Proof.
  intros.
  econstructor; auto.
  - inv H7; simpl in *; auto.
  - apply InRule_In_inlined, H.
  - simpl; apply H6.
  - auto.
  - auto.
  - intros; destruct x; auto.
    apply (H2 rn0); assumption.
  - apply PPlusSubsteps_inline_Rule_NoExec_PPlusSubsteps; auto.
Qed.

Lemma filter_idemp (A : Type) (f : A -> bool) (l : list A) :
  (filter f (filter f l)) = (filter f l).
Proof.
  induction l; auto.
  - simpl; remember (f a) as fa.
    destruct fa; auto.
    simpl; rewrite <-Heqfa, IHl; reflexivity.
Qed.

Lemma filter_complement_nil (A : Type) (f : A -> bool) (l : list A) :
  (filter f (filter (complement f) l)) = nil.
Proof.
  induction l; auto.
  - simpl; remember (f a) as fa.
    destruct fa; auto; simpl.
    rewrite <- Heqfa, IHl; reflexivity.
Qed.

Lemma called_by_fst_eq g f l:
  In g (filter (called_by f) l) ->
  (fst g = fst f).
Proof.
  induction l;[contradiction|].
  unfold called_by; simpl; destruct string_dec; simpl; intros.
  - destruct H; subst; auto.
  - specialize (IHl H); auto.
Qed.

Lemma complement_called_by_neq g f l :
  In g (filter (complement (called_by f)) l) ->
  (fst g <> fst f).
Proof.
  induction l;[contradiction|].
  unfold called_by; simpl; destruct string_dec; simpl; intros.
  - specialize (IHl H); auto.
  - destruct H; subst; auto.
Qed.

Lemma cons_app (A : Type) (a : A) (l1 l2 : list A) :
  a::(l1++l2) = (a::l1)++l2.
Proof.
  auto.
Qed.

Lemma PPlusSubsteps_inline_Rule_In f m o rn rb upds execs calls :
  In (rn, rb) (getRules m) ->
  In f (getMethods m) ->
  NoDup (map fst (getMethods m)) ->
  NoDup (map fst (getRules m)) ->
  In (Rle rn) execs ->
  MatchingExecCalls_flat calls execs m ->
  PPlusSubsteps m o upds execs calls ->
  exists fcalls execs' calls',
    execs [=] (map Meth fcalls)++execs' /\
    calls [=] fcalls++calls' /\
    PPlusSubsteps (inlineSingle_Rule_BaseModule f rn m) o upds execs' calls'.
Proof.
  intros.
  specialize (ExtractRuleAction _ H2 H H3 H5) as TMP; dest.
  rewrite (separate_calls_by_filter x3 (called_by f)) in H8.
  apply (PSemAction_rewrite_calls (separate_calls_by_filter x3 (called_by f))) in H6.
  exists (filter (called_by f) x3).
  specialize (MatchingExecCalls_flat_surjective_split _ H0 H4) as TMP; dest.
  specialize (in_eq (Rle (fst (rn, rb))) x0); rewrite <-H12, H15, in_app_iff; intro; destruct H16;
    [apply False_ind;clear - H16; induction calls; auto; simpl in H16;(destruct (called_by f a));auto; simpl in *; destruct H16; auto; discriminate|].
  apply in_split in H16; dest; rewrite H16, <-Permutation_middle in H15.
  rewrite H12, Permutation_app_comm in H15; simpl in *; apply Permutation_cons_inv in H15.
  rewrite Permutation_app_comm in H15; rewrite H15 in H14.
  rewrite H8 in H14; repeat rewrite filter_app in H14.
  rewrite filter_idemp, filter_complement_nil, app_nil_r, map_app, <-app_assoc in H14.
  rewrite <-app_assoc in H8.
  exists ((map Meth (filter (called_by f) x4))++x6), ((filter (complement (called_by f)) x3)++x4).
  repeat split; auto.
  - rewrite H12, H15, H16, H8; repeat rewrite filter_app, map_app; rewrite filter_idemp, filter_complement_nil; simpl.
    repeat rewrite app_assoc; rewrite Permutation_app_comm.
    repeat rewrite <- app_assoc.
    rewrite cons_app, Permutation_app_comm; repeat rewrite <-app_assoc; simpl; reflexivity.
  - assert (forall g, In g (filter (called_by f) x3) -> (fst g = fst f)) as P1;[eauto using called_by_fst_eq|].
    specialize (extract_execs_PPlus _ _ _ H1 H0 P1 H14) as TMP; dest.
    assert (~In (fst f) (map fst (filter (complement (called_by f)) x3))) as P2;
      [intro; rewrite in_map_iff in H24; dest; apply (complement_called_by_neq) in H25; contradiction|].
    assert (DisjKey x10 x1) as P3;[intro k; specialize (H9 k); rewrite H19, map_app, in_app_iff in H9; clear - H9; firstorder fail|].
    specialize (PSemAction_inline_In _ H6 P2 P3 H17) as P4.
    rewrite Permutation_app_comm.
    rewrite H7, H16, <-Permutation_middle; simpl.
    rewrite H18, H19.
    assert (x1++x10++x11 [=] (x10++x1)++x11) as P5;
      [rewrite app_assoc; apply Permutation_app_tail, Permutation_app_comm| rewrite P5].
    assert ((filter (complement (called_by f)) x3) ++ x12 ++ x13 [=] (x12 ++ (filter (complement (called_by f)) x3))++x13) as P6;
      [rewrite app_assoc; apply Permutation_app_tail, Permutation_app_comm| rewrite P6].
    rewrite (shatter_word_0) in P4.
    eapply PPlus_inline_Rule_with_action with (reads:= (x9++x)); eauto.
    + intro; rewrite <-H18, Permutation_app_comm; rewrite H8 in H15; repeat rewrite filter_app, map_app in H15; rewrite filter_idemp, filter_complement_nil in H15.
      simpl in *; specialize (H13 rn'); rewrite H15 in H13; repeat rewrite in_app_iff in *; clear - H13; firstorder fail.
    + rewrite map_app, SubList_app_l_iff; auto.
    + rewrite map_app, SubList_app_l_iff; auto.
    + intro k; specialize (H20 k); specialize (H9 k); rewrite H19,map_app, in_app_iff in *.
      clear - H20 H9; firstorder fail.
    + rewrite <-H18, Permutation_app_comm; assumption.
Qed.

Lemma call_execs_counts_eq f calls :
  getNumFromCalls f calls = getNumFromExecs f (map Meth calls).
Proof.
  Opaque getNumFromCalls. Opaque getNumFromExecs.
  induction calls; auto.
  destruct (MethT_dec f a).
  - simpl; rewrite getNumFromCalls_eq_cons, getNumFromExecs_eq_cons; auto; rewrite IHcalls; reflexivity.
  - simpl; rewrite getNumFromCalls_neq_cons, getNumFromExecs_neq_cons; auto.
  Transparent getNumFromCalls. Transparent getNumFromExecs.
Qed.

Corollary MatchingExecCalls_Base_subtract_fcalls m calls calls' execs execs' fcalls:
  MatchingExecCalls_flat calls execs m ->
  execs [=] (map Meth fcalls)++execs' ->
  calls [=] fcalls++calls' ->
  MatchingExecCalls_flat calls' execs' m.
Proof.
  unfold MatchingExecCalls_flat; intros.
  specialize (H _ H2); rewrite H0, H1, getNumFromCalls_app, getNumFromExecs_app in H.
  rewrite (call_execs_counts_eq f fcalls) in H; Omega.omega.
Qed.

Lemma PPlusStep_inline_Rule_NotIn f m o rn upds execs calls :
  NoDup (map fst (getMethods m)) ->
  In f (getMethods m) ->
  ~In (Rle rn) execs ->
  PPlusStep m o upds execs calls ->
  PPlusStep (inlineSingle_Rule_BaseModule f rn m) o upds execs calls.
Proof.
  induction 4.
  econstructor; eauto.
  apply PPlusSubsteps_inline_Rule_NoExec_PPlusSubsteps; auto.
Qed.
  
Lemma PPlusStep_inline_Rule_In f m o rn rb upds execs calls :
  In (rn, rb) (getRules m) ->
  In f (getMethods m) ->
  NoDup (map fst (getRules m)) ->
  NoDup (map fst (getMethods m)) ->
  In (Rle rn) execs ->
  PPlusStep m o upds execs calls ->
  exists fcalls execs' calls',
    execs [=] (map Meth fcalls)++execs' /\
    calls [=] fcalls++calls' /\
    PPlusStep (inlineSingle_Rule_BaseModule f rn m) o upds execs' calls'.
Proof.
  induction 6.
  specialize (PPlusSubsteps_inline_Rule_In _ _ _ H H0 H2 H1 H3 H5 H4) as TMP; dest.
  exists x, x0, x1.
  repeat split; auto.
  apply (MatchingExecCalls_Base_subtract_fcalls _ _ _ H5 H6 H7).
Qed.

Lemma PPlusTrace_inline_Rule_NotIn f m o rn tl :
  NoDup (map fst (getMethods m)) ->
  In f (getMethods m) ->
  (forall t, In t tl -> ~In (Rle rn) (fst (snd t))) ->
  PPlusTrace m o tl ->
  PPlusTrace (inlineSingle_Rule_BaseModule f rn m) o tl.
Proof.
  induction 4.
  - subst; econstructor; eauto.
  - subst; econstructor 2; eauto.
    + apply IHPPlusTrace; auto;intros; apply (H1 _ (in_cons _ _ _ H3)).
    + specialize (H1 _ (in_eq _ _ )); simpl in *.
      apply (PPlusStep_inline_Rule_NotIn _ _ H H0 H1 HPPlusStep).
Qed.

Lemma RuleOrMeth_dec :
  forall (rm1 rm2 : RuleOrMeth), {rm1=rm2}+{rm1<>rm2}.
Proof.
  intros.
  destruct rm1, rm2; simpl in *.
  - destruct (string_dec rn rn0); subst; auto.
    right; intro; inv H; apply n; reflexivity.
  - right; intro; discriminate.
  - right; intro; discriminate.
  - destruct (MethT_dec f f0); subst; auto.
    right; intro; inv H; apply n; reflexivity.
Qed.

Lemma PPlusSubsteps_inlined_undef_Rule f rn m o upds execs calls:
  ~In rn (map fst (getRules m)) ->
  PPlusSubsteps m o upds execs calls ->
  PPlusSubsteps (inlineSingle_Rule_BaseModule f rn m) o upds execs calls.
Proof.
  induction 2.
  - econstructor 1; eauto.
  - rewrite HUpds, HExecs, HCalls; econstructor 2; eauto.
    simpl; induction (getRules m);[contradiction|].
    simpl; destruct (string_dec rn (fst a)); subst.
    + apply False_ind, H; simpl; left; reflexivity.
    + simpl in H; assert (~In rn (map fst l)); auto.
      specialize (IHl H1).
      destruct HInRules; subst;[left; reflexivity|].
      right; apply IHl; auto.
  - rewrite HUpds, HExecs, HCalls; econstructor 3; eauto.
Qed.      

Lemma PPlusStep_inlined_undef_Rule f rn m o upds execs calls:
  ~In rn (map fst (getRules m)) ->
  PPlusStep m o upds execs calls ->
  PPlusStep (inlineSingle_Rule_BaseModule f rn m) o upds execs calls.
Proof.
  induction 2.
  - econstructor 1; eauto.
    apply PPlusSubsteps_inlined_undef_Rule; auto.
Qed.      

Lemma WfActionT_inline_Rule (k : Kind) m (a : ActionT type k) rn f:
  WfActionT m a ->
  WfActionT (inlineSingle_Rule_BaseModule f rn m) a.
Proof.
  intros; induction H; econstructor; auto.
Qed.

Lemma WfActionT_inline_Rule_inline_action (k : Kind) m (a : ActionT type k) rn (f : DefMethT):
  WfActionT m a ->
  (forall v, WfActionT m (projT2 (snd f) type v)) ->
  WfActionT (inlineSingle_Rule_BaseModule f rn m) (inlineSingle f a).
Proof.
  induction 1; try econstructor; eauto.
  simpl.
  destruct string_dec;[destruct Signature_dec|]; subst; econstructor; eauto.
  econstructor.
  intros.
  specialize (H1 v).
  apply (WfActionT_inline_Rule); auto.
Qed.

Lemma inlineSingle_Rule_BaseModule_dec ty rule f rn l:
  In rule (inlineSingle_Rule_in_list f rn l) ->
  In rule l \/
  exists rule',
    In rule' l /\
    (fst rule' = fst rule) /\
    ((inlineSingle f (snd rule' ty)) = snd rule ty).
Proof.
  induction l.
  - intros; auto.
  - simpl; destruct string_dec; subst; intros.
    + destruct H; subst; destruct a; simpl in *.
      * right; exists (s, a); simpl; repeat split; auto.
      * destruct (IHl H); auto.
        dest.
        right; exists x; auto.
    + destruct H; auto.
      destruct (IHl H); auto.
      dest.
      right; exists x; auto.
Qed.

Lemma inlineSingle_Rule_BaseModule_dec2 f rn rb l:
  In (rn, rb) l ->
  In (rn, fun ty : Kind -> Type => inlineSingle f (rb ty)) (inlineSingle_Rule_in_list f rn l).
Proof.
  induction l;[contradiction|].
  intros; simpl in *.
  destruct string_dec, a; subst; simpl in *.
  - destruct H;[inv H|];auto.
  - destruct H;[inv H; exfalso; apply n|];auto.
Qed.

Lemma inlineSingle_Rule_preserves_names f rn l:
  (map fst l) = (map fst (inlineSingle_Rule_in_list f rn l)).
Proof.
  induction l; auto.
  simpl; destruct string_dec, a; simpl;rewrite IHl; reflexivity.
Qed.

Lemma WfMod_Rule_inlined m f rn :
  WfMod (Base m) ->
  In f (getMethods m) ->
  WfMod (Base (inlineSingle_Rule_BaseModule f rn m)).
Proof.
  intros; inv H; econstructor; eauto.
  - inv HWfBaseModule.
    split; intros; simpl in *; dest; try inv HWfBaseModule; eauto; repeat split; intros; pose proof (H1 _ H0); auto.
    + destruct (inlineSingle_Rule_BaseModule_dec type _ _ _ _ H2).
      * specialize (H _ H7); apply WfActionT_inline_Rule; auto.
      * dest.
        specialize (H _ H7).
        rewrite <- H9.
        apply WfActionT_inline_Rule_inline_action; auto.
    + apply WfActionT_inline_Rule; auto.
    + rewrite <- inlineSingle_Rule_preserves_names; auto.
Qed.    

Lemma PPlusStrongTraceInclusion_inlining_Rules_r m f rn :
  In f (getMethods m) ->
  (WfMod (Base m)) ->
  StrongPPlusTraceInclusion m (inlineSingle_Rule_BaseModule f rn m).
Proof.
  unfold StrongPPlusTraceInclusion; induction 3; subst.
  - exists nil; split.
    + econstructor; eauto.
    + constructor.
  - dest.
    pose proof H0 as sth.
    specialize (H0).
      destruct (in_dec (RuleOrMeth_dec) (Rle rn) execs),(in_dec string_dec rn (map fst (getRules m))); inv H0.
    * rewrite in_map_iff in i0; dest; destruct x0; simpl in *; subst.
      destruct HWfBaseModule as [? [? [NoDupMeths [NoDupRegisters NoDupRle]]]].
      specialize (PPlusStep_inline_Rule_In _ _ _ H4 H NoDupRle NoDupMeths i HPPlusStep) as TMP; dest.
      exists ((upds, (x1, x2))::x); split.
      -- econstructor 2; eauto.
      -- constructor; auto.
         unfold WeakInclusion_flat, getListFullLabel_diff_flat.
         split; intros.
         ++ simpl;rewrite H6, H7, getNumFromExecs_app, getNumFromCalls_app, (call_execs_counts_eq); Omega.omega.
         ++ simpl in *.
            destruct H9; exists x3.
            rewrite H6, in_app_iff; right; assumption.
    * exists ((upds, (execs, calls))::x); split.
      -- econstructor 2; eauto.
         apply PPlusStep_inlined_undef_Rule; auto.
      -- econstructor; eauto.
         unfold WeakInclusion_flat; split; intros; auto.
    * exists ((upds, (execs, calls))::x); split.
      -- econstructor 2; eauto.
         apply (PPlusStep_inline_Rule_NotIn); auto.
         inv HWfBaseModule; dest; auto.
      -- econstructor; eauto.
         unfold WeakInclusion_flat; split; intros; auto.
    * exists ((upds, (execs, calls))::x); split.
      -- econstructor 2; eauto.
         apply (PPlusStep_inline_Rule_NotIn); auto.
         inv HWfBaseModule; dest; auto.
      -- econstructor; eauto.
         unfold WeakInclusion_flat; split; intros; auto.
Qed.

Theorem TraceInclusion_inlining_Rules_r m f rn :
  In f (getMethods m) ->
  (WfMod (Base m)) ->
  TraceInclusion (Base m) (Base (inlineSingle_Rule_BaseModule f rn m)).
Proof.
  intros.
  apply PPlusTraceInclusion_TraceInclusion; auto.
  intros.
  specialize (H0).
  apply (WfMod_Rule_inlined); auto.
  eauto using StrongPPlusTraceInclusion_PPlusTraceInclusion, PPlusStrongTraceInclusion_inlining_Rules_r.
Qed.


Lemma WfBaseMod_Rule_inlined m f rn:
  WfBaseModule m ->
  In f (getMethods m) ->
  WfBaseModule (inlineSingle_Rule_BaseModule f rn m).
Proof.
  intros.
  specialize (WfMod_Rule_inlined (m:=m) f rn); intros.
  assert (WfMod m) as TMP;[constructor; auto|specialize (H1 TMP H0); clear TMP].
  inversion H1; auto.
Qed.

Definition inlineSingle_Rule_BaseModuleWf {f} rn {m: BaseModuleWf} (inMeths: In f (getMethods m)):=
  Build_BaseModuleWf (WfBaseMod_Rule_inlined f rn (wfBaseModule m) inMeths).

Theorem TraceInclusion_inlining_Rules_Wf_r {f} {m : BaseModuleWf} rn
        (inMeths: In f (getMethods m)):
  TraceInclusion m (inlineSingle_Rule_BaseModuleWf rn inMeths).
Proof.
  simpl; apply TraceInclusion_inlining_Rules_r; eauto.
  constructor; apply wfBaseModule.
Qed.

Lemma ProjT1_inline_eq (f g : DefMethT):
  (projT1 (snd g)) = (projT1 (snd (inlineSingle_Meth f g))).
Proof.
  destruct g, s0; simpl; destruct string_dec; simpl; reflexivity.
Qed.

Lemma InMeth_In_inlined f gn gb m:
  gn <> (fst f) ->
  In (gn, gb) (getMethods m) ->
  In (inlineSingle_Meth f (gn, gb)) (getMethods (inlineSingle_Meth_BaseModule f gn m)).
Proof.
  simpl; induction (getMethods m); intros.
  - contradiction.
  - destruct H0; subst.
    + simpl; destruct string_dec;[|destruct string_dec]; simpl; auto.
      * apply False_ind, H; subst; reflexivity.
      * apply False_ind, n0; reflexivity.
    + simpl; destruct string_dec;[apply False_ind, H; subst|destruct string_dec;simpl;right];eauto.
Qed.

Lemma InMeth_In_inlined_neq f gn1 gn2 gb m:
  gn1 <> gn2 ->
  In (gn2, gb) (getMethods m) ->
  In (gn2, gb) (getMethods (inlineSingle_Meth_BaseModule f gn1 m)).
Proof.
  simpl; induction (getMethods m); intros.
  - contradiction.
  - destruct H0; subst; simpl; auto.
    + destruct string_dec;[destruct string_dec; contradiction|left; reflexivity].
    + destruct string_dec; right; apply IHl; auto.
Qed.

Lemma extract_meths_PPlus gn m o upds execs calls :
  NoDup (map fst (getMethods m)) ->
  PPlusSubsteps m o upds execs calls ->
  exists upds1 upds2 fexecs1 execs2 calls1 calls2,
    PPlusSubsteps m o upds1 (map Meth fexecs1) calls1 /\
    upds [=] upds1++upds2 /\
    calls [=] calls1++calls2 /\
    DisjKey upds2 upds1 /\
    execs [=] (map Meth fexecs1)++execs2 /\
    (forall g, In g fexecs1 -> (fst g = gn)) /\
    (forall fb, ~In (Meth (gn, fb)) execs2) /\
    PPlusSubsteps m o upds2 execs2 calls2.
Proof.
  induction 2.
  - exists nil, nil, nil, nil, nil, nil.
    repeat split; simpl; try constructor; auto.
    intros; contradiction.
  - dest.
    exists x, (u++x0), x1, (Rle rn::x2), x3, (cs++x4).
    repeat split; auto.
    + rewrite HUpds, H2; repeat rewrite app_assoc.
      apply Permutation_app_tail, Permutation_app_comm.
    + rewrite HCalls, H3; repeat rewrite app_assoc.
      apply Permutation_app_tail, Permutation_app_comm.
    + intro k; specialize (H4 k); specialize (HDisjRegs k).
      rewrite H2, map_app, in_app_iff in *.
      clear -HDisjRegs H4; firstorder fail.
    + rewrite HExecs, H5; apply Permutation_middle.
    + repeat intro.
      destruct H9;[discriminate|specialize (H7 fb); contradiction].
    + econstructor 2; eauto.
      * intro k; specialize (HDisjRegs k); rewrite H2,map_app,in_app_iff in HDisjRegs.
        clear - HDisjRegs; firstorder fail.
      * intros x5 HInx5; specialize (HNoRle x5).
        rewrite H5, in_app_iff in HNoRle.
        apply (HNoRle (or_intror _ HInx5)).
  - dest.
    destruct (string_dec fn gn).
    + subst.
      exists (u++x), x0, ((gn, existT _ (projT1 fb) (argV, retV))::x1), x2, (cs++x3), x4.
      repeat split; auto.
      * econstructor 3; eauto.
        -- simpl; reflexivity.
        -- intro k; specialize (HDisjRegs k).
           rewrite H2, map_app, in_app_iff in HDisjRegs.
           clear - HDisjRegs; firstorder fail.
      * rewrite HUpds, H2, app_assoc; reflexivity.
      * rewrite HCalls, H3, app_assoc; reflexivity.
      * intro k; specialize (H4 k); specialize (HDisjRegs k).
        rewrite H2, map_app, in_app_iff in *.
        clear - H4 HDisjRegs; firstorder fail.
      * rewrite HExecs, H5; simpl; reflexivity.
      * simpl; intros.
        destruct H9;[subst|apply H6];auto.
    + exists x, (u++x0), x1, (Meth (fn, existT _ (projT1 fb) (argV, retV))::x2), x3, (cs++x4).
      repeat split; auto.
      * rewrite HUpds, H2; repeat rewrite app_assoc; apply Permutation_app_tail, Permutation_app_comm.
      * rewrite HCalls, H3; repeat rewrite app_assoc; apply Permutation_app_tail, Permutation_app_comm.
      * intro k; specialize (H4 k); specialize (HDisjRegs k).
        rewrite H2, map_app, in_app_iff in *.
        clear - H4 HDisjRegs; firstorder fail.
      * rewrite HExecs, H5; apply Permutation_middle.
      * repeat intro.
        destruct H9;[inv H9; apply n; reflexivity|eapply H7; eauto].
      * econstructor 3; eauto.
        intro k; specialize (HDisjRegs k).
        rewrite H2, map_app, in_app_iff in HDisjRegs.
        clear - HDisjRegs; firstorder fail.
Qed.

Lemma PPlusSubsteps_inlineMeth_NotIn f gn m o upds execs calls :
  In gn (map fst (getMethods m)) ->
  NoDup (map fst (getMethods m)) ->
  (gn <> fst f) ->
  (~In (fst f) (map fst calls)) ->
  PPlusSubsteps m o upds execs calls ->
  PPlusSubsteps (inlineSingle_Meth_BaseModule f gn m) o upds execs calls.
Proof.
  induction 5.
  - econstructor 1; eauto.
  - rewrite HUpds, HExecs, HCalls in *; econstructor 2; eauto.
    apply IHPPlusSubsteps; rewrite map_app, in_app_iff in H2; clear - H2; firstorder fail.
  - assert (~In (fst f) (map fst cs)) as P1;[rewrite HCalls,map_app,in_app_iff in H2; firstorder fail|].
    specialize (PSemAction_inline_notIn _ HPAction P1) as P2.
    destruct (string_dec gn fn); subst.
    + specialize (InMeth_In_inlined _ _ _ H1 HInMeths); simpl; intro P3; destruct fb; simpl in *.
      destruct string_dec; rewrite HUpds, HExecs, HCalls in *.
      * econstructor 3; simpl; eauto.
      * econstructor 3; simpl; eauto.
        apply IHPPlusSubsteps; clear - H2; rewrite map_app, in_app_iff in H2; firstorder fail.
    + specialize (InMeth_In_inlined_neq f _ _ n HInMeths) as P3.
      rewrite HUpds, HExecs, HCalls in *; econstructor 3; eauto.
      apply IHPPlusSubsteps.
      clear - H2; rewrite map_app, in_app_iff in H2; firstorder fail.
Qed.
      
Lemma ExtractMethAction m o (g : DefMethT) (f : MethT) upds execs calls :
  NoDup (map fst (getMethods m)) ->
  In g (getMethods m) ->
  In (Meth f) execs ->
  fst g = fst f ->
  PPlusSubsteps m o upds execs calls ->
  exists reads execs' upds1 upds2 calls1 calls2 argV retV,
    PSemAction o (projT2 (snd g) type argV) reads upds1 calls1 retV /\
    upds [=] upds1++upds2 /\
    calls [=] calls1++calls2 /\
    DisjKey upds2 upds1 /\
    SubList (getKindAttr upds1) (getKindAttr (getRegisters m)) /\
    SubList (getKindAttr reads) (getKindAttr (getRegisters m)) /\
    execs [=] ((Meth f)::execs') /\
    snd f = existT SignT (projT1 (snd g)) (argV, retV) /\
    PPlusSubsteps m o upds2 execs' calls2.
Proof.
  induction 5.
  - inv H1.
  - rewrite HExecs in H1.
    destruct H1;[discriminate|].
    specialize (IHPPlusSubsteps H1); dest.
    exists x, ((Rle rn)::x0), x1, (u++x2), x3, (cs++x4), x5, x6.
    repeat split; auto.
    + rewrite HUpds, H5.
      repeat rewrite app_assoc; apply Permutation_app_tail, Permutation_app_comm.
    + rewrite HCalls, H6.
      repeat rewrite app_assoc; apply Permutation_app_tail, Permutation_app_comm.
    + rewrite H5 in HDisjRegs; intro k; specialize (HDisjRegs k); specialize (H7 k).
      clear - HDisjRegs H7.
      rewrite map_app, in_app_iff in *; firstorder fail.
    + rewrite HExecs, H10; apply perm_swap.
    + econstructor 2; eauto.
      * intro k; specialize (HDisjRegs k); rewrite H5, map_app, in_app_iff in HDisjRegs.
        clear - HDisjRegs; firstorder fail.
      * intros; eapply HNoRle; eauto.
        rewrite H10; right; assumption.
  - rewrite HExecs in H1.
    destruct H1.
    + destruct g; inv H1; simpl in *.
      specialize (KeyMatching3 _ _ _ H H0 HInMeths H2) as P1;inv P1.
      exists reads, oldExecs, u, oldUpds, cs, oldCalls, argV, retV.
      repeat split; auto.
    + specialize (IHPPlusSubsteps H1); dest. 
    exists x, ((Meth (fn, existT _ (projT1 fb) (argV, retV)))::x0), x1, (u++x2), x3, (cs++x4), x5, x6.
    repeat split; auto.
    * rewrite HUpds, H5.
      repeat rewrite app_assoc; apply Permutation_app_tail, Permutation_app_comm.
    * rewrite HCalls, H6.
      repeat rewrite app_assoc; apply Permutation_app_tail, Permutation_app_comm.
    * rewrite H5 in HDisjRegs; intro k; specialize (HDisjRegs k); specialize (H7 k).
      clear - HDisjRegs H7.
      rewrite map_app, in_app_iff in *; firstorder fail.
    * rewrite HExecs, H10; apply perm_swap.
    * econstructor 3; eauto.
      -- intro k; specialize (HDisjRegs k); rewrite H5, map_app, in_app_iff in HDisjRegs.
         clear - HDisjRegs; firstorder fail.
Qed.

Lemma inline_meths_PPlus f gn m o :
  forall gexecs fcalls upds1 upds2 calls1 calls2 reads,
    PPlusSubsteps m o upds2 (map Meth gexecs) (fcalls++calls2) ->
    (forall g, In g fcalls -> (fst g = fst f)) ->
    PSemAction_meth_collector f o reads upds1 calls1 fcalls ->
    DisjKey upds2 upds1 ->
    SubList (getKindAttr reads) (getKindAttr (getRegisters m)) ->
    SubList (getKindAttr upds1) (getKindAttr (getRegisters m)) ->
    gn <> fst f ->
    NoDup (map fst (getMethods m)) ->
    (~In (fst f) (map fst calls2)) ->
    (forall g, In g gexecs -> (fst g = gn)) ->
    PPlusSubsteps (inlineSingle_Meth_BaseModule f gn m) o (upds1++upds2) (map Meth gexecs) (calls1++calls2).
Proof.
  induction gexecs; simpl.
  - intros; inv H.
    + specialize (app_eq_nil _ _ (eq_sym H10)) as TMP; dest; subst.
      inv H1; simpl in *.
      * econstructor 1; eauto.
      * apply Permutation_nil in H14; inv H14.
    + apply Permutation_nil in HExecs; inv HExecs.
    + apply Permutation_nil in HExecs; inv HExecs.
  - intros.
    assert (exists g, In g (getMethods m) /\ fst g = gn) as TMP.
    + inv H.
      * apply False_ind; assert (In (Rle rn) (Meth a:: map Meth gexecs));[rewrite HExecs; left; reflexivity|].
        clear - H; induction gexecs;simpl in H;[destruct H;[discriminate|contradiction]|].
        destruct H;[discriminate|destruct H;[discriminate|apply (IHgexecs (or_intror H))]].
      * exists (fn, fb); split; auto; simpl.
        assert (In (Meth (fn, existT _ (projT1 fb) (argV, retV))) (Meth a :: map Meth gexecs));
          [rewrite HExecs; left; reflexivity
          |destruct H;[inv H; apply (H8 _ (or_introl _ eq_refl))|]].
        rewrite in_map_iff in H; dest; inv H.
        apply (H8 _ (or_intror _ H9)).
    + dest; destruct x; simpl in *; subst.
      specialize (H8 _ (or_introl _ eq_refl)) as TMP.
      assert (fst (gn, s0) = fst a) as P1; auto; clear TMP.
      specialize (ExtractMethAction  _ _ H6 H9 (in_eq _ _) P1 H) as TMP; dest.
      apply Permutation_cons_inv in H16; rewrite <-H16 in H18.
      assert (fcalls [=] filter (called_by f) (x3++x4)) as P2;
        [rewrite <-H12, filter_app; rewrite (notIn_filter_nil f calls2); auto; rewrite (collector_called_by_filter_irrel H1), app_nil_r; reflexivity|].
      specialize (separate_calls_by_filter (x3++x4) (called_by f)) as P3; rewrite <-H12 in P3 at 1; rewrite P2 in P3; apply Permutation_app_inv_l in P3.
      rewrite P2, filter_app in H1.
      apply collector_split in H1; dest.
      rewrite (separate_calls_by_filter x4 (called_by f)) in H18.
      assert (forall g, In g gexecs -> fst g = gn) as P4; auto.
      specialize (InMeth_In_inlined _ _ _ H5 H9) as P5; destruct s0; simpl in *.
      destruct string_dec; [clear - H5 e; apply False_ind, H5; subst; reflexivity|].
      econstructor 3.
      * clear - H18; inv H18; auto.
      * apply P5.
      * simpl. apply (PSemAction_rewrite_calls (separate_calls_by_filter x3 (called_by f))) in H10.
        assert (~In (fst f) (map fst (filter (complement (called_by f)) x3))) as P6;
          [clear; induction x3; simpl; intros;[|unfold called_by in *; destruct string_dec; simpl; intro;[|destruct H]]|]; auto.
        assert (DisjKey x9 x1) as P7;
          [intro k; specialize (H2 k); rewrite H19, H11 in H2; repeat rewrite map_app, in_app_iff in H2; clear - H2; firstorder fail|].
        apply (PSemAction_inline_In _ H10 P6 P7 H22).
      * rewrite H1 in H3; clear - H3 H15; rewrite map_app, SubList_app_l_iff in *; dest; split; auto.
      * rewrite H19 in H4; clear - H4 H14; rewrite map_app, SubList_app_l_iff in *; dest; split; auto.
      * rewrite H19, H11; repeat rewrite <-app_assoc.
        apply Permutation_app_head.
        rewrite Permutation_app_comm, <-app_assoc.
        apply Permutation_app_head, Permutation_app_comm.
      * simpl. destruct a; simpl in *; rewrite H17; rewrite P1; reflexivity.
      * rewrite H20, P3; repeat rewrite <-app_assoc.
        apply Permutation_app_head; rewrite filter_app.
        rewrite Permutation_app_comm, <-app_assoc.
        apply Permutation_app_head, Permutation_app_comm.
      * intro k; specialize (H13 k); specialize (H21 k); specialize (H2 k).
        rewrite H19, H11 in H2; clear - H13 H21 H2.
        repeat rewrite map_app, in_app_iff in *.
        firstorder fail.
      * eapply IHgexecs; eauto.
        -- clear; unfold called_by; simpl; induction x4; intros;[contradiction|].
           simpl in H; destruct string_dec; simpl in *;
             [destruct H; subst; auto|apply (IHx4 _ H)].
        -- intro k; specialize (H2 k); rewrite H19, H11 in H2; clear - H2.
           repeat rewrite map_app, in_app_iff in *; firstorder fail.
        -- rewrite H1, map_app, SubList_app_l_iff in H3; dest; auto.
        -- rewrite H19, map_app, SubList_app_l_iff in H4; dest; auto.
        -- clear; induction x4; unfold called_by in *; simpl; auto.
           destruct string_dec; simpl; auto.
           intro; destruct H;[apply n; rewrite H; reflexivity|contradiction].
Qed.

Lemma PPlusSubsteps_inline_Meth_NoExec_PPlusSubsteps f m o gn upds execs calls :
  NoDup (map fst (getMethods m)) ->
  In f (getMethods m) ->
  (forall gb, ~In (Meth (gn, gb)) execs) ->
  PPlusSubsteps m o upds execs calls ->
  PPlusSubsteps (inlineSingle_Meth_BaseModule f gn m) o upds execs calls.
Proof.
  induction 4.
  - econstructor 1; eauto.
  - rewrite HUpds, HExecs, HCalls; econstructor 2; eauto.
    apply IHPPlusSubsteps.
    repeat intro; apply (H1 gb); rewrite HExecs; right; assumption.
  - rewrite HUpds, HExecs, HCalls; econstructor 3; eauto.
    apply InMeth_In_inlined_neq; auto.
    + intro; subst; eapply H1.
      rewrite HExecs; left; reflexivity.
    + eapply IHPPlusSubsteps.
      repeat intro; apply (H1 gb); rewrite HExecs; right; assumption.
Qed.

Lemma Disjoint_list_split (A : Type):
  forall (l1 l2 l3 l4 : list A),
    l1 ++ l2 [=] l3 ++ l4 ->
    (forall a, ~In a l1 \/ ~In a l3) ->
    exists l5,
      l4 [=] l1++l5.
Proof.
  induction l1; simpl; intros.
  - exists l4; reflexivity.
  - assert (In a l4).
    + specialize (in_app_or l3 l4 a); rewrite <-H; intros.
      specialize (H1 (in_eq _ _)).
      destruct H1;auto.
      apply False_ind.
      destruct (H0 a);[firstorder fail|contradiction].
    + apply in_split in H1; dest.
      rewrite H1 in H.
      assert (l3 ++ x ++ a::x0 [=] a::l3++x++x0);
        [rewrite <-Permutation_middle; repeat rewrite app_assoc, app_comm_cons;
         apply Permutation_app_tail, Permutation_sym, Permutation_middle|].
      rewrite H2 in H; apply Permutation_cons_inv in H.
      assert (forall a, (~In a l1 \/ ~In a l3));
        [intros; specialize (H0 a0); firstorder fail|].
      specialize (IHl1 _ _ _ H H3); dest.
      exists x1.
      rewrite <-H4, H1; apply Permutation_sym, Permutation_middle.
Qed.

Lemma PPlusSubsteps_exec_Rule_defined m o upds execs calls rn :
  In (Rle rn) execs ->
  PPlusSubsteps m o upds execs calls ->
  exists rb,
    In (rn, rb) (getRules m).
Proof.
  induction 2.
  - contradiction.
  - rewrite HExecs in H; destruct H.
    + inv H; exists rb; auto.
    + apply IHPPlusSubsteps; auto.
  - rewrite HExecs in H.
    destruct H;[discriminate|].
    apply IHPPlusSubsteps; auto.
Qed.

Lemma PPlusSubsteps_exec_Meth_defined m o upds execs calls fn fb :
  In (Meth (fn, fb)) execs ->
  PPlusSubsteps m o upds execs calls ->
  exists fb',
    In (fn, fb') (getMethods m).
Proof.
  induction 2.
  - contradiction.
  - rewrite HExecs in H; destruct H;[discriminate|].
    apply IHPPlusSubsteps; auto.
  - rewrite HExecs in H; destruct H.
    + inv H; exists fb0; auto.
    + apply IHPPlusSubsteps; auto.
Qed.

Lemma PPlusSubsteps_upds_SubList m o upds execs calls :
  PPlusSubsteps m o upds execs calls ->
  SubList (getKindAttr upds) (getKindAttr (getRegisters m)).
Proof.
  induction 1.
  - repeat intro; contradiction.
  - rewrite HUpds, map_app, SubList_app_l_iff; split; auto.
  - rewrite HUpds, map_app, SubList_app_l_iff; split; auto.
Qed.

Lemma PPlusSubsteps_upds_NoDup_Keys m o upds execs calls :
  PPlusSubsteps m o upds execs calls ->
  NoDup (map fst upds).
Proof.
  induction 1.
  - constructor.
  - rewrite HUpds, map_app, NoDup_app_iff; repeat split; auto.
    + apply (PSemAction_NoDup_Key_Writes HPAction).
    + repeat intro.
      destruct (HDisjRegs a); contradiction.
    + repeat intro.
      destruct (HDisjRegs a); contradiction.
  - rewrite HUpds, map_app, NoDup_app_iff; repeat split; auto.
    + apply (PSemAction_NoDup_Key_Writes HPAction).
    + repeat intro.
      destruct (HDisjRegs a); contradiction.
    + repeat intro.
      destruct (HDisjRegs a); contradiction.
Qed.

Lemma PPlusSubsteps_split_execs_OneRle m o :
  NoDup (map fst (getMethods m)) ->
  NoDup (map fst (getRules m)) ->
  forall execs1 execs2 upds calls,
    PPlusSubsteps m o upds (execs1++execs2) calls ->
    (forall x y, In x execs1 ->
                 In y execs2 ->
                 match x with
                 | Rle _ => match y with
                            | Rle _ => False
                            | Meth _ => True
                            end
                 | Meth _ => True
                 end).
Proof.
  induction execs1;[contradiction|].
  intros; destruct H2.
  - subst; simpl in H1; destruct x, y; auto.
    specialize (PPlusSubsteps_exec_Rule_defined _ (in_eq _ _ ) H1) as TMP; dest.
    assert (In (Rle (fst (rn, x))) (Rle rn::execs1++execs2)) as P1;simpl; auto.
    specialize (ExtractRuleAction _ H0 H2 P1 H1) as TMP; dest; simpl in *.
    apply Permutation_cons_inv in H10; specialize (H11 rn0); apply H11;
      rewrite <-H10, in_app_iff; right; assumption.
  - destruct a; simpl in *.
    + specialize (PPlusSubsteps_exec_Rule_defined _ (in_eq _ _ ) H1) as TMP; dest.
      assert (In (Rle (fst (rn, x))) (Rle rn::execs1++execs2)) as P1;simpl; auto.
      specialize (ExtractRuleAction _ H0 H4 P1 H1) as TMP; dest; simpl in *.
      apply Permutation_cons_inv in H11; rewrite <-H11 in H13.
      eapply IHexecs1; eauto.
    + destruct f.
      specialize (PPlusSubsteps_exec_Meth_defined _ _ (in_eq _ _ ) H1) as TMP; dest.
      assert (fst (s, x0) = fst (s, s0)) as P1; auto.
      specialize (ExtractMethAction _ _ H H4 (in_eq _ _) P1 H1) as TMP; dest; simpl in *.
      apply Permutation_cons_inv in H11; rewrite <-H11 in H13.
      eapply IHexecs1; eauto.
Qed.

Lemma PPlusSubsteps_merge m o :
  forall execs1 execs2 upds1 upds2 calls1 calls2,
  NoDup (map fst (getMethods m)) ->
  NoDup (map fst (getRules m)) ->
  DisjKey upds1 upds2 ->
  (forall x y, In x execs1 -> In y execs2 -> match x with
                                             | Rle _ => match y with
                                                        | Rle _ => False
                                                        | Meth _ => True
                                                        end
                                             | Meth _ => True
                                             end) ->
  PPlusSubsteps m o upds1 execs1 calls1 ->
  PPlusSubsteps m o upds2 execs2 calls2 ->
  PPlusSubsteps m o (upds1++upds2) (execs1++execs2) (calls1++calls2).
Proof.
  induction execs1.
  - intros.
    inv H3; simpl; auto.
    + apply False_ind.
      apply Permutation_nil in HExecs; inv HExecs.
    + apply Permutation_nil in HExecs; inv HExecs.
  - intros; simpl.
    destruct a.
    specialize (PPlusSubsteps_exec_Rule_defined _ (in_eq _ _) H3) as TMP; dest.
    specialize (ExtractRuleAction _ H0 H5 (in_eq _ _ ) H3) as TMP; dest.
    + econstructor 2.
      * clear - H14; inv H14; auto.
      * apply H5.
      * rewrite shatter_word_0 in H6.
        apply H6.
      * assumption.
      * assumption.
      * rewrite H7, <-app_assoc.
        apply Permutation_app_head, Permutation_refl.
      * reflexivity.
      * rewrite H8, <-app_assoc.
        apply Permutation_app_head, Permutation_refl.
      * intro k; specialize (H9 k); specialize (H1 k).
        rewrite H7 in H1; repeat rewrite map_app, in_app_iff in *.
        clear - H9 H1; firstorder fail.
      * intros; rewrite in_app_iff in H15.
        destruct H15.
        -- apply Permutation_cons_inv in H12.
           rewrite H12 in H15; destruct x7; auto.
           eapply H13; eauto.
        -- apply (H2 _ _ (in_eq _ _) H15).
      * apply Permutation_cons_inv in H12; rewrite <-H12 in H14.
        apply IHexecs1; auto.
        -- intro k; specialize (H1 k); rewrite H7, map_app, in_app_iff in H1.
           clear - H1; firstorder fail.
        -- intros; apply H2; auto; right; assumption.
    + destruct f.
      specialize (PPlusSubsteps_exec_Meth_defined _ _ (in_eq _ _) H3) as TMP; dest.
      assert (fst (s, x) = fst (s, s0)); auto.
      specialize (ExtractMethAction _ _ H H5 (in_eq _ _) H6 H3) as TMP; dest.
      econstructor 3.
      * clear - H15; inv H15; auto.
      * apply H5.
      * apply H7.
      * assumption.
      * assumption.
      * rewrite H8, <-app_assoc.
        apply Permutation_app_head, Permutation_refl.
      * simpl in *; rewrite H14; reflexivity.
      * rewrite H9, <-app_assoc.
        apply Permutation_app_head, Permutation_refl.
      * intro k; specialize (H10 k); specialize (H1 k).
        rewrite H8 in H1; repeat rewrite map_app, in_app_iff in *.
        clear - H10 H1; firstorder fail.
      * apply Permutation_cons_inv in H13.
        rewrite <- H13 in H15.
        apply IHexecs1; auto.
        -- intro k; specialize (H1 k); rewrite H8, map_app, in_app_iff in H1.
           clear - H1; firstorder fail.
        -- intros; apply H2; auto; right; assumption.
Qed.

Lemma SameKeys_inline_Meth f gn l:
  (map fst (inlineSingle_Meth_in_list f gn l)) = (map fst l).
Proof.
  induction l.
  - reflexivity.
  - simpl; destruct string_dec; simpl;[|rewrite IHl; reflexivity].
    unfold inlineSingle_Meth; destruct a, string_dec; simpl; rewrite IHl; reflexivity.
Qed.

Lemma PPlusSubsteps_inline_Meth f m o gn gb upds execs calls :
  In (gn, gb) (getMethods m) ->
  In f (getMethods m) ->
  NoDup (map fst (getMethods m)) ->
  NoDup (map fst (getRules m)) ->
  MatchingExecCalls_flat calls execs m ->
  (gn <> fst f) ->
  PPlusSubsteps m o upds execs calls ->
  exists fcalls execs' calls',
    execs [=] (map Meth fcalls)++execs' /\
    calls [=] fcalls++calls' /\
    PPlusSubsteps (inlineSingle_Meth_BaseModule f gn m) o upds execs' calls'.
Proof.
  intros.
  specialize (extract_meths_PPlus gn H1 H5) as TMP; dest.
  rewrite H7, H8, H10 in H5.
  specialize (MatchingExecCalls_flat_surjective_split _ H0 H3) as TMP; dest.
  assert (forall a, ~In a (map Meth (filter (called_by f) calls)) \/ ~In a (map Meth x1));
    [intro; destruct (in_dec RuleOrMeth_dec a (map Meth x1)), (in_dec RuleOrMeth_dec a (map Meth (filter (called_by f) calls)));
     auto; rewrite in_map_iff in i, i0; dest;specialize (H11 _ H18); apply called_by_fst_eq in H16;
     rewrite <-H17 in H15; inv H15; contradiction
    |].
  rewrite H14 in H10.
  destruct (Disjoint_list_split _ _ _ _ H10 H15).
  rewrite H8, filter_app, map_app, <-app_assoc in H16.
  exists (filter (called_by f) x3), ((map Meth (filter (called_by f) x4))++x5), ((filter (complement (called_by f)) x3)++x4).
  repeat split.
  - rewrite H14, H8, filter_app, map_app, app_assoc; reflexivity.
  - rewrite app_assoc, <-(separate_calls_by_filter x3 (called_by f)); assumption.
  - rewrite H16 in H13.
    assert (forall g, In g (filter (called_by f) x3) -> fst g = fst f);
      [intros; eapply called_by_fst_eq; eauto|].
    specialize (extract_execs_PPlus _ _ _ H1 H0 H17 H13) as TMP; dest.
    rewrite (separate_calls_by_filter x3 (called_by f)) in H6.
    assert (DisjKey x x8);
      [intro k; specialize (H9 k); rewrite H20, map_app, in_app_iff in H9; clear - H9; firstorder fail|].
    assert (~In (fst f) (map fst (filter (complement (called_by f)) x3)));
      [clear; induction x3; auto; unfold called_by in *; simpl; destruct string_dec; simpl; auto;
      intro; destruct H;[auto|contradiction]|].
    specialize (inline_meths_PPlus _ _ H6 H17 H18 H25 H23 H22 H4 H1 H26 H11) as P1.
    rewrite (separate_calls_by_filter x3 (called_by f)) in H6.
    assert (forall gb : {x : Kind * Kind & SignT x}, ~ In (Meth (gn, gb)) (map Meth (filter (called_by f) x4)++x6));
      [repeat intro; apply (H12 gb0); rewrite H16; clear - H27; repeat rewrite in_app_iff in *; firstorder fail|].
    specialize (PPlusSubsteps_inline_Meth_NoExec_PPlusSubsteps _ _ H1 H0 H27 H24) as P2.
    assert (upds [=] ((x8++x) ++ x9)) as TMP;
      [rewrite H7, H20, app_assoc; apply Permutation_app_tail, Permutation_app_comm
      |rewrite TMP; clear TMP].
    assert ((map Meth (filter (called_by f) x4)) ++ x5 [=] (map Meth x1)++(map Meth (filter (called_by f) x4) ++ x6)) as TMP;
      [rewrite app_assoc, <-map_app, <-filter_app, <-H8 in H16; rewrite H16, app_assoc, Permutation_app_comm in H10;
       apply Permutation_sym in H10; rewrite Permutation_app_comm, app_assoc in H10; apply Permutation_app_inv_r in H10;
       symmetry; rewrite Permutation_app_comm, <-app_assoc; apply Permutation_app_head; assumption
      |rewrite TMP; clear TMP].
    assert ((filter (complement (called_by f)) x3)++x4 [=] ((x10++(filter (complement (called_by f)) x3))++x11)) as TMP;
      [symmetry; rewrite <-app_assoc, Permutation_app_comm, <-app_assoc; apply Permutation_app_head; rewrite H19; apply Permutation_app_comm| rewrite TMP; clear TMP].
    apply PPlusSubsteps_merge; simpl; auto.
    + rewrite SameKeys_inline_Meth; assumption.
    + intro k; specialize (H9 k); specialize (H21 k); rewrite H20 in H9; clear - H9 H21.
      rewrite map_app, in_app_iff in *; firstorder fail.
    + specialize (PPlusSubsteps_split_execs_OneRle H1 H2 _ _ H5) as P3; clear - P3 H16.
      intros; specialize (P3 x y H).
      rewrite H16, in_app_iff in P3.
      apply (P3 (or_intror _ H0)).
Qed.

Lemma PPlusStep_inline_Meth_In f m o gn gb upds execs calls :
  In (gn, gb) (getMethods m) ->
  In f (getMethods m) ->
  NoDup (map fst (getRules m)) ->
  NoDup (map fst (getMethods m)) ->
  (gn <> fst f) ->
  PPlusStep m o upds execs calls ->
  exists fcalls execs' calls',
    execs [=] (map Meth fcalls)++execs' /\
    calls [=] fcalls++calls' /\
    PPlusStep (inlineSingle_Meth_BaseModule f gn m) o upds execs' calls'.
Proof.
  induction 6.
  specialize (PPlusSubsteps_inline_Meth _ _ H H0 H2 H1 H5 H3 H4) as TMP; dest.
  exists x, x0, x1.
  repeat split; auto.
  unfold MatchingExecCalls_flat in *.
  simpl; rewrite SameKeys_inline_Meth; intros; specialize (H5 _ H9).
  rewrite H6, H7, getNumFromCalls_app, getNumFromExecs_app, call_execs_counts_eq in H5.
  Omega.omega.
Qed.

Lemma PPlusSubsteps_inline_Meth_NotInDef f m o gn upds execs calls :
  ~In gn (map fst (getMethods m)) ->
  PPlusSubsteps m o upds execs calls ->
  PPlusSubsteps (inlineSingle_Meth_BaseModule f gn m) o upds execs calls.
Proof.
  induction 2.
  - econstructor 1; auto.
  - econstructor 2; simpl; eauto.
  - econstructor 3; simpl; eauto.
    clear - H HInMeths.
    induction (getMethods m);[contradiction|].
    destruct HInMeths; subst.
    + simpl; destruct string_dec;
        [destruct string_dec;subst;simpl;[left; reflexivity|]|left; reflexivity].
      apply False_ind, H; simpl; left; reflexivity.
    + simpl; destruct string_dec; right; apply IHl; auto; intro; apply H; simpl; right; assumption.
Qed.

Corollary PPlusStep_inline_Meth_NotInDef f m o gn upds execs calls :
  ~In gn (map fst (getMethods m)) ->
  PPlusStep m o upds execs calls ->
  PPlusStep (inlineSingle_Meth_BaseModule f gn m) o upds execs calls.
Proof.
  induction 2.
  constructor;[apply PPlusSubsteps_inline_Meth_NotInDef; auto|].
  intros g HInDef; simpl in *.
  rewrite SameKeys_inline_Meth in HInDef.
  specialize (H1 _ HInDef); assumption.
Qed.

Lemma PPlusSubsteps_inline_Meth_identical f m o gn upds execs calls :
  gn = fst f ->
  PPlusSubsteps m o upds execs calls ->
  PPlusSubsteps (inlineSingle_Meth_BaseModule f gn m) o upds execs calls.
Proof.
  induction 2.
  - econstructor 1; eauto.
  - econstructor 2; simpl; eauto.
  - econstructor 3; simpl; eauto.
    clear - H HInMeths.
    induction (getMethods m);[contradiction|].
    destruct HInMeths; subst.
    + simpl; destruct string_dec; left; reflexivity.
    + simpl; destruct string_dec; right; apply IHl; auto.
Qed.

Corollary PPlusStep_inline_Meth_identical f m o gn upds execs calls :
  gn = fst f ->
  PPlusStep m o upds execs calls ->
  PPlusStep (inlineSingle_Meth_BaseModule f gn m) o upds execs calls.
Proof.
  induction 2.
  constructor;[apply PPlusSubsteps_inline_Meth_identical; auto|].
  intros g HInDef; simpl in *.
  rewrite SameKeys_inline_Meth in HInDef.
  specialize (H1 _ HInDef); assumption.
Qed.

Lemma WfActionT_inline_Meth (k : Kind) m (a : ActionT type k) rn f:
  WfActionT m a ->
  WfActionT (inlineSingle_Meth_BaseModule f rn m) a.
Proof.
  intros; induction H; econstructor; auto.
Qed.

Lemma WfActionT_inline_Meth_inline_action (k : Kind) m (a : ActionT type k) gn (f : DefMethT):
  WfActionT m a ->
  (forall v, WfActionT m (projT2 (snd f) type v)) ->
  WfActionT (inlineSingle_Meth_BaseModule f gn m) (inlineSingle f a).
Proof.
  induction 1; try econstructor; eauto.
  simpl.
  destruct string_dec;[destruct Signature_dec|]; subst; econstructor; eauto.
  econstructor.
  intros.
  specialize (H1 v).
  apply (WfActionT_inline_Meth); auto.
Qed.
     
Lemma inlineSingle_Meth_BaseModule_dec meth f gn l:
  In meth (inlineSingle_Meth_in_list f gn l) ->
  In meth l \/
  exists meth',
    In meth' l /\
    (inlineSingle_Meth f meth' = meth). 
Proof.
  induction l.
  - intros; simpl in *; contradiction.
  - simpl; destruct string_dec; subst; intros.
    + destruct H; subst.
      * right; exists a; split; auto.
      * specialize (IHl H).
        destruct IHl;auto; dest; subst.
        right; exists x; split; auto.
    + destruct H; subst; auto.
      destruct (IHl H); auto; dest; subst.
      right; exists x; split; auto.
Qed.

Lemma WfMod_Meth_inlined m f gn :
  (WfMod (Base m)) ->
  In f (getMethods m) ->
  (WfMod (Base (inlineSingle_Meth_BaseModule f gn m))).
Proof.
  intros.
  pose proof H as sth.
  specialize (H).
  inv H; econstructor; eauto.
  - split; intros; simpl in *; inv HWfBaseModule.
    + apply WfActionT_inline_Meth; auto.
    + repeat split; dest; intros; try rewrite SameKeys_inline_Meth; auto.
      * destruct (inlineSingle_Meth_BaseModule_dec _ _ _ _ H5).
        -- specialize (H1 _ H6 v); apply WfActionT_inline_Meth; auto.
        -- dest.
           destruct x, s0, meth, s1; simpl in *.
           inv H7; destruct string_dec.
           ++ inv H10; EqDep_subst; simpl in *.
              specialize (H1 _ H6 v); simpl in *; apply WfActionT_inline_Meth; assumption.
           ++ inv H10; EqDep_subst.
              apply WfActionT_inline_Meth_inline_action; auto.
              specialize (H1 _ H6 v); simpl in *; assumption.
Qed.

Lemma PPlusStrongTraceInclusion_inlining_Meth_r m f gn :
  In f (getMethods m) ->
  (WfMod (Base m)) ->
  StrongPPlusTraceInclusion m (inlineSingle_Meth_BaseModule f gn m).
Proof.
  unfold StrongPPlusTraceInclusion; induction 3; subst.
  - exists nil; split.
    + econstructor; eauto.
    + constructor.
  - dest;destruct (string_dec gn (fst f)).
    + exists ((upds, (execs, calls))::x); split.
      * econstructor 2; eauto.
        apply PPlusStep_inline_Meth_identical; auto.
      * constructor; auto; unfold WeakInclusion_flat; split; intro; auto.
    + destruct (in_dec string_dec gn (map fst (getMethods m))).
      * rewrite in_map_iff in i; dest.
        specialize (H0).
        inv H0; destruct x0; simpl in *.
        destruct HWfBaseModule as [? [? [NoDupMeths [NoDupRegisters NoDupRle]]]].
        specialize (PPlusStep_inline_Meth_In _ _ H5 H NoDupRle NoDupMeths n HPPlusStep) as TMP; dest.
        exists ((upds, (x1, x2))::x); split.
        -- econstructor 2; eauto.
        -- constructor; auto.
           unfold WeakInclusion_flat, getListFullLabel_diff_flat; simpl; split; intros; auto.
           ++ rewrite H6, H7, getNumFromExecs_app, getNumFromCalls_app, call_execs_counts_eq; Omega.omega.
           ++ dest; exists x3.
              rewrite ?H6, ?H7, in_app_iff; right; assumption.
      * exists ((upds, (execs, calls))::x); split.
        -- econstructor 2; eauto.
           apply PPlusStep_inline_Meth_NotInDef; auto.
        -- constructor; auto.
           unfold WeakInclusion_flat; split; intros; auto.
Qed.

Theorem TraceInclusion_inlining_Meth_r m f gn :
  In f (getMethods m) ->
  (WfMod (Base m)) ->
  TraceInclusion (Base m) (Base (inlineSingle_Meth_BaseModule f gn m)).
Proof.
  intros.
  apply PPlusTraceInclusion_TraceInclusion; auto.
  apply (WfMod_Meth_inlined); auto.
  eauto using StrongPPlusTraceInclusion_PPlusTraceInclusion, PPlusStrongTraceInclusion_inlining_Meth_r.
Qed.

Lemma WfBaseMod_Meth_inlined m f gn :
  (WfBaseModule m) ->
  In f (getMethods m) ->
  (WfBaseModule (inlineSingle_Meth_BaseModule f gn m)).
Proof.
  intros.
  specialize (WfMod_Meth_inlined (m:=m) f gn); intro.
  assert (WfMod m) as TMP;[constructor; auto|specialize (H1 TMP H0); clear TMP].
  inv H1; auto.
Qed.

Definition inlineSingle_Meth_BaseModuleWf {f} {m: BaseModuleWf} gn (inMeths: In f (getMethods m)):=
  Build_BaseModuleWf (WfBaseMod_Meth_inlined f gn (wfBaseModule m) inMeths).

Theorem TraceInclusion_inlining_Meth_Wf_r {f} {m : BaseModuleWf} rn
        (inMeths: In f (getMethods m)):
  TraceInclusion m (inlineSingle_Meth_BaseModuleWf rn inMeths).
Proof.
  simpl; apply TraceInclusion_inlining_Meth_r; eauto.
  constructor; apply wfBaseModule.
Qed.

Section Rel.
  Variable A B: Type.
  Variable f: B -> A  -> A.

  Variable R: A -> A -> Prop.

  Lemma fold_right_Rel ls:
    forall x b,
      (forall x b, R x (f b x)) ->
      R (fold_right f x ls) (f b (fold_right f x ls)).
  Proof.
    induction ls; simpl; auto; intros.
  Qed.
End Rel.


Lemma Method_list_invariance f gn ls:
  ~In gn (map fst ls) ->
  ls = inlineSingle_Meth_in_list f gn ls.
Proof.
  induction ls; auto.
  simpl; intros.
  destruct string_dec.
  - apply False_ind, H; rewrite e; auto.
  - rewrite IHls at 1;[reflexivity|].
    intro; apply H; auto.
Qed.

Lemma Rule_list_invariance f rn ls:
  ~In rn (map fst ls) ->
  ls = inlineSingle_Rule_in_list f rn ls.
Proof.
  induction ls; auto.
  simpl; intros.
  destruct string_dec.
  - apply False_ind, H; rewrite e; auto.
  - rewrite IHls at 1;[reflexivity|].
    intro; apply H; auto.
Qed.

Section transform_nth_right.
  Lemma inlineSingle_Meth_transform_nth f ls:
    NoDup (map fst ls) ->
    forall i,
      i < length ls ->
      exists val,
        In val ls /\
        transform_nth_right (inlineSingle_Meth f) i ls =
        inlineSingle_Meth_in_list f (fst val) ls.
  Proof.
    induction ls; destruct i; simpl in *; auto; intros; try Omega.omega.
    - exists a; repeat split; auto.
      destruct (string_dec (fst a) (fst a)); [| tauto].
      f_equal.
      inv H.
      apply Method_list_invariance; auto.
    - inv H.
      specialize (IHls H4 i ltac:(Omega.omega)); dest.
      exists x.
      repeat split; auto.
      destruct (string_dec (fst x) (fst a)).
      apply in_map with (f := fst) in H.
      + rewrite e in *; tauto.
      + rewrite H1; auto.
  Qed.

  Lemma inlineSingle_Rule_transform_nth f ls:
    NoDup (map fst ls) ->
    forall i,
      i < length ls ->
      exists val,
        In val ls /\
        transform_nth_right (inlineSingle_Rule f) i ls =
        inlineSingle_Rule_in_list f (fst val) ls.
  Proof.
    induction ls; destruct i; simpl in *; auto; intros; try Omega.omega.
    - exists a; repeat split; auto.
      destruct (string_dec (fst a) (fst a)); [| tauto].
      f_equal.
      inv H.
      apply Rule_list_invariance; auto.
    - inv H.
      specialize (IHls H4 i ltac:(Omega.omega)); dest.
      exists x.
      repeat split; auto.
      destruct (string_dec (fst x) (fst a)).
      apply in_map with (f := fst) in H.
      + rewrite e in *; tauto.
      + rewrite H1; auto.
  Qed.
  
  Lemma inlineSingle_Meth_transform_nth_keys f ls :
    forall i,
      map fst (transform_nth_right (inlineSingle_Meth f) i ls) =
      map fst ls.
  Proof.
    induction ls; destruct i; simpl in *; auto; intros; try Omega.omega.
    - destruct a; simpl; reflexivity.
    - rewrite (IHls i); auto.
  Qed.
  
  Lemma inlineSingle_Rule_transform_nth_keys f ls :
    forall i,
      map fst (transform_nth_right (inlineSingle_Rule f) i ls) =
      map fst ls.
  Proof.
    induction ls; destruct i; simpl in *; auto; intros; try Omega.omega.
    - destruct a; simpl; reflexivity.
    - rewrite (IHls i); auto.
  Qed.
  
  Lemma inlineSingle_transform_gt (A : Type) (f : A -> A) ls :
    forall i,
      length ls <= i ->
      transform_nth_right f i ls = ls.
  Proof.
    induction ls; destruct i; simpl in *; auto; intros; try Omega.omega.
    rewrite (IHls i ltac:(Omega.omega)); reflexivity.
  Qed.
End transform_nth_right.

Lemma fold_right_nil xs (A: Type) (f : A -> A) :
  (fold_right (transform_nth_right f) nil xs) = nil.
Proof.
  induction xs; simpl; auto.
  rewrite IHxs; simpl; destruct a; simpl; reflexivity.
Qed.

Lemma transform_len (A : Type) (f : A -> A) ls :
  forall i, 
    length (transform_nth_right f i ls) = length ls.
Proof.
  induction ls; destruct i; simpl; auto.
Qed.

Lemma fold_right_len xs (A : Type) (f : A -> A) ls :
  length (fold_right (transform_nth_right f) ls xs) = length ls.
Proof.
  induction xs; simpl; auto.
  rewrite transform_len; auto.
Qed.

Lemma SameKeys_Meth_fold_right ls xs f :
  (map fst ls = map fst (fold_right (transform_nth_right (inlineSingle_Meth f)) ls xs)).
Proof.
  induction xs; simpl; auto.
  rewrite inlineSingle_Meth_transform_nth_keys; auto.
Qed.

Lemma SameKeys_Rule_fold_right ls xs f :
  (map fst ls = map fst (fold_right (transform_nth_right (inlineSingle_Rule f)) ls xs)).
Proof.
  induction xs; simpl; auto.
  rewrite inlineSingle_Rule_transform_nth_keys; auto.
Qed.

Lemma inline_Meth_not_transformed f ls :
  In f ls ->
  forall i,
    In f (transform_nth_right (inlineSingle_Meth f) i ls).
Proof.
  induction ls; destruct i; simpl; auto.
  - destruct H; subst; auto.
    unfold inlineSingle_Meth; destruct f, string_dec; auto.
    apply False_ind, n; reflexivity.
  - destruct H; auto.
Qed.

Lemma inlined_Meth_not_transformed_fold_right ls xs f :
  In f ls ->
  In f (fold_right (transform_nth_right (inlineSingle_Meth f)) ls xs).
Proof.
  induction xs; simpl; auto.
  intros; specialize (IHxs H).
  apply inline_Meth_not_transformed; assumption.
Qed.

Lemma WfMod_inline_all_Meth regs rules meths f xs:
  In f meths ->
  (WfMod (Base (BaseMod regs rules meths))) ->
  (WfMod (Base (BaseMod regs rules (fold_right (transform_nth_right (inlineSingle_Meth f)) meths xs)))).
Proof.
  induction xs; auto.
  simpl.
  intros; specialize (IHxs H).
  destruct (lt_dec a (length meths)).
  - pose proof H0 as H0'.
    specialize (H0).
    inv H0; simpl in *.
    destruct HWfBaseModule as [? [? [NoDupMeths [NoDupRegisters NoDupRle]]]].
    simpl in *.
    rewrite (SameKeys_Meth_fold_right meths xs f) in NoDupMeths.
    rewrite <- (fold_right_len xs (inlineSingle_Meth f) meths) in l.
    specialize (inlineSingle_Meth_transform_nth f _ NoDupMeths l) as TMP; dest.
    rewrite H3.
    assert (In f (fold_right (transform_nth_right (inlineSingle_Meth f)) meths xs));
      [apply inlined_Meth_not_transformed_fold_right; auto|].
    specialize (WfMod_Meth_inlined _ (fst x) (IHxs H0') H4) as P1.
    unfold inlineSingle_Meth_BaseModule in P1; simpl in *.
    eauto.
  - apply Nat.nlt_ge in n.
    rewrite <- (fold_right_len xs (inlineSingle_Meth f) meths) in n.
    rewrite inlineSingle_transform_gt; auto.
Qed.

Lemma WfMod_inline_all_Rule regs rules meths f xs:
  In f meths ->
  (WfMod (Base (BaseMod regs rules meths))) ->
  (WfMod (Base (BaseMod regs (fold_right (transform_nth_right (inlineSingle_Rule f)) rules xs) meths))).
Proof.
  induction xs; auto.
  simpl.
  intros; specialize (IHxs H).
  destruct (lt_dec a (length rules)).
  - pose proof H0 as H0'.
    specialize (H0).
    inv H0; simpl in *.
    destruct HWfBaseModule as [? [? [NoDupMeths [NoDupRegisters NoDupRle]]]].
    simpl in *.
    rewrite (SameKeys_Rule_fold_right rules xs f) in NoDupRle.
    rewrite <- (fold_right_len xs (inlineSingle_Rule f) rules) in l.
    specialize (inlineSingle_Rule_transform_nth f _ NoDupRle l) as TMP; dest.
    rewrite H3.
    specialize (WfMod_Rule_inlined _ (fst x) (IHxs H0') H) as P1.
    unfold inlineSingle_Rule_BaseModule in P1; simpl in *; assumption.
  - apply Nat.nlt_ge in n.
    rewrite <- (fold_right_len xs (inlineSingle_Rule f) rules) in n.
    rewrite inlineSingle_transform_gt; auto.
Qed.

Theorem inline_meth_transform f regs rules meths:
  (WfMod (Base (BaseMod regs rules meths))) ->
  In f meths ->
  forall i,
    TraceInclusion (Base (BaseMod regs rules meths)) (Base (BaseMod regs rules (transform_nth_right (inlineSingle_Meth f) i meths))).
Proof.
  intros; destruct (lt_dec i (length meths)).
  - pose proof H as H'.
    inv H; simpl in *.
    destruct HWfBaseModule as [? [? [NoDupMeths [NoDupRegisters NoDupRle]]]].
    simpl in *.
    specialize (inlineSingle_Meth_transform_nth f _ NoDupMeths l) as TMP; dest.
    rewrite H3.
    assert (In f (getMethods (BaseMod regs rules meths))); auto.
    specialize (TraceInclusion_inlining_Meth_r _ (fst x) H4 H') as P1.
    unfold inlineSingle_Meth_BaseModule in P1; simpl in *; assumption.
  - apply Nat.nlt_ge in n.
    rewrite inlineSingle_transform_gt; auto.
    apply TraceInclusion_refl.
Qed.

Lemma WfBaseMod_inline_nth_Meth m f i:
  In f (getMethods m) ->
  (WfBaseModule m) ->
  (WfBaseModule (BaseMod (getRegisters m) (getRules m) (transform_nth_right (inlineSingle_Meth f) i (getMethods m)))).
Proof.
  intros.
  destruct (lt_dec i (length (getMethods m))).
  - pose proof H0 as H0'.
    destruct H0 as [? [? [NoDupMeths [NoDupRegisters NoDupRle]]]].
    simpl in *.
    specialize (inlineSingle_Meth_transform_nth f _ NoDupMeths l) as TMP; dest.
    rewrite H3.
    assert (In f (transform_nth_right (inlineSingle_Meth f) i (getMethods m)));
      [apply inline_Meth_not_transformed; auto|].
    assert (WfMod m) as P1; [constructor; auto|].
    specialize (WfMod_Meth_inlined _ (fst x) P1 H) as P2.
    unfold inlineSingle_Meth_BaseModule in P2; simpl in *.
    inv P2; eauto.
  - apply Nat.nlt_ge in n.
    rewrite inlineSingle_transform_gt; auto.
    assert (WfMod m) as P1;[constructor; auto| apply (WfMod_WfBaseMod_flat P1)].
Qed.

Definition inline_nth_Meth_BaseModuleWf {f} {m : BaseModuleWf} i
           (inMeths : In f (getMethods m)):=
  (Build_BaseModuleWf (WfBaseMod_inline_nth_Meth f i inMeths (wfBaseModule m))).

Theorem inline_meth_transform_Wf {f} {m : BaseModuleWf} i (inMeths : In f (getMethods m)):
    TraceInclusion m (inline_nth_Meth_BaseModuleWf i inMeths).
Proof.
  intros; simpl.
  specialize (TraceInclusion_flatten_r m) as P1.
  specialize (wfMod (flatten_ModWf m)) as P2; simpl in *.
  unfold flatten, getFlat in *; simpl in *.
  specialize (inline_meth_transform f P2 inMeths i) as P3.
  eauto using TraceInclusion_trans.
Qed.

Lemma WfBaseMod_inline_all_Meth m f xs:
  In f (getMethods m) ->
  (WfBaseModule m) ->
  (WfBaseModule (BaseMod (getRegisters m) (getRules m) (fold_right (transform_nth_right (inlineSingle_Meth f)) (getMethods m) xs))).
Proof.
  intros.
  assert (WfMod (Base m)) as P1;[constructor; auto|].
  specialize (WfMod_WfBaseMod_flat P1) as P2.
  unfold getFlat in P2; simpl in *.
  assert (WfMod (Base (BaseMod (getRegisters m) (getRules m) (getMethods m)))) as P3;
    [constructor; auto|].
  specialize (WfMod_inline_all_Meth f xs H P3) as P4.
  inv P4; auto.
Qed.

Definition inline_all_Meth_BaseModuleWf {f} {m : BaseModuleWf} xs
           (inMeths : In f (getMethods m)):=
  (Build_BaseModuleWf (WfBaseMod_inline_all_Meth f xs inMeths (wfBaseModule m))).

Lemma WfBaseMod_inline_all_Rule m f xs:
  In f (getMethods m) ->
  (WfBaseModule m) ->
  (WfBaseModule (BaseMod (getRegisters m) (fold_right (transform_nth_right (inlineSingle_Rule f)) (getRules m) xs) (getMethods m))).
Proof.
  intros.
  assert (WfMod (Base m)) as P1;[constructor; auto|].
  specialize (WfMod_WfBaseMod_flat P1) as P2.
  unfold getFlat in P2; simpl in *.
  assert (WfMod (Base (BaseMod (getRegisters m) (getRules m) (getMethods m)))) as P3;
    [constructor; auto|].
  specialize (WfMod_inline_all_Rule f xs H P3) as P4.
  inv P4; auto.
Qed.

Definition inline_all_Rule_BaseModuleWf {f} {m : BaseModuleWf} xs
           (inMeths : In f (getMethods m)):=
  (Build_BaseModuleWf (WfBaseMod_inline_all_Rule f xs inMeths (wfBaseModule m))).

Theorem inline_rule_transform f regs rules meths:
  (WfMod (Base (BaseMod regs rules meths))) ->
  In f meths ->
  forall i,
    TraceInclusion (Base (BaseMod regs rules meths)) (Base (BaseMod regs (transform_nth_right (inlineSingle_Rule f) i rules) meths)).
Proof.
  intros; destruct (lt_dec i (length rules)).
  - pose proof H as H'.
    inv H; simpl in *.
    destruct HWfBaseModule as [? [? [NoDupMeths [NoDupRegisters NoDupRle]]]].
    simpl in *.
    specialize (inlineSingle_Rule_transform_nth f _ NoDupRle l) as TMP; dest.
    rewrite H3.
    assert (In f (getMethods (BaseMod regs rules meths))); auto.
    specialize (TraceInclusion_inlining_Rules_r _ (fst x) H4 H') as P1.
    unfold inlineSingle_Rule_BaseModule in P1; simpl in *; assumption.
  - apply Nat.nlt_ge in n.
    rewrite inlineSingle_transform_gt; auto.
    apply TraceInclusion_refl.
Qed.

Lemma WfBaseMod_inline_nth_Rule m f i:
  In f (getMethods m) ->
  (WfBaseModule m) ->
  (WfBaseModule (BaseMod (getRegisters m) (transform_nth_right (inlineSingle_Rule f) i (getRules m)) (getMethods m))).
Proof.
  intros.
  destruct (lt_dec i (length (getRules m))).
  - pose proof H0 as H0'.
    destruct H0 as [? [? [NoDupMeths [NoDupRegisters NoDupRle]]]].
    specialize (inlineSingle_Rule_transform_nth f _ NoDupRle l) as TMP; dest.
    rewrite H3.
    assert (WfMod m) as P1; [constructor; auto|].
    specialize (WfMod_Rule_inlined _ (fst x) P1 H) as P2.
    unfold inlineSingle_Rule_BaseModule in P2; simpl in *.
    inv P2; eauto.
  - apply Nat.nlt_ge in n.
    rewrite inlineSingle_transform_gt; auto.
    assert (WfMod m) as P1;[constructor; auto| apply (WfMod_WfBaseMod_flat P1)].
Qed.

Definition inline_nth_Rule_BaseModuleWf {f} {m : BaseModuleWf} i
           (inMeths : In f (getMethods m)):=
  (Build_BaseModuleWf (WfBaseMod_inline_nth_Rule f i inMeths (wfBaseModule m))).

Theorem inline_rule_transform_Wf {f} {m : BaseModuleWf} i (inMeths : In f (getMethods m)):
    TraceInclusion m (inline_nth_Rule_BaseModuleWf i inMeths).
Proof.
  intros; simpl.
  specialize (TraceInclusion_flatten_r m) as P1.
  specialize (wfMod (flatten_ModWf m)) as P2; simpl in *.
  unfold flatten, getFlat in *; simpl in *.
  specialize (inline_rule_transform f P2 inMeths i) as P3.
  eauto using TraceInclusion_trans.
Qed.

Section inlineSingle_nth.
  Variable (f : DefMethT).
  Variable (regs: list RegInitT) (rules: list RuleT) (meths: list DefMethT).
  Variable (Wf : WfMod (Base (BaseMod regs rules meths))).

  Theorem inline_meth_fold_right xs:
    In f meths ->
    TraceInclusion (Base (BaseMod regs rules meths)) (Base (BaseMod regs rules (fold_right (transform_nth_right (inlineSingle_Meth f)) meths xs))).
  Proof.
    induction xs; intros.
    - simpl; apply TraceInclusion_refl.
    - simpl.
      specialize (IHxs H).
      specialize (WfMod_inline_all_Meth _ xs H Wf) as P1.
      specialize (inlined_Meth_not_transformed_fold_right _ xs _ H) as P2.
      specialize (inline_meth_transform _ P1 P2 a) as P3.
      apply (TraceInclusion_trans IHxs P3).
  Qed.
  
  Theorem inline_rule_fold_right xs:
    In f meths ->
    TraceInclusion (Base (BaseMod regs rules meths)) (Base (BaseMod regs (fold_right (transform_nth_right (inlineSingle_Rule f)) rules xs) meths)).
  Proof.
    induction xs; intros.
    - simpl; apply TraceInclusion_refl.
    - simpl.
      specialize (IHxs H).
      specialize (WfMod_inline_all_Rule _ xs H Wf) as P1.
      specialize (inline_rule_transform _ P1 H a) as P2.
      apply (TraceInclusion_trans IHxs P2).
  Qed.
End inlineSingle_nth.

Theorem inline_meth_fold_right_Wf {f} {m : BaseModuleWf} xs (inMeth : In f (getMethods m)):
  TraceInclusion m (inline_all_Meth_BaseModuleWf xs inMeth).
Proof.
  specialize (TraceInclusion_flatten_r m) as P1.
  simpl in *; unfold flatten, getFlat in P1; simpl in *.
  assert (WfMod m) as TMP. {
    constructor; apply wfBaseModule.
  }
  specialize (WfMod_getFlat TMP) as P2; clear TMP.
  specialize (inline_meth_fold_right f P2 xs inMeth) as P3.
  eauto using TraceInclusion_trans.
Qed.

Theorem inline_rule_fold_right_Wf {f} {m : BaseModuleWf} xs (inMeth : In f (getMethods m)):
  TraceInclusion m (inline_all_Rule_BaseModuleWf xs inMeth).
Proof.
  specialize (TraceInclusion_flatten_r m) as P1.
  simpl in *; unfold flatten, getFlat in P1; simpl in *.
  assert (WfMod m) as TMP.
  { constructor; apply wfBaseModule.
  }
  specialize (WfMod_getFlat TMP) as P2; clear TMP.
  specialize (inline_rule_fold_right f P2 xs inMeth) as P3.
  eauto using TraceInclusion_trans.
Qed.

Theorem TraceInclusion_inline_BaseModule_rules regs rules meths f:
  (WfMod (Base (BaseMod regs rules meths))) ->
  In f meths ->
  TraceInclusion (Base (BaseMod regs rules meths)) (Base (BaseMod regs (map (inlineSingle_Rule f) rules) meths)).
Proof.
  intros.
  specialize (inline_rule_fold_right f H (seq 0 (length rules)) H0) as P1.
  specialize (WfMod_inline_all_Rule _ (seq 0 (length rules)) H0 H) as P2.
  repeat rewrite map_fold_right_eq in *.
  assumption.
Qed.

Lemma WfBaseMod_inline_BaseModule_Rules m f:
  In f (getMethods m) ->
  WfBaseModule m ->
  WfBaseModule (BaseMod (getRegisters m) (map (inlineSingle_Rule f) (getRules m)) (getMethods m)).
Proof.
  intros.
  assert (WfMod m) as TMP;[constructor; auto|specialize (WfMod_getFlat TMP) as P1; clear TMP].
  specialize (WfMod_inline_all_Rule _ (seq 0 (length (getRules m))) H P1) as P2.
  repeat rewrite map_fold_right_eq in *; simpl in *.
  inv P2; auto.
Qed.

Definition inline_BaseModule_rules_BaseModuleWf {f} {m : BaseModuleWf}
           (inMeth : In f (getMethods m)) :=
  Build_BaseModuleWf (WfBaseMod_inline_BaseModule_Rules _ inMeth (wfBaseModule m)).

Theorem TraceInclusion_inline_BaseModule_rules_Wf {f} {m : BaseModuleWf}
        (inMeth : In f (getMethods m)):
  TraceInclusion m (inline_BaseModule_rules_BaseModuleWf inMeth).
Proof.
  specialize (TraceInclusion_flatten_r m) as P1.
  simpl in *; unfold flatten, getFlat in P1; simpl in *.
  assert (WfMod m) as TMP;[constructor; apply wfBaseModule
                          |specialize (WfMod_getFlat TMP) as P2; clear TMP].
  specialize (TraceInclusion_inline_BaseModule_rules f P2 inMeth) as P3.
  eauto using TraceInclusion_trans.
Qed.

Theorem TraceInclusion_inline_BaseModule_meths regs rules meths f:
  (WfMod (Base (BaseMod regs rules meths))) ->
  In f meths ->
  TraceInclusion (Base (BaseMod regs rules meths)) (Base (BaseMod regs rules (map (inlineSingle_Meth f) meths))).
Proof.
  intros.
  unfold inlineSingle_BaseModule.
  specialize (inline_meth_fold_right f H (seq 0 (length meths)) H0) as P1.
  repeat rewrite map_fold_right_eq in *.
  assumption.
Qed.

Lemma WfBaseMod_inline_BaseModule_Meths m f:
  In f (getMethods m) ->
  WfBaseModule m ->
  WfBaseModule (BaseMod (getRegisters m) (getRules m) (map (inlineSingle_Meth f) (getMethods m))).
Proof.
  intros.
  assert (WfMod m) as TMP;[constructor; auto|specialize (WfMod_getFlat TMP) as P1; clear TMP].
  specialize (WfMod_inline_all_Meth _ (seq 0 (length (getMethods m))) H P1) as P2.
  repeat rewrite map_fold_right_eq in *; simpl in *.
  inv P2; auto.
Qed.

Definition inline_BaseModule_meths_BaseModuleWf {f} {m : BaseModuleWf}
           (inMeth : In f (getMethods m)) :=
  Build_BaseModuleWf (WfBaseMod_inline_BaseModule_Meths _ inMeth (wfBaseModule m)).

Theorem TraceInclusion_inline_BaseModule_meths_Wf {f} {m : BaseModuleWf}
        (inMeth : In f (getMethods m)):
  TraceInclusion m (inline_BaseModule_meths_BaseModuleWf inMeth).
Proof.
  specialize (TraceInclusion_flatten_r m) as P1.
  simpl in *; unfold flatten, getFlat in P1; simpl in *.
  assert (WfMod m) as TMP;[constructor; apply wfBaseModule
                          |specialize (WfMod_getFlat TMP) as P2; clear TMP].
  specialize (TraceInclusion_inline_BaseModule_meths f P2 inMeth) as P3.
  eauto using TraceInclusion_trans.
Qed.

Theorem TraceInclusion_inline_BaseModule_all regs rules meths f:
  (WfMod (Base (BaseMod regs rules meths))) ->
  In f meths ->
  TraceInclusion (Base (BaseMod regs rules meths)) (Base (inlineSingle_BaseModule f regs rules meths)).
Proof.
  intros.
  unfold inlineSingle_BaseModule.
  specialize (TraceInclusion_inline_BaseModule_rules f H H0) as P1.
  specialize (WfMod_inline_all_Rule _ (seq 0 (length rules)) H0 H) as P2.
  specialize (TraceInclusion_inline_BaseModule_meths f P2 H0) as P3.
  repeat rewrite map_fold_right_eq in *.
  apply (TraceInclusion_trans P1 P3).
Qed.

Lemma WfBaseMod_inlineSingle_BaseModule m f:
  In f (getMethods m) ->
  WfBaseModule m ->
  WfBaseModule (inlineSingle_BaseModule f (getRegisters m) (getRules m) (getMethods m)).
Proof.
  intros.
  unfold inlineSingle_BaseModule.
  specialize (WfBaseMod_inline_BaseModule_Rules f H H0) as P1.
  assert (In f (getMethods ((BaseMod (getRegisters m) (map (inlineSingle_Rule f) (getRules m)) (getMethods m))))) as P2;[simpl; auto|].
  apply (WfBaseMod_inline_BaseModule_Meths f P2 P1).
Qed.

Definition inlineSingle_BaseModuleWf {f} {m : BaseModuleWf} (inMeth : In f (getMethods m)):=
  Build_BaseModuleWf (WfBaseMod_inlineSingle_BaseModule _ inMeth (wfBaseModule m)).

Theorem TraceInclusion_inline_BaseModule_all_Wf {f} {m : BaseModuleWf}
        (inMeth : In f (getMethods m)):
  TraceInclusion m (inlineSingle_BaseModuleWf inMeth).
Proof.
  specialize (TraceInclusion_flatten_r m) as P1.
  specialize (wfMod (flatten_ModWf m)) as P2.
  simpl in *; unfold flatten, getFlat in *; simpl in *.
  specialize (TraceInclusion_inline_BaseModule_all _ P2 inMeth) as P3.
  eauto using TraceInclusion_trans.
Qed.

Section inline_all_all.
  Theorem TraceInclusion_inlineSingle_pos_Rules regs rules meths:
    (WfMod (Base (BaseMod regs rules meths))) ->
    forall n,
      (WfMod (Base (BaseMod regs (inlineSingle_Rules_pos meths n rules) meths))) /\
      TraceInclusion (Base (BaseMod regs rules meths)) (Base (BaseMod regs (inlineSingle_Rules_pos meths n rules) meths)).
  Proof.
    intros WfH n.
    unfold inlineSingle_Rules_pos.
    case_eq (nth_error meths n); intros sth; [intros sthEq|split; [assumption | apply TraceInclusion_refl]].
    split.
    - apply nth_error_In in sthEq.
      pose proof (WfMod_inline_all_Rule sth (seq 0 (length rules)) sthEq WfH).
      repeat rewrite map_fold_right_eq in *.
      assumption.
    - apply TraceInclusion_inline_BaseModule_rules; auto.
      eapply nth_error_In; eauto.
  Qed.

  Lemma WfBaseMod_inlineSingle_Rules_pos m n:
    WfBaseModule m ->
    WfBaseModule (BaseMod (getRegisters m) (inlineSingle_Rules_pos (getMethods m) n (getRules m)) (getMethods m)).
  Proof.
    intros.
    assert (WfMod m) as P1;[constructor; auto|apply WfMod_getFlat in P1].
    unfold getFlat in P1; simpl in *.
    specialize (TraceInclusion_inlineSingle_pos_Rules P1 n) as TMP; dest.
    inversion H0; auto.
  Qed.

  Definition inlineSingle_Rules_pos_BaseModuleWf (m : BaseModuleWf) n :=
    Build_BaseModuleWf (WfBaseMod_inlineSingle_Rules_pos n (wfBaseModule m)).

  Theorem TraceInclusion_inlineSingle_pos_Rules_Wf (m : BaseModuleWf) n :
    TraceInclusion m (inlineSingle_Rules_pos_BaseModuleWf m n).
  Proof.
    specialize (TraceInclusion_flatten_r m) as P1.
    specialize (wfMod (flatten_ModWf m)) as P2.
    simpl in *; unfold flatten, getFlat in *; simpl in *.
    specialize (TraceInclusion_inlineSingle_pos_Rules P2 n) as TMP; dest.
    eauto using TraceInclusion_trans.
  Qed.
  
  Theorem TraceInclusion_inlineAll_pos_Rules regs rules meths:
    (WfMod (Base (BaseMod regs rules meths))) ->
    (WfMod (Base (BaseMod regs (inlineAll_Rules meths rules) meths))) /\
    TraceInclusion (Base (BaseMod regs rules meths)) (Base (BaseMod regs (inlineAll_Rules meths rules) meths)).
  Proof.
    intros WfH.
    unfold inlineAll_Rules.
    induction (Datatypes.length meths); [simpl in *; split; [assumption | apply TraceInclusion_refl]|].
    rewrite seq_eq.
    rewrite fold_left_app; simpl in *.
    destruct IHn as [IHn1 IHn2].
    pose proof (TraceInclusion_inlineSingle_pos_Rules IHn1 n) as [sth1 sth2].
    destruct n; simpl in *; auto.
    split; auto.
    eapply TraceInclusion_trans; eauto.
  Qed.
  
  Lemma WfBaseMod_inlineAll_Rules m :
    WfBaseModule m ->
    WfBaseModule (BaseMod (getRegisters m) (inlineAll_Rules (getMethods m) (getRules m)) (getMethods m)).
  Proof.
    intros.
    assert (WfMod m) as P1;[constructor; auto|apply WfMod_getFlat in P1].
    unfold getFlat in P1; simpl in *.
    specialize (TraceInclusion_inlineAll_pos_Rules P1) as TMP; dest.
    inversion H0; auto.
  Qed.

  Definition inlineAll_Rules_BaseModuleWf (m : BaseModuleWf) :=
    Build_BaseModuleWf (WfBaseMod_inlineAll_Rules (wfBaseModule m)).

  Theorem TraceInclusion_inlineAll_pos_Rules_Wf (m : BaseModuleWf) :
    TraceInclusion m (inlineAll_Rules_BaseModuleWf m).
  Proof.
    specialize (TraceInclusion_flatten_r m) as P1.
    specialize (wfMod (flatten_ModWf m)) as P2.
    simpl in *; unfold flatten, getFlat in *; simpl in *.
    specialize (TraceInclusion_inlineAll_pos_Rules P2) as TMP; dest.
    eauto using TraceInclusion_trans.
  Qed.
  
  Theorem TraceInclusion_inlineSingle_pos_Meths regs rules meths:
    (WfMod (Base (BaseMod regs rules meths))) ->
    forall n,
      (WfMod (Base (BaseMod regs rules (inlineSingle_Meths_pos meths n)))) /\
      TraceInclusion (Base (BaseMod regs rules meths)) (Base (BaseMod regs rules (inlineSingle_Meths_pos meths n))).
  Proof.
    intros WfH n.
    unfold inlineSingle_Meths_pos.
    case_eq (nth_error meths n); intros sth; [intros sthEq|split; [assumption | apply TraceInclusion_refl]].
    split.
    - apply nth_error_In in sthEq.
      pose proof (WfMod_inline_all_Meth sth (seq 0 (length meths)) sthEq WfH).
      repeat rewrite map_fold_right_eq in *.
      assumption.
    - apply TraceInclusion_inline_BaseModule_meths; auto.
      eapply nth_error_In; eauto.
  Qed.

  Lemma WfBaseMod_inlineSingle_Meths_pos m n:
    WfBaseModule m ->
    WfBaseModule (BaseMod (getRegisters m) (getRules m) (inlineSingle_Meths_pos (getMethods m) n)).
  Proof.
    intros.
    assert (WfMod m) as P1;[constructor; auto|apply WfMod_getFlat in P1].
    unfold getFlat in P1; simpl in *.
    specialize (TraceInclusion_inlineSingle_pos_Meths P1 n) as TMP; dest.
    inversion H0; auto.
  Qed.

  Definition inlineSingle_Meths_pos_BaseModuleWf (m : BaseModuleWf) n :=
    Build_BaseModuleWf (WfBaseMod_inlineSingle_Meths_pos n (wfBaseModule m)).

  Theorem TraceInclusion_inlineSingle_pos_Meths_Wf (m : BaseModuleWf) n :
    TraceInclusion m (inlineSingle_Meths_pos_BaseModuleWf m n).
  Proof.
    specialize (TraceInclusion_flatten_r m) as P1.
    specialize (wfMod (flatten_ModWf m)) as P2.
    simpl in *; unfold flatten, getFlat in *; simpl in *.
    specialize (TraceInclusion_inlineSingle_pos_Meths P2 n) as TMP; dest.
    eauto using TraceInclusion_trans.
  Qed.

  Theorem TraceInclusion_inlineAll_pos_Meths regs rules meths:
    (WfMod (Base (BaseMod regs rules meths))) ->
    (WfMod (Base (BaseMod regs rules (inlineAll_Meths meths)))) /\
    TraceInclusion (Base (BaseMod regs rules meths)) (Base (BaseMod regs rules (inlineAll_Meths meths))).
  Proof.
    intros WfH.
    unfold inlineAll_Meths.
    induction (Datatypes.length meths); [simpl; split; [assumption | apply TraceInclusion_refl]|].
    rewrite seq_eq.
    rewrite fold_left_app; simpl.
    destruct IHn as [IHn1 IHn2].
    pose proof (TraceInclusion_inlineSingle_pos_Meths IHn1 n) as [sth1 sth2].
    destruct n; simpl in *; auto.
    split; auto.
    eapply TraceInclusion_trans; eauto.
  Qed.

  Lemma WfBaseMod_inlineAll_Meths m :
    WfBaseModule m ->
    WfBaseModule (BaseMod (getRegisters m) (getRules m) (inlineAll_Meths (getMethods m))).
  Proof.
    intros.
    assert (WfMod m) as P1;[constructor; auto|apply WfMod_getFlat in P1].
    unfold getFlat in P1; simpl in *.
    specialize (TraceInclusion_inlineAll_pos_Meths P1) as TMP; dest.
    inversion H0; auto.
  Qed.

  Definition inlineAll_Meths_BaseModuleWf (m : BaseModuleWf) :=
    Build_BaseModuleWf (WfBaseMod_inlineAll_Meths (wfBaseModule m)).

  Theorem TraceInclusion_inlineAll_pos_Meths_Wf (m : BaseModuleWf) :
    TraceInclusion m (inlineAll_Meths_BaseModuleWf m).
  Proof.
    specialize (TraceInclusion_flatten_r m) as P1.
    specialize (wfMod (flatten_ModWf m)) as P2.
    simpl in *; unfold flatten, getFlat in *; simpl in *.
    specialize (TraceInclusion_inlineAll_pos_Meths P2) as TMP; dest.
    eauto using TraceInclusion_trans.
  Qed.
  
  Theorem TraceInclusion_inlineAll_pos regs rules meths:
    (WfMod (Base (BaseMod regs rules meths))) ->
    (WfMod (Base (inlineAll_All regs rules meths))) /\
    TraceInclusion (Base (BaseMod regs rules meths)) (Base (inlineAll_All regs rules meths)).
  Proof.
    unfold inlineAll_All in *.
    intros WfH1.
    pose proof (TraceInclusion_inlineAll_pos_Meths WfH1) as [WfH2 P2].
    pose proof (TraceInclusion_inlineAll_pos_Rules WfH2) as [WfH3 P3].
    split; auto.
    eapply TraceInclusion_trans; eauto.
  Qed.

  Lemma WfBaseMod_inlineAll_All m :
    WfBaseModule m ->
    WfBaseModule (inlineAll_All (getRegisters m) (getRules m) (getMethods m)).
  Proof.
    intros.
    assert (WfMod m) as P1;[constructor; auto|apply WfMod_getFlat in P1].
    unfold getFlat in P1; simpl in *.
    specialize (TraceInclusion_inlineAll_pos P1) as TMP; dest.
    inversion H0; auto.
  Qed.

  Definition inlineAll_All_BaseModuleWf (m : BaseModuleWf) :=
    Build_BaseModuleWf (WfBaseMod_inlineAll_All (wfBaseModule m)).

  Theorem TraceInclusion_inlineAll_pos_Wf (m : BaseModuleWf) :
    TraceInclusion m (inlineAll_All_BaseModuleWf m).
  Proof.
    specialize (TraceInclusion_flatten_r m) as P1.
    specialize (wfMod (flatten_ModWf m)) as P2.
    simpl in *; unfold flatten, getFlat in *; simpl in *.
    specialize (TraceInclusion_inlineAll_pos P2) as TMP; dest.
    eauto using TraceInclusion_trans.
  Qed.
End inline_all_all.

Section flatten_and_inline_all.
  Lemma inline_preserves_key_Meth (f : DefMethT) (meth : DefMethT):
    fst (inlineSingle_Meth f meth) = fst meth.
  Proof.
    destruct meth; auto.
  Qed.

  Corollary inline_preserves_keys_Meth (f : DefMethT) (l : list DefMethT) :
    (map fst (map (inlineSingle_Meth f) l)) = (map fst l).
  Proof.
    induction l; auto.
    simpl;rewrite inline_preserves_key_Meth; rewrite IHl; reflexivity.
  Qed.

  Lemma SameKeys_inlineSingle_Meth_pos meths :
    forall n,
      map fst meths = map fst (inlineSingle_Meths_pos meths n).
  Proof.
    induction meths; destruct n; simpl in *; auto.
    - rewrite inline_preserves_key_Meth, inline_preserves_keys_Meth; reflexivity.
    - unfold inlineSingle_Meths_pos in *; simpl in *.
      specialize (IHmeths n); case_eq (nth_error meths n);intros;[setoid_rewrite H; setoid_rewrite H in IHmeths|].
      + simpl; rewrite inline_preserves_key_Meth, inline_preserves_keys_Meth; reflexivity.
      + setoid_rewrite H; simpl; reflexivity.
  Qed.
  
  Lemma fold_left_nil xs :
    fold_left inlineSingle_Meths_pos xs nil = nil.
  Proof.
    induction xs; simpl; auto.
    unfold inlineSingle_Meths_pos in *; simpl.
    case_eq (nth_error (nil: list DefMethT) a); auto.
  Qed.
  
  Lemma SameKeys_inlineSome_Meths :
    forall xs meths,
    map fst meths = map fst (fold_left inlineSingle_Meths_pos xs meths).
  Proof.
    induction xs; simpl; auto.
    unfold inlineSingle_Meths_pos at 2.
    intros.
    case_eq (nth_error meths a);intros;setoid_rewrite H; auto.
    erewrite <-IHxs.
    rewrite inline_preserves_keys_Meth; reflexivity.
  Qed.
  (*
  Lemma SameKeys_inlineSome_Rules :
    forall (xs : nat) (meths : list DefMethT) (rules : list RuleT),
    map fst rules = map fst (inlineSingle_Rules_pos meths xs rules).
  Proof.
    induction xs; simpl.
    - intros; unfold inlineSingle_Rules_pos.
      simpl; destruct meths; auto.
      
    unfold inlineSingle_Rules_pos.
    intros.
    case_eq (nth_error meths a);intros;setoid_rewrite H; auto.
    erewrite <-IHxs.
    rewrite inline_preserves_keys_Meth; reflexivity.
  Qed.*)
  
  Corollary SameKeys_inlineAll_Meths meths:
    map fst meths = map fst (inlineAll_Meths meths).
  Proof.
    unfold inlineAll_Meths; rewrite <-SameKeys_inlineSome_Meths; reflexivity.
  Qed.

  Lemma map_inlineSingle_Rule_SameKey f rules:
    map fst (map (inlineSingle_Rule f) rules) = map fst rules.
  Proof.
    induction rules; simpl; auto.
    unfold inlineSingle_Rule at 1; destruct a; simpl.
    rewrite IHrules; reflexivity.
  Qed.
  
  Lemma SameKeys_inlineSome_Rules a:
    forall rules meths,
    map fst rules =  map fst (inlineSingle_Rules_pos meths a rules).
  Proof.
    intros; unfold inlineSingle_Rules_pos.
    case_eq (nth_error meths a); intros; auto.
    rewrite map_inlineSingle_Rule_SameKey; reflexivity.
  Qed.
  
  Lemma SameKeys_inlineAll_Rules meths:
    forall rules,
      map fst rules = map fst (inlineAll_Rules meths rules).
  Proof.
    unfold inlineAll_Rules.
    induction (seq 0 (Datatypes.length meths)); simpl; auto.
    intros.
    rewrite <- IHl.
    apply SameKeys_inlineSome_Rules.
  Qed.
  
  Theorem flatten_inline_everything_Wf (m : ModWf) :
    WfMod (flatten_inline_everything m).
  Proof.
    unfold flatten_inline_everything, inlineAll_All_mod.
    pose proof (flatten_WfMod (wfMod m)) as HWfm'.
    pose proof (HWfm') as HWfm.
    unfold flatten, getFlat in *.
    setoid_rewrite WfMod_createHide in HWfm'; dest.
    rewrite WfMod_createHide in *; dest.
    split; simpl in *.
    - repeat intro; specialize (H _ H3); rewrite <-SameKeys_inlineAll_Meths; assumption.
    - apply TraceInclusion_inlineAll_pos in H2; dest.
      unfold inlineAll_All in *; auto.
  Qed.

  Definition flatten_inline_everything_ModWf (m : ModWf) : ModWf :=
    (Build_ModWf (flatten_inline_everything_Wf m)).
  
  Lemma TraceHide_Trace m o s ls:
    Trace (HideMeth m s) o ls -> Trace m o ls.
  Proof.
    induction 1.
    - econstructor 1; eauto.
    - econstructor 2; eauto.
      inv HStep; auto.
  Qed.

  Lemma Trace_TraceHide m o s ls :
    Trace m o ls ->
    (forall l, In l ls -> In s (map fst (getAllMethods m)) -> (forall v,  getListFullLabel_diff (s, v) l = 0%Z)) ->
    Trace (HideMeth m s) o ls.
  Proof.
    induction 1; subst; simpl in *; intros.
    - constructor; auto.
    - econstructor 2; eauto.
      econstructor 2; eauto.
  Qed.

  Lemma Trace_TraceHide' m o s ls :
    Trace (HideMeth m s) o ls ->
    (forall l, In l ls -> In s (map fst (getAllMethods m)) -> (forall v,  getListFullLabel_diff (s, v) l = 0%Z)) /\
    Trace m o ls.
  Proof.
    induction 1; subst; simpl in *; intros.
    -  split; intros; try contradiction.
       constructor; auto.
    - dest; split; intros.
      + destruct H2;[subst|eapply H0; eauto].
        inv HStep.
        eapply HHidden; eauto.
      + econstructor 2; eauto.
        inv HStep; eauto.
  Qed.

  Lemma TraceHide_same m o ls:
    Trace m o ls ->
    forall s,
      ~ In s (map fst (getAllMethods m)) ->
      Trace (HideMeth m s) o ls.
  Proof.
    induction 1; simpl; subst; auto; intros.
    - econstructor; eauto.
    - econstructor 2; eauto.
      constructor; auto; intros; tauto.
  Qed.
    
  Lemma TraceHide_same' m o ls s:
    Trace (HideMeth m s) o ls ->
    Trace m o ls.
  Proof.
    intros.
    apply Trace_TraceHide' with (s := s) in H; auto.
    dest.
    auto.
  Qed.

  Lemma WeakInclusions_In_l l ls:
    In l ls ->
    forall ls',
      WeakInclusions ls ls' ->
      exists l',
        In l' ls' /\
        WeakInclusion l l'.
  Proof.
    induction ls; intros; try contradiction.
    destruct H; subst; inv H0.
    - exists l'; split; auto.
      left; reflexivity.
    - specialize (IHls H _ H3); dest.
      exists x; split; auto.
      right; assumption.
  Qed.

  Lemma WeakInclusions_In_r l ls':
    In l ls' ->
    forall ls,
      WeakInclusions ls ls' ->
      exists l',
        In l' ls /\
        WeakInclusion l' l.
  Proof.
    induction ls'; intros; inv H0; try contradiction.
    destruct H; subst.
    - exists l0; split; auto.
      left; reflexivity.
    - specialize (IHls' H _ H4); dest.
      exists x; split; auto.
      right; assumption.
  Qed.
  
  Lemma TraceInclusion'_HideMeth m m' s:
    TraceInclusion' m m' ->
    TraceInclusion' (HideMeth m s) (HideMeth m' s).
  Proof.
    unfold TraceInclusion'.
    intros.
    destruct (in_dec string_dec s (map fst (getAllMethods m))).
    - specialize (H _ _ (TraceHide_Trace H0)); dest.
      exists x; split; auto.
      destruct H.
      exists x0.
      eapply Trace_TraceHide; eauto.
      intros.
      inv H0;[inv H1; contradiction|].
      inv HStep.
      apply Trace_TraceHide' in HOldTrace; dest.
      inv H1.
      destruct H2.
      + subst.
        specialize (HHidden i v).
        destruct H9.
        specialize (H1 (s, v)).
        Omega.omega.
      + specialize (WeakInclusions_In_r _ H1 H7) as TMP; dest.
        specialize (H0 _ H2 i v).
        destruct H5.
        specialize (H5 (s, v)).
        Omega.omega.
    - apply Trace_TraceHide' in H0.
      dest.
      specialize (H _ _ H1).
      dest.
      exists x.
      split; auto.
      unfold TraceList in *.
      dest.
      exists x0.
      eapply Trace_TraceHide; eauto.
      intros.
      unfold getListFullLabel_diff in *.
      specialize (WeakInclusions_In_r _ H3 H2) as TMP; dest.
      specialize (In_nth_error _ _ H5) as TMP; dest.
      specialize (NotInDef_ZeroExecs_Trace (s, v) H1 n x2 H7) as P1.
      specialize (In_nth_error _ _ H3) as TMP; dest.
      specialize (Trace_meth_InCall_InDef_InExec H (s, v) x3 H8 H4) as P2.
      destruct H6; unfold getListFullLabel_diff in *.
      specialize (H6 (s, v)).
      assert (getNumCalls (s, v) x1 = 0%Z).
      + clear - H6 P1 P2.
        specialize (getNumCalls_nonneg (s, v) x1) as P3.
        Omega.omega.
      + rewrite H10, P1 in H6; clear - H6; Omega.omega.
  Qed.

  Corollary TraceInclusion_HideMeth m m' s:
    TraceInclusion m m' ->
    TraceInclusion (HideMeth m s) (HideMeth m' s).
  Proof.
    intros.
    apply TraceInclusion'_TraceInclusion.
    apply TraceInclusion_TraceInclusion' in H.
    eauto using TraceInclusion'_HideMeth.
  Qed.

  Lemma TraceInclusion_createHideMod m m' ls:
    TraceInclusion m m' ->
    TraceInclusion (createHideMod m ls) (createHideMod m' ls).
  Proof.
    intros; induction ls; auto; simpl in *.
    apply TraceInclusion_HideMeth.
    assumption.
  Qed.

  Lemma TraceInclusion'_TraceInclusion_iff m m' :
    TraceInclusion m m' <-> TraceInclusion' m m'.
  Proof.
    split; intros; eauto using TraceInclusion'_TraceInclusion, TraceInclusion_TraceInclusion'.
  Qed.
  
  Lemma Trace_createHide l m m' :
    TraceInclusion (Base m) (Base m') ->
    TraceInclusion (createHide m l) (createHide m' l).
  Proof.
    induction l; simpl in *; auto.
    intros.
    apply TraceInclusion_TraceInclusion' in H.
    apply TraceInclusion'_TraceInclusion.
    apply TraceInclusion'_HideMeth.
    apply TraceInclusion_TraceInclusion'; apply TraceInclusion'_TraceInclusion in H; auto.
  Qed.

  Lemma WfMod_WfBase_getFlat m:
    (WfMod m) ->
    (WfMod (Base (getFlat m))).
  Proof.
    intro.
    induction m; simpl in *.
    - intros.
      constructor 1; intros; apply WfMod_WfBaseMod_flat; auto; specialize (H ty); inv H; auto.
    - intros.
      unfold getFlat in *; simpl in *; apply IHm.
      intros.
      specialize (H).
      inv H; auto.
    - intros.
      assert (HWf1: WfMod m1) by (specialize (H);
                                  inv H; auto).
      assert (HWf2: WfMod m2) by (specialize (H);
                                  inv H; auto).
      assert (WfConcat1: WfConcat m1 m2) by
          (specialize (H); inv H; auto).
      assert (WfConcat2: WfConcat m2 m1) by
          (specialize (H); inv H; auto).
      specialize (H).
      inv H.
      specialize (IHm1 HWf1); specialize (IHm2 HWf2).
      constructor 1;
        ((apply WfMod_WfBaseMod_flat; constructor 3; auto)
         || (specialize (IHm1);
             specialize (IHm2);
             inv IHm1; inv IHm2;
             simpl in *; apply NoDupKey_Expand; auto)).
  Qed.
  
  Theorem TraceInclusion_flatten_inline_everything_r (m : ModWf) :
    TraceInclusion m (flatten_inline_everything_ModWf m).
  Proof.
    specialize (wfMod (flatten_inline_everything_ModWf m)) as Wf1.
    simpl.
    specialize (TraceInclusion_flatten_r m) as P1.
    unfold flatten, getFlat in *.
    assert (WfMod (Base (getFlat m))). {
      intros.
      apply (WfMod_WfBase_getFlat (wfMod m)).
    }
    unfold getFlat in *.
    specialize (TraceInclusion_inlineAll_pos H) as TMP; dest.
    unfold inlineAll_All in *.
    apply (Trace_createHide (getHidden m)) in H1.
    eauto using TraceInclusion_trans.
  Qed.
End flatten_and_inline_all.

Theorem inlineSingle_Rule_map_Wf {m : ModWf} {f : DefMethT} (inMeths : In f (getAllMethods m)):
  WfMod (createHide (inlineSingle_Rule_map_BaseModule f (getFlat m)) (getHidden m)).
Proof.
  intros.
  unfold inlineSingle_Rule_map_BaseModule.
  specialize (flatten_WfMod (wfMod m)) as P1; unfold flatten, getFlat in P1; simpl in P1.
  specialize (WfMod_inline_all_Rule (regs:= (getAllRegisters m)) (rules:= (getAllRules m)) (meths:= (getAllMethods m)) f (seq 0 (length (getAllRules m))) inMeths) as P2.
  repeat rewrite map_fold_right_eq in *.
  unfold getFlat in *; simpl in *.
  rewrite WfMod_createHide in *; dest; simpl in *; split; eauto.
Qed.

Definition inlineSingle_Rule_map_ModWf {m : ModWf} {f : DefMethT} (inMeths : In f (getAllMethods m)) :=
  (Build_ModWf (inlineSingle_Rule_map_Wf inMeths)).

Theorem inlineSingle_Meth_map_Wf {m : ModWf} {f : DefMethT} (inMeths : In f (getAllMethods m)) :
  WfMod (createHide (inlineSingle_Meth_map_BaseModule f (getFlat m)) (getHidden m)).
Proof.
  intros.
  unfold inlineSingle_Meth_map_BaseModule.
  specialize (flatten_WfMod (wfMod m)) as P1; unfold flatten, getFlat in P1; simpl in P1.
  specialize (WfMod_inline_all_Meth (regs:= (getAllRegisters m)) (rules:= (getAllRules m)) (meths:= (getAllMethods m)) f (seq 0 (length (getAllMethods m))) inMeths) as P2.
  repeat rewrite map_fold_right_eq in *.
  unfold getFlat in *; simpl in *.
  rewrite WfMod_createHide in *; dest; simpl in *; split; eauto.
  rewrite <- SameKeys_Meth_fold_right.
  assumption.
Qed.

Definition inlineSingle_Meth_map_ModWf {m : ModWf} {f : DefMethT} (inMeths : In f (getAllMethods m)) :=
  (Build_ModWf (inlineSingle_Meth_map_Wf inMeths)).

Theorem inlineSingle_Rule_map_TraceInclusion {m : ModWf} {f : DefMethT} (inMeths : In f (getAllMethods m)):
  TraceInclusion m (inlineSingle_Rule_map_ModWf inMeths).
Proof.
  intros.
  specialize (TraceInclusion_flatten_r m) as TI_flatten; simpl in *.
  unfold flatten, inlineSingle_Rule_map_BaseModule, getFlat in *; simpl in *.
  specialize (TraceInclusion_inline_BaseModule_rules f (WfMod_WfBase_getFlat (wfMod m)) inMeths) as P1.
  specialize (Trace_createHide (getHidden m) P1) as P2.
  apply (TraceInclusion_trans TI_flatten P2).
Qed.

Theorem inlineSingle_Meth_map_TraceInclusion {m : ModWf}  {f : DefMethT} (inMeths : In f (getAllMethods m)) :
  TraceInclusion m (inlineSingle_Meth_map_ModWf inMeths).
Proof.
  intros.
  specialize (TraceInclusion_flatten_r m) as TI_flatten; simpl in *.
  unfold flatten, inlineSingle_Meth_map_BaseModule, getFlat in *; simpl in *.
  specialize (TraceInclusion_inline_BaseModule_meths f (WfMod_WfBase_getFlat (wfMod m)) inMeths) as P1.
  specialize (Trace_createHide (getHidden m) P1) as P2.
  apply (TraceInclusion_trans TI_flatten P2).
Qed.

Definition inlineSingle_Module (f : DefMethT) (m : Mod) :=
  createHide (inlineSingle_BaseModule f (getAllRegisters m) (getAllRules m) (getAllMethods m)) (getHidden m).

Theorem inlineSingle_Module_Wf {m : ModWf} {f : DefMethT} (inMeths : In f (getAllMethods m)) :
  WfMod (inlineSingle_Module f m).
Proof.
  unfold inlineSingle_Module, inlineSingle_BaseModule; simpl.
  specialize (inlineSingle_Rule_map_Wf inMeths) as P1; unfold inlineSingle_Rule, inlineSingle_Rule_map_BaseModule, getFlat in P1; simpl in *.
  assert (In f (getAllMethods (createHide (inlineSingle_Rule_map_BaseModule f (getFlat m)) (getHidden m)))) as P2.
  - unfold inlineSingle_Rule_map_BaseModule, getFlat; simpl.
    rewrite createHide_Meths; simpl; assumption.
  - specialize (inlineSingle_Meth_map_Wf (m := Build_ModWf P1) P2) as P3; simpl in *.
    rewrite createHide_hides in P3; simpl in P3; unfold getFlat in P3.
    rewrite createHide_Regs, createHide_Rules, createHide_Meths in P3; simpl in P3.
    unfold inlineSingle_Meth_map_BaseModule in P3; simpl in P3.
    assumption.
Qed.
  
Definition inlineSingle_Module_ModWf {m : ModWf} {f : DefMethT} (inMeths : In f (getAllMethods m)) :=
  (Build_ModWf (inlineSingle_Module_Wf inMeths)).

Theorem inlineSingle_BaseModule_TraceInclusion {m : ModWf} {f : DefMethT} (inMeths : In f (getAllMethods m)) :
  TraceInclusion m (inlineSingle_Module_ModWf inMeths).
Proof.
  specialize (TraceInclusion_flatten_r  m) as TI_flatten; simpl in *.
  unfold flatten, getFlat in *; simpl in *.
  specialize (flatten_WfMod (wfMod m)) as P1; unfold flatten, getFlat in P1; simpl in P1.
  rewrite WfMod_createHide in P1; dest.
  specialize (TraceInclusion_inline_BaseModule_all _ H0 inMeths) as P2.
  specialize (Trace_createHide (getHidden m) P2) as P3.
  apply (TraceInclusion_trans TI_flatten P3).
Qed.

Theorem inlineSingle_BaseModule_nth_Meth_Wf {m : ModWf} {f : DefMethT} (inMeths : In f (getAllMethods m)) (xs : list nat) :
  WfMod (createHide (inlineSingle_BaseModule_nth_Meth f (getAllRegisters m) (getAllRules m) (getAllMethods m) xs) (getHidden m)).
Proof.
  specialize (flatten_WfMod (wfMod m)) as P1; unfold flatten, getFlat in P1; simpl in P1.
  rewrite WfMod_createHide in *; dest.
  specialize (WfMod_inline_all_Meth f xs inMeths H0) as P3.
  split; auto; simpl in *.
  rewrite <- SameKeys_Meth_fold_right; assumption.
Qed.

Definition inlineSingle_BaseModule_nth_Meth_ModWf {m : ModWf} {f : DefMethT} (inMeths : In f (getAllMethods m)) (xs : list nat) :=
  (Build_ModWf (inlineSingle_BaseModule_nth_Meth_Wf inMeths xs)).

Theorem inlineSingle_BaseModule_nth_Meth_TraceInclusion {m : ModWf} {f : DefMethT} (inMeths : In f (getAllMethods m)) (xs : list nat) :
  TraceInclusion m (inlineSingle_BaseModule_nth_Meth_ModWf inMeths xs).
Proof.
  specialize (TraceInclusion_flatten_r m) as TI_flatten; simpl in *.
  unfold flatten, getFlat in *; simpl in *.
  specialize (flatten_WfMod (wfMod m)) as P1; unfold flatten, getFlat in P1; simpl in P1.
  rewrite WfMod_createHide in P1; dest.
  specialize (inline_meth_fold_right _ H0 xs inMeths) as P2.
  specialize (Trace_createHide (getHidden m) P2) as P3.
  apply (TraceInclusion_trans TI_flatten P3).
Qed.

Theorem inlineSingle_BaseModule_nth_Rule_Wf {m : ModWf} {f : DefMethT} (inMeths : In f (getAllMethods m)) (xs : list nat) :
  WfMod (createHide (inlineSingle_BaseModule_nth_Rule f (getAllRegisters m) (getAllRules m) (getAllMethods m) xs) (getHidden m)).
Proof.
  specialize (flatten_WfMod (wfMod m)) as P1; unfold flatten, getFlat in P1; simpl in P1.
  rewrite WfMod_createHide in *; dest; split; auto.
  apply (WfMod_inline_all_Rule f xs inMeths H0).
Qed.

Definition inlineSingle_BaseModule_nth_Rule_ModWf {m : ModWf} {f : DefMethT} (inMeths : In f (getAllMethods m)) (xs : list nat) :=
  (Build_ModWf (inlineSingle_BaseModule_nth_Rule_Wf inMeths xs)).

Theorem inlineSingle_BaseModule_nth_Rule_TraceInclusion {m : ModWf} {f : DefMethT} (inMeths : In f (getAllMethods m)) (xs : list nat) :
  TraceInclusion m (inlineSingle_BaseModule_nth_Rule_ModWf inMeths xs).
Proof.
  specialize (TraceInclusion_flatten_r m) as TI_flatten; simpl in *.
  unfold flatten, getFlat in *; simpl in *.
  specialize (flatten_WfMod (wfMod m)) as P1; unfold flatten, getFlat in P1; simpl in P1.
  rewrite WfMod_createHide in P1; dest.
  specialize (inline_rule_fold_right _ H0 xs inMeths) as P2.
  specialize (Trace_createHide (getHidden m) P2) as P3.
  apply (TraceInclusion_trans TI_flatten P3).
Qed.

Definition inlineAll_Rules_Mod (m : Mod) :=
  (createHide (inlineAll_Rules_mod (getFlat m)) (getHidden m)).

Theorem inlineAll_Rules_Wf (m : ModWf):
  WfMod (inlineAll_Rules_Mod m).
Proof.
  specialize (flatten_WfMod (wfMod m)) as P1; unfold flatten, getFlat in P1; simpl in P1.
  unfold inlineAll_Rules_Mod; rewrite WfMod_createHide in *; dest; split; auto.
  apply (TraceInclusion_inlineAll_pos_Rules H0).
Qed.

Definition inlineAll_Rules_ModWf (m : ModWf) :=
  (Build_ModWf (inlineAll_Rules_Wf m)).

Theorem inlineAll_Rules_TraceInclusion (m : ModWf) :
  TraceInclusion m (inlineAll_Rules_ModWf m).
Proof.
  specialize (flatten_WfMod (wfMod m)) as P1; unfold flatten, getFlat in P1; simpl in P1.
  rewrite WfMod_createHide in P1; dest.
  specialize (TraceInclusion_inlineAll_pos_Rules H0) as P2; dest.
  specialize (Trace_createHide (getHidden m) H2) as P1.
  specialize (TraceInclusion_flatten_r m) as TI_flatten; simpl in *.
  unfold flatten, getFlat in *; simpl in *.
  apply (TraceInclusion_trans TI_flatten P1).
Qed.

Definition inlineAll_Meths_Mod (m : Mod) :=
  (createHide (inlineAll_Meths_mod (getFlat m)) (getHidden m)).

Theorem inlineAll_Meths_Wf (m : ModWf) :
  WfMod (inlineAll_Meths_Mod m).
Proof.
  specialize (flatten_WfMod (wfMod m)) as P1; unfold flatten, getFlat in P1; simpl in P1.
  unfold inlineAll_Meths_Mod, inlineAll_Meths_Mod, inlineAll_Meths_mod, inlineAll_Meths; rewrite WfMod_createHide in *; dest; split; simpl in *.
  - rewrite <- SameKeys_inlineSome_Meths; assumption.
  - apply (TraceInclusion_inlineAll_pos_Meths H0).
Qed.

Definition inlineAll_Meths_ModWf (m : ModWf) :=
  (Build_ModWf (inlineAll_Meths_Wf m)).

Theorem inlineAll_Meths_TraceInclusion (m : ModWf) :
  TraceInclusion m (inlineAll_Meths_ModWf m).
Proof.
  specialize (flatten_WfMod (wfMod m)) as P1; unfold flatten, getFlat in P1; simpl in P1.
  rewrite WfMod_createHide in P1; dest.
  specialize (TraceInclusion_inlineAll_pos_Meths H0) as P2; dest.
  specialize (Trace_createHide (getHidden m) H2) as P1.
  specialize (TraceInclusion_flatten_r m) as TI_flatten; simpl in *.
  unfold flatten, getFlat in *; simpl in *.
  apply (TraceInclusion_trans TI_flatten P1).
Qed.

Theorem flatten_inline_remove_Wf (m : ModWf) :
  WfMod (flatten_inline_remove m).
Proof.
  unfold flatten_inline_remove.
  specialize (TraceInclusion_inlineAll_pos (WfMod_WfBase_getFlat (wfMod m))) as P1; dest.
  inv H; unfold WfBaseModule in *; dest.
  econstructor; repeat split; unfold removeHides; simpl in *; intros; eauto.
  - specialize (H _ H5).
    unfold inlineAll_All in *.
    induction H; econstructor; eauto.
  - rewrite filter_In in H5; dest.
    specialize (H1 _ H5 v).
    induction H1; econstructor; eauto.
  - clear - H2.
    induction (inlineAll_Meths (getAllMethods m)); simpl; auto.
    destruct negb.
    + simpl in *; econstructor; inv H2; auto.
      intro P1; apply H1.
      rewrite in_map_iff in P1; dest.
      rewrite <- H.
      rewrite filter_In in H0; dest.
      rewrite in_map_iff; exists x; auto.
    + inv H2; auto.
Qed.

Definition flatten_inline_remove_ModWf (m : ModWf) :=
  (Build_ModWf (flatten_inline_remove_Wf m)).

Definition removeMeth (m : BaseModule) (s : string) :=
  (BaseMod (getRegisters m) (getRules m) ((filter (fun df => (negb (getBool (string_dec s (fst df)))))) (getMethods m))).

Lemma Substeps_removeMeth (f : string) (m : BaseModule) (o : RegsT) (l : list FullLabel):
  Substeps m o l ->
  (forall v, getNumCalls (f, v) l = 0%Z) ->
  (forall v, getNumExecs (f, v) l = 0%Z) ->
  Substeps (removeMeth m f) o l.
Proof.
  induction 1; intros.
  - econstructor 1; eauto.
  - rewrite HLabel in *; simpl in *.
    econstructor; eauto.
    assert (((u, (Rle rn, cs)) :: ls) = [(u, (Rle rn, cs))]++ls) as TMP; auto.
    apply IHSubsteps; intros.
    + specialize (H0 v).
      rewrite TMP in H0; rewrite getNumCalls_app in H0.
      specialize (getNumCalls_nonneg (f, v) [(u, (Rle rn, cs))]) as TMP2.
      specialize (getNumCalls_nonneg (f, v) ls) as TMP3.
      omega.
    + specialize (H1 v).
      rewrite TMP in H1; rewrite getNumExecs_app in H1.
      specialize (getNumExecs_nonneg (f, v) [(u, (Rle rn, cs))]) as TMP2.
      specialize (getNumExecs_nonneg (f, v) ls) as TMP3.
      omega.
  - rewrite HLabel in *; simpl in *.
    econstructor 3; eauto.
    + destruct (string_dec f fn); subst.
      * exfalso.
        specialize (H1 (existT SignT (projT1 fb) (argV, retV))).
        unfold getNumExecs in H1.
        rewrite map_cons in H1.
        assert ((fst (snd (u, (Meth (fn, existT SignT (projT1 fb) (argV, retV)), cs)))) = Meth (fn, existT SignT (projT1 fb) (argV, retV))) as TMP; auto; rewrite TMP in H1; clear TMP.
        rewrite getNumFromExecs_eq_cons in H1; auto.
        specialize (getNumFromExecs_nonneg (fn, existT SignT (projT1 fb) (argV, retV)) (map PPT_execs ls)) as TMP2.
        omega.
      * unfold removeMeth.
        simpl.
        rewrite filter_In.
        split; auto.
        simpl.
        destruct (string_dec); auto.
    + apply IHSubsteps; intros.
      * specialize (H0 v).
        rewrite getNumCalls_cons in H0; simpl in H0.
        specialize (getNumFromCalls_nonneg (f, v) cs) as TMP1.
        specialize (getNumCalls_nonneg (f, v) ls) as TMP2.
        omega.
      * specialize (H1 v).
        assert (((u, (Meth (fn, existT SignT (projT1 fb) (argV, retV)), cs)) :: ls) = [(u, (Meth (fn, existT SignT (projT1 fb) (argV, retV)), cs))] ++ ls) as TMP1; auto.
        rewrite TMP1 in H1.
        rewrite getNumExecs_app in H1.
        specialize (getNumExecs_nonneg (f, v) [(u, (Meth (fn, existT SignT (projT1 fb) (argV, retV)), cs))]) as TMP2.
        specialize (getNumExecs_nonneg (f, v) ls) as TMP3.
        omega.
Qed.

Lemma Substeps_HideMeth (f : string) (m : BaseModule) (o :RegsT) (l : list FullLabel) :
  Substeps (removeMeth m f) o l ->
  Substeps m o l.
Proof.
  induction 1.
  - econstructor 1; eauto.
  - subst; econstructor 2; eauto.
  - subst; econstructor 3; eauto.
    simpl in HInMeths.
    rewrite filter_In in HInMeths; destruct HInMeths; auto.
Qed.

Lemma Step_removeMeth (f : string) (m : BaseModule) (o : RegsT) (l : list FullLabel) :
  Step m o l ->
  (forall v, getNumCalls (f, v) l = 0%Z) ->
  (forall v, getNumExecs (f, v) l = 0%Z) ->
  Step (removeMeth m f) o l.
Proof.
  intros.
  inv H.
  econstructor; eauto using Substeps_removeMeth.
  unfold MatchingExecCalls_Base in *; simpl.
  intros.
  specialize (HMatching f0).
  rewrite in_map_iff in H; dest.
  rewrite filter_In in H2; dest.
  rewrite <- H in HMatching.
  apply (in_map fst) in H2.
  auto.
Qed.

Lemma Step_removeMeth_HideMeth_noCalls (f : string) (m : BaseModule) (o : RegsT) (l : list FullLabel) :
  Step (removeMeth m f) o l ->
  (forall v, getNumCalls (f, v) l = 0%Z) ->
  Step (HideMeth m f) o l.
Proof.
  intros; inv H.
  econstructor.
  - econstructor.
    + eapply Substeps_HideMeth; eauto.
    + intros f0 P1.
      specialize (HMatching f0); simpl in *.
      destruct (string_dec f (fst f0)); subst.
      * destruct f0; simpl in *; rewrite H0.
        apply getNumExecs_nonneg.
      * rewrite (in_map_iff) in P1; inv P1; inv H.
        assert (In x (filter (fun df : string * {x : Signature & MethodT x} =>
                                negb (getBool (string_dec f (fst df)))) (getMethods m))).
        -- rewrite filter_In; split; auto.
           destruct (string_dec f (fst x)); simpl; auto.
           exfalso.
           rewrite H1 in e; tauto.
        -- apply (in_map fst) in H; rewrite H1 in H.
           eauto.
  - intros.
    unfold getListFullLabel_diff; rewrite H0.
    assert (~In f (map fst (getMethods (removeMeth m f)))).
    + intro; rewrite in_map_iff in H1; inv H1; inv H2.
      simpl in H3; rewrite filter_In in H3; inv H3.
      destruct string_dec; simpl in *;[discriminate|].
      apply n; reflexivity.
    + rewrite in_map_iff in H; inv H; inv H2.
      rewrite (NotInDef_ZeroExecs_Substeps (fst x, v) H1 HSubsteps); simpl; reflexivity.
Qed.

Lemma Step_HideMeth_removeMeth_noCalls (f : string) (m : BaseModule) (o : RegsT) (l : list FullLabel) (wfMod : WfMod m):
  Step (HideMeth m f) o l ->
  (forall v, getNumCalls (f, v) l = 0%Z) ->
  Step (removeMeth m f) o l.
Proof.
  intros.
  destruct (in_dec string_dec f (map fst (getMethods m))).
  - inv H.
    specialize (HHidden i).
    apply Step_removeMeth; auto.
    intro; specialize (HHidden v); specialize (H0 v).
    unfold getListFullLabel_diff in HHidden.
    rewrite H0 in HHidden.
    omega.
  - inv H.
    unfold removeMeth.
    rewrite filter_true_list.
    + apply Step_substitute in HStep; auto.
    + intros.
      destruct (string_dec).
      * exfalso.
        apply (in_map fst) in H; rewrite <- e in H.
        tauto.
      * simpl; reflexivity.
Qed.

Lemma Trace_HideMeth_removeMeth_noCalls (f : string) (m : BaseModule) (o : RegsT) (ls : list (list FullLabel)) (wfMod : WfMod m) :
  Trace (HideMeth m f) o ls ->
  (forall l, In l ls -> forall v, getNumCalls (f, v) l = 0%Z) ->
  Trace (removeMeth m f) o ls.
Proof.
  induction 1; subst; intros.
  - econstructor 1; eauto.
  - econstructor 2; eauto.
    eapply IHTrace.
    intros.
    eapply H0.
    right; assumption.
    apply Step_HideMeth_removeMeth_noCalls; auto.
    intros.
    eapply H0; left; reflexivity.
Qed.

Lemma Trace_removeMeth_HideMeth_noCalls (f : string) (m : BaseModule) (o : RegsT) (ls : list (list FullLabel)) (wfMod : WfMod m) :
  Trace (removeMeth m f) o ls ->
  (forall l, In l ls -> forall v, getNumCalls (f, v) l = 0%Z) ->
  Trace (HideMeth m f) o ls.
Proof.
  induction 1; subst; intros.
  - econstructor 1; eauto.
  - econstructor 2; eauto.
    + eapply IHTrace; intros.
      eapply H0; right; assumption.
    + apply Step_removeMeth_HideMeth_noCalls; auto.
      intros; apply H0; left; reflexivity.
Qed.

Lemma NoSelfCallBaseModule_Substeps f m o l:
  NoSelfCallBaseModule m ->
  Substeps m o l ->
  In f (map fst (getMethods m)) ->
  (forall v, getNumCalls (f, v) l = 0%Z).
Proof.
  induction 2; intros.
  - apply getNumCalls_nil.
  - rewrite HLabel in *.
    rewrite getNumCalls_cons; simpl in *.
    rewrite (IHSubsteps H1).
    rewrite (NoSelfCallRule_Impl _ H HInRules HAction (f, v) H1).
    simpl; reflexivity.
  - rewrite HLabel in *.
    rewrite getNumCalls_cons; simpl in *.
    rewrite (IHSubsteps H1).
    rewrite (NoSelfCallMeth_Impl _ H HInMeths argV HAction (f, v) H1).
    simpl; reflexivity.
Qed.

Lemma NoSelfCallBaseModule_Step f m o l:
  NoSelfCallBaseModule m ->
  Step m o l ->
  In f (map fst (getMethods m)) ->
  (forall v, getNumCalls (f, v) l = 0%Z).
Proof.
  intros; inv H0.
  eapply NoSelfCallBaseModule_Substeps; eauto.
Qed.

Lemma NoSelfCallBaseModule_Trace f m o ls :
  NoSelfCallBaseModule m ->
  Trace m o ls ->
  In f (map fst (getMethods m)) ->
  (forall l, In l ls -> forall v, getNumCalls (f, v) l = 0%Z).
Proof.
  induction 2; subst; simpl in *; intros.
  - contradiction.
  - destruct H2; subst.
    + eapply NoSelfCallBaseModule_Step; eauto.
    + eapply IHTrace; eauto.
Qed.

Lemma NoSelfCallBaseModule_TraceHide f (m : BaseModuleWf) o ls :
  NoSelfCallBaseModule m ->
  Trace (HideMeth m f) o ls ->
  Trace (removeMeth m f) o ls.
Proof.
  destruct (in_dec string_dec f (map fst (getMethods m))).
  - intros.
    apply Trace_HideMeth_removeMeth_noCalls; auto.
    + constructor; apply wfBaseModule.
    + intros.
      specialize (TraceHide_Trace H0) as P1.
      eapply NoSelfCallBaseModule_Trace; eauto.
  - intros.
    apply TraceHide_Trace in H0.
    unfold removeMeth; simpl.
    rewrite filter_true_list.
    + apply (Trace_flatten_same1 m H0).
    + intros; destruct string_dec; subst.
      * exfalso; apply n; apply (in_map fst) in H1; assumption.
      * simpl; reflexivity.
Qed.

Lemma SubstepsRemove_Substeps m o s l :
  Substeps (removeMeth m s) o l -> Substeps m o l.
Proof.
  induction 1.
  - econstructor 1; eauto.
  - rewrite HLabel; econstructor 2; eauto.
  - rewrite HLabel; econstructor 3; eauto.
    simpl in HInMeths.
    rewrite filter_In in HInMeths; inv HInMeths; auto.
Qed.

Lemma StepRemove_Step m o s l :
  (forall v, getNumCalls (s, v) l = 0%Z) ->
  Step (removeMeth m s) o l ->
  Step m o l.
Proof.
  intros; inv H0.
  econstructor; eauto using SubstepsRemove_Substeps.
  intros f P1.
  destruct (string_dec s (fst f)); subst.
  - destruct f; simpl in *.
    rewrite H.
    apply getNumExecs_nonneg.
  - assert (In (fst f) (map fst (getMethods (removeMeth m s)))).
    + simpl; rewrite in_map_iff in *.
      inv P1; inv H0.
      exists x; split; auto.
      rewrite filter_In; split; auto.
      destruct string_dec; simpl; auto.
      exfalso; apply n.
      rewrite e; auto.
    + apply HMatching; auto.
Qed.

Lemma TraceRemove_Trace m o s ls :
  (forall l, In l ls -> forall v, getNumCalls (s, v) l = 0%Z) ->
  Trace (removeMeth m s) o ls ->
  Trace m o ls.
Proof.
  intros.
  induction H0; subst.
  - econstructor 1; eauto.
  - econstructor 2; eauto.
    + apply IHTrace.
      intros; apply H.
      right; assumption.
    + eapply (StepRemove_Step); eauto.
      eapply H.
      left; reflexivity.
Qed.

Lemma Substeps_NoSelfCallBaseModule_Remove m o s l :
  In s (map fst (getMethods m)) ->
  NoSelfCallBaseModule m ->
  Substeps (removeMeth m s) o l ->
  (forall v, getNumCalls (s, v) l = 0%Z).
Proof.
  intros.
  apply SubstepsRemove_Substeps in H1.
  eapply NoSelfCallBaseModule_Substeps; eauto.
Qed.

Lemma Step_NoSelfCallBaseModule_Remove m o s l :
  In s (map fst (getMethods m)) ->
  NoSelfCallBaseModule m ->
  Step (removeMeth m s) o l ->
  (forall v, getNumCalls (s, v) l = 0%Z).
Proof.
  intros.
  inv H1.
  eapply Substeps_NoSelfCallBaseModule_Remove; eauto.
Qed.

Lemma Trace_NoSelfCallBaseModule_Remove m o s ls :
  In s (map fst (getMethods m)) ->
  NoSelfCallBaseModule m ->
  Trace (removeMeth m s) o ls ->
  (forall l, In l ls -> forall v, getNumCalls (s, v) l = 0%Z).
Proof.
  intros.
  induction H1; subst.
  - destruct H2.
  - destruct H2; subst.
    + eapply Step_NoSelfCallBaseModule_Remove; eauto.
    + apply IHTrace; auto.
Qed.

Lemma Trace_NoSelfCallBaseModule_Remove_Hide m o s ls :
  In s (map fst (getMethods m)) ->
  NoSelfCallBaseModule m ->
  Trace (removeMeth m s) o ls ->
  Trace (HideMeth m s) o ls.
Proof.
  intros.
  apply Trace_TraceHide.
  - eapply TraceRemove_Trace; eauto.
    eapply Trace_NoSelfCallBaseModule_Remove; eauto.
  - intros; unfold getListFullLabel_diff.
    rewrite (Trace_NoSelfCallBaseModule_Remove H H0 H1 _ H2 v).
    specialize (In_nth_error _ _ H2) as P1. destruct P1 as [n P2].
    erewrite (NotInDef_ZeroExecs_Trace); simpl; auto.
    + apply H1.
    + simpl; intro P1.
      rewrite in_map_iff in P1.
      inv P1; inv H4.
      rewrite filter_In in H6; inv H6.
      destruct string_dec; simpl in *.
      * discriminate.
      * apply n0; reflexivity.
    + apply P2.
Qed.

Lemma removeMeth_removeHides m f :
  (getMethods (removeMeth m f)) = (getMethods (removeHides m [f])).
Proof.
  simpl.
  induction (getMethods m); simpl; auto.
  - destruct string_dec; simpl; auto.
    rewrite IHl; reflexivity.
Qed.

Lemma removeHides_cons m f l:
  (getMethods (removeHides m (f::l))) = (getMethods (removeHides (removeHides m l) [f])).
Proof.
  simpl.
  induction (getMethods m); simpl; auto.
  destruct string_dec; subst; simpl.
  - repeat rewrite IHl0; simpl.
    destruct (in_dec string_dec (fst a) l); simpl in *; auto.
    destruct (string_dec); simpl; auto.
    exfalso; auto.
  - repeat rewrite IHl0; simpl.
    destruct (in_dec string_dec (fst a) l); simpl in *; auto.
    destruct string_dec; auto.
    exfalso; auto.
Qed.

Lemma removeMeth_removeHides_cons m f l:
  (getMethods (removeHides m (f::l)) = (getMethods (removeMeth (removeHides m l) f))).
Proof.
  rewrite removeHides_cons.
  rewrite removeMeth_removeHides.
  reflexivity.
Qed.

Lemma removeHidesWfActionT (m : BaseModule)(k : Kind) (a : ActionT type k) (l : list string):
  WfActionT m a ->
  WfActionT (removeHides m l) a.
Proof.
  induction 1; econstructor; eauto.
Qed.

Lemma NoDup_filtered_keys {B : Type} (l : list (string*B)) (f : (string*B) -> bool):
  NoDup (map fst l) -> NoDup (map fst (filter f l)).
Proof.
  induction l; intros; auto.
  inv H; simpl; destruct (f a); eauto.
  simpl; constructor; eauto.
  intro; apply H2.
  rewrite in_map_iff in *.
  destruct H; destruct H; subst.
  rewrite filter_In in H0; destruct H0.
  eauto.
Qed.

Lemma removeHidesWf (m : BaseModule) (l : list string):
  WfBaseModule m ->
  WfBaseModule (removeHides m l).
Proof.
  intros.
  inv H; inv H1; inv H2; inv H3.
  repeat split; intros; auto.
  - specialize (H0 _ H3).
    apply removeHidesWfActionT; assumption.
  - simpl in H3.
    rewrite (filter_In) in H3; inv H3.
    specialize (H _ H5 v).
    apply removeHidesWfActionT; auto.
  - simpl.
    apply NoDup_filtered_keys; auto.
Qed.

Lemma removeMethWf (m : BaseModule) (f : string) :
  WfBaseModule m ->
  WfBaseModule (removeMeth m f).
Proof.
  intros.
  specialize (WfMod_WfBaseMod_flat (BaseWf (removeHidesWf [f] H))) as P1.
  unfold getFlat in P1.
  assert (getAllMethods (removeHides m [f]) = getMethods (removeHides m [f])) as P2; auto.
  rewrite P2 in P1.
  rewrite <- removeMeth_removeHides in P1.
  unfold removeMeth; simpl in P1; assumption.
Qed.

Definition removeHides_ModWf (m : BaseModuleWf) (l : list string) :=
  Build_BaseModuleWf (removeHidesWf l (wfBaseModule m)).

Lemma WfMod_createHide1 (m : BaseModuleWf) (l : list string) (subList : SubList l (map fst (getMethods m))):
  WfMod (createHide m l).
Proof.
  rewrite WfMod_createHide; split; auto.
  apply (BaseWf (wfBaseModule m)).
Qed.

Definition createHide_ModWf (m : BaseModuleWf) (l : list string) (subList : SubList l (map fst (getMethods m))) := (Build_ModWf (WfMod_createHide1 m subList)).

Lemma HideMeth_removeMeth_TraceInclusion (m : BaseModuleWf) (f : string):
  NoSelfCallBaseModule m ->
  TraceInclusion (HideMeth m f) (removeMeth m f).
Proof.
  repeat intro.
  exists o1, ls1; repeat split; auto.
  apply NoSelfCallBaseModule_TraceHide; auto.
  apply (WeakInclusions_WeakInclusion (WeakInclusionsRefl ls1)).
Qed.

Lemma removeMeth_HideMeth_TraceInclusion (m : BaseModuleWf) (f : string):
  NoSelfCallBaseModule m ->
  In f (map fst (getMethods m)) ->
  TraceInclusion (removeMeth m f) (HideMeth m f).
Proof.
  repeat intro.
  exists o1, ls1; repeat split.
  - apply Trace_NoSelfCallBaseModule_Remove_Hide; auto.
  - apply WeakInclusions_WeakInclusion; apply WeakInclusionsRefl.
Qed.

Lemma NoSelfCallBaseModule_removeHides (m : BaseModule) (l : list string) :
  NoSelfCallBaseModule m ->
  NoSelfCallBaseModule (removeHides m l).
Proof.
  unfold NoSelfCallBaseModule; intros; inv H; split.
  - repeat intro.
    specialize (H0 _ H).
    induction H0; econstructor; eauto.
    simpl; intro.
    apply H0.
    rewrite in_map_iff in *; inv H4; inv H5.
    rewrite filter_In in H6; inv H6.
    exists x; auto.
  - repeat intro.
    simpl in *; rewrite filter_In in H; inv H.
    specialize (H1 _ H2 arg).
    induction H1; econstructor; eauto.
    intro; apply H.
    rewrite in_map_iff in *; inv H5; inv H6.
    rewrite filter_In in H7; inv H7.
    exists x; auto.
Qed.

Lemma NoSelfCallBaseModule_removeMeth (m : BaseModule) (f : string) :
  NoSelfCallBaseModule m ->
  NoSelfCallBaseModule (removeMeth m f).
Proof.
  intros; inv H.
  split; repeat intro.
  - specialize (H0 _ H).
    induction H0; econstructor; eauto.
    intro; apply H0.
    rewrite in_map_iff in *.
    inv H4; inv H5.
    exists x; split; auto.
    simpl in H6; rewrite filter_In in H6; inv H6.
    destruct string_dec; simpl in *;[discriminate|auto].
  - assert (In meth (getMethods m)).
    + simpl in *; rewrite filter_In in H; inv H; auto.
    + specialize (H1 _ H2 arg).
      induction H1; econstructor; eauto.
      intro; apply H1.
      rewrite in_map_iff in *; inv H5; inv H6.
      exists x; split; auto.
      simpl in *; rewrite filter_In in H7.
      inv H7; auto.
Qed.  

Lemma removeHides_removeMeth_TraceInclusion m l a :
  TraceInclusion (removeMeth (removeHides_ModWf m l) a) (removeHides_ModWf m (a::l)).
Proof.
  specialize (TraceInclusion_flatten_r (Build_ModWf (BaseWf (removeMethWf a (wfBaseModule (removeHides_ModWf m l)))))) as P1.
  simpl in *; unfold flatten, getFlat in *; simpl in *.
  specialize (removeMeth_removeHides_cons m a l) as P2; simpl in *.
  rewrite <- P2 in P1.
  unfold removeMeth, removeHides in *; simpl in *.
  assumption.
Qed.

Lemma removeMeth_removeHides_TraceInclusion m l a :
  TraceInclusion (removeHides_ModWf m (a::l)) (removeMeth (removeHides_ModWf m l) a).
Proof.
  specialize (TraceInclusion_flatten_l (Build_ModWf (BaseWf (removeMethWf a (wfBaseModule (removeHides_ModWf m l)))))) as P1.
  simpl in *; unfold flatten, getFlat in *; simpl in *.
  specialize (removeMeth_removeHides_cons m a l) as P2; simpl in *.
  rewrite <- P2 in P1.
  unfold removeMeth, removeHides in *; simpl in *.
  assumption.
Qed.

Lemma createHide_Step_In m l a o ls:
  In a l ->
  Step (createHide m l) o ls ->
  (In a (map fst (getAllMethods m)) ->
   forall v, getListFullLabel_diff (a, v) ls = 0%Z).
Proof.
  induction l; simpl; [tauto|].
  intros.
  destruct H; subst; inv H0; auto.
  apply HHidden.
  rewrite createHide_Meths; assumption.
Qed.

Lemma createHide_idempotent m l a :
  In a l ->
  TraceInclusion (createHide m l) (HideMeth (createHide m l) a).
Proof.
  repeat intro.
  exists o1, ls1.
  repeat split; auto.
  - induction H0; subst.
    + econstructor; eauto.
    + econstructor 2; eauto.
      econstructor 2; eauto.
      intros; eapply createHide_Step_In.
      * apply H.
      * apply HStep.
      * rewrite createHide_Meths in H1; simpl in *; auto.
  - apply WeakInclusions_WeakInclusion; apply WeakInclusionsRefl.
Qed.  

Lemma removeMeth_removeHides_cons_In m f l:
  In f l ->
  getMethods (removeHides m l) = getMethods (removeMeth (removeHides m l) f).
Proof.
  intros; simpl.
  induction (getMethods m); simpl; auto.
  - destruct in_dec; simpl; auto.
    destruct string_dec; subst; simpl;[contradiction|].
    rewrite IHl0 at 1; reflexivity.
Qed.

Lemma removeMeth_idempotent (m : BaseModuleWf) l a :
  In a l ->
  (removeHides m l) = (removeMeth (removeHides m l) a).
Proof.
  intros.
  specialize (removeMeth_removeHides_cons_In m _ _ H) as P1.
  unfold removeHides, removeMeth in *; simpl in *; rewrite P1 at 1.
  reflexivity.
Qed.

Theorem removeHides_createHide_TraceInclusion (m : BaseModuleWf) (l : list string) (subList : SubList l (map fst (getMethods m))):
  NoSelfCallBaseModule m ->
  TraceInclusion (removeHides_ModWf m l) (createHide_ModWf m subList).
Proof.
  induction l; simpl; intros.
  - unfold removeHides; simpl.
    rewrite filter_true_list; simpl; auto.
    specialize (TraceInclusion_flatten_l m) as P1.
    simpl in *; unfold flatten, getFlat in *; simpl in *.
    assumption.
  - specialize (removeMeth_removeHides_TraceInclusion (m:=m) (l:=l) (a:=a)) as P1.
    assert (SubList l (map fst (getMethods m))) as P2;[repeat intro; apply (subList x (in_cons a _ _ H0))|].
    specialize (TraceInclusion_TraceInclusion' (IHl P2 H)) as P3.
    specialize (TraceInclusion'_TraceInclusion (TraceInclusion'_HideMeth P3 (s:=a))) as P4; clear P3.
    destruct (in_dec string_dec a l).
    + specialize (createHide_idempotent m _ _ i) as P5.
      simpl in P1.
      rewrite <- removeMeth_idempotent in P1; auto.
      specialize (IHl P2 H).
      eauto using TraceInclusion_trans.
    + assert (In a (map fst (getMethods (removeHides_ModWf m l)))) as P5.
      * simpl; rewrite in_map_iff.
        specialize (subList _ (in_eq _ _)).
        rewrite in_map_iff in subList.
        inv subList; inv H0.
        exists x; split; auto.
        rewrite filter_In; split; auto.
        destruct in_dec; simpl; auto.
      * specialize (removeMeth_HideMeth_TraceInclusion (removeHides_ModWf m l) (NoSelfCallBaseModule_removeHides l H) (f:= a) P5) as P6.
      eauto using TraceInclusion_trans.
Qed.

Theorem createHide_removeHides_TraceInclusion (m : BaseModuleWf) (l : list string) (subList : SubList l (map fst (getMethods m))):
  NoSelfCallBaseModule m ->
  TraceInclusion (createHide_ModWf m subList) (removeHides_ModWf m l).
Proof.
  induction l; simpl; intros.
  - unfold removeHides; simpl.
    rewrite filter_true_list; simpl; auto.
    specialize (TraceInclusion_flatten_r m) as P1.
    simpl in *; unfold flatten, getFlat in *; simpl in *.
    apply P1.
  - specialize (SubList_cons subList) as P0; inv P0.
    specialize (TraceInclusion_TraceInclusion' (IHl H1 H)) as P1.
    specialize (TraceInclusion'_TraceInclusion (TraceInclusion'_HideMeth P1 (s:= a))) as P2; clear P1.
    specialize (HideMeth_removeMeth_TraceInclusion (removeHides_ModWf m l) (f:=a) (NoSelfCallBaseModule_removeHides l H)) as P1.
    specialize (removeHides_removeMeth_TraceInclusion) as P3; specialize (P3 m l a).
    eauto using TraceInclusion_trans.
Qed.

Theorem flatten_inline_remove_TraceInclusion_r_lemma (m : ModWf) :
  NoSelfCallBaseModule (inlineAll_All_mod m) ->
  TraceInclusion (flatten_inline_everything m) (flatten_inline_remove_ModWf m).
Proof.
  simpl; unfold flatten_inline_everything, flatten_inline_remove.
  intros.
  specialize (WfMod_WfBase_getFlat (wfMod m)) as P1; unfold getFlat in *.
  specialize (TraceInclusion_inlineAll_pos P1) as P2; inv P2.
  inv H0.
  assert (SubList (getHidden m) (map fst (getAllMethods m))) as P2;
    [repeat intro; apply (WfMod_Hidden (wfMod m) _ H0)|].
  specialize (createHide_removeHides_TraceInclusion (Build_BaseModuleWf HWfBaseModule) (l := (getHidden m))) as P3; simpl in *.
  rewrite <- SameKeys_inlineAll_Meths in P3.
  apply (P3 P2); eauto.
Qed.

Lemma PSemAction_meth_collector_stitch f o readRegs1 newRegs1 calls1 calls2:
  PSemAction_meth_collector f o readRegs1 newRegs1 calls1 calls2 ->
  forall readRegs2 newRegs2 calls3 calls4,
    DisjKey newRegs1 newRegs2 ->
    PSemAction_meth_collector f o readRegs2 newRegs2 calls3 calls4 ->
    PSemAction_meth_collector f o (readRegs1++readRegs2) (newRegs1++newRegs2) (calls1++calls3) (calls2++calls4).
Proof.
  induction 1; simpl; auto; intros.
  rewrite H4.
  econstructor.
  - apply IHPSemAction_meth_collector; auto.
    + assert (DisjKey upds1 newRegs2) as P1;[|apply P1].
      rewrite H2 in H6; intro k; specialize (H6 k).
      clear - H6; rewrite map_app, in_app_iff in *; firstorder.
    + apply H7.
  - assert (DisjKey (upds1++newRegs2) upds2) as P1;[|apply P1].
    rewrite H2 in H6; intro k; specialize (H6 k); specialize (H0 k).
    clear - H0 H6; rewrite map_app, in_app_iff in *; firstorder.
  - rewrite H1; repeat rewrite <- app_assoc.
    apply Permutation_app_head, Permutation_app_comm.
  - rewrite H2; repeat rewrite <- app_assoc.
    apply Permutation_app_head, Permutation_app_comm.
  - rewrite H3; repeat rewrite <- app_assoc.
    apply Permutation_app_head, Permutation_app_comm.
  - simpl; reflexivity.
  - assumption.
Qed.

Lemma PSemAction_In_inline (f : DefMethT) o:
  forall {retK2} a readRegs newRegs calls (retV2 : type retK2),
    PSemAction o (inlineSingle f a) readRegs newRegs calls retV2 ->
    exists readRegs1 readRegs2 newRegs1 newRegs2 calls1 calls2 calls3,
      DisjKey newRegs1 newRegs2 /\
      readRegs [=] readRegs1++readRegs2 /\
      newRegs [=] newRegs1++newRegs2 /\
      calls [=] calls1++calls2 /\
      PSemAction_meth_collector f o readRegs1 newRegs1 calls1 calls3 /\
      PSemAction o a readRegs2 newRegs2 (calls3++calls2) retV2.
Proof.
  intros retK2 a.
  induction a; subst; simpl in *; intros.
  - destruct string_dec;[destruct Signature_dec|]; subst; simpl in *.
    + inv H0; EqDep_subst.
      inv HPSemAction; EqDep_subst.
      specialize (H _ _ _ _ _ HPSemActionCont); dest.
      exists (readRegs0++x), x0, (newRegs0++x1), x2, (calls0++x3), x4, (((fst f),(existT SignT (projT1 (snd f)) (evalExpr e, v)))::x5).
      repeat split; auto.
      * intro k; clear - H HDisjRegs H1; rewrite H1 in *;
          specialize (H k); specialize (HDisjRegs k).
        rewrite map_app, in_app_iff in *; firstorder.
      * clear -H0 HUReadRegs.
        rewrite H0, app_assoc in *; assumption.
      * clear -H1 HUNewRegs.
        rewrite H1, app_assoc in *; assumption.
      * clear -H2 HUCalls.
        rewrite H2, app_assoc in *; assumption.
      * econstructor 2.
        -- eapply H3.
        -- rewrite H1 in HDisjRegs.
           assert (DisjKey x1 newRegs0) as P1;
             [intro k; specialize (HDisjRegs k); rewrite map_app, in_app_iff in *;
              clear - HDisjRegs; firstorder| apply P1].
        -- apply Permutation_app_comm.
        -- apply Permutation_app_comm.
        -- apply Permutation_app_comm.
        -- reflexivity.
        -- assumption.
      * econstructor; eauto.
        simpl; reflexivity.
    + inv H0; EqDep_subst.
      specialize (H _ _ _ _ _ HPSemAction); dest.
      exists x, x0, x1, x2, x3, ((fst f, existT SignT s (evalExpr e, mret))::x4), x5.
      repeat split; auto.
      * rewrite Permutation_app_comm; simpl.
        rewrite H2 in HAcalls.
        rewrite HAcalls.
        constructor; apply Permutation_app_comm.
      * apply (PSemAction_rewrite_calls (Permutation_app_comm _ _)).
        apply (PSemAction_rewrite_calls (Permutation_app_comm _ _)) in H4; simpl in *.
        econstructor; eauto.
    + inv H0; EqDep_subst.
      specialize (H _ _ _ _ _ HPSemAction); dest.
      exists x, x0, x1, x2, x3, ((meth, existT SignT s (evalExpr e, mret)) ::x4), x5.
      repeat split; auto.
      * rewrite Permutation_app_comm; simpl; rewrite HAcalls.
        constructor; rewrite H2.
        apply Permutation_app_comm.
      * apply (PSemAction_rewrite_calls (Permutation_app_comm _ _)).
        apply (PSemAction_rewrite_calls (Permutation_app_comm _ _)) in H4; simpl in *.
        econstructor; eauto.
  - inv H0; EqDep_subst.
    specialize (H _ _ _ _ _ HPSemAction); dest.
    exists x, x0, x1, x2, x3, x4, x5; repeat split; auto.
    econstructor; eauto.
  - inv H0; EqDep_subst.
    specialize (H _ _ _ _ _ HPSemActionCont); dest.
    specialize (IHa _ _ _ _  HPSemAction); dest.
    exists (x++x6), (x0++x7), (x1++x8), (x2++x9), (x3++x10), (x4++x11), (x5++x12).
    repeat split; auto.
    + rewrite H7, H1 in HDisjRegs.
      clear - H H5 HDisjRegs.
      intro k; specialize (H k); specialize (H5 k); specialize (HDisjRegs k).
      repeat rewrite map_app, in_app_iff in *; firstorder.
    + rewrite HUReadRegs, H6, H0; simpl.
      rewrite Permutation_app_comm.
      repeat rewrite app_assoc.
      apply Permutation_app_tail.
      repeat rewrite <- app_assoc.
      apply Permutation_app_head.
      apply Permutation_app_comm.
    + rewrite HUNewRegs, H7, H1.
      rewrite Permutation_app_comm.
      repeat rewrite app_assoc.
      apply Permutation_app_tail.
      repeat rewrite <- app_assoc.
      apply Permutation_app_head.
      apply Permutation_app_comm.
    + rewrite HUCalls, H8, H2.
      rewrite Permutation_app_comm.
      repeat rewrite app_assoc.
      apply Permutation_app_tail.
      repeat rewrite <- app_assoc.
      apply Permutation_app_head.
      apply Permutation_app_comm.
    + eapply PSemAction_meth_collector_stitch; eauto.
      rewrite H7, H1 in HDisjRegs.
      intro k0; specialize (HDisjRegs k0); clear - HDisjRegs.
      repeat rewrite map_app, in_app_iff in *.
      firstorder.
    + econstructor.
      * assert (DisjKey x9 x2) as P1;[|apply P1].
        rewrite H7, H1 in HDisjRegs; clear -HDisjRegs; intro k; specialize (HDisjRegs k).
        repeat rewrite map_app, in_app_iff in *; firstorder.
      * apply H10.
      * apply Permutation_app_comm.
      * apply Permutation_app_comm.
      * assert ((x5 ++ x12) ++ x4 ++ x11 [=] (x12++x11)++(x4++x5)) as P1;[|apply P1].
        repeat rewrite <- app_assoc; rewrite Permutation_app_comm.
        repeat rewrite app_assoc.
        apply Permutation_app_tail.
        repeat rewrite <- app_assoc.
        apply Permutation_app_head, Permutation_app_comm.
      * apply (PSemAction_rewrite_calls (Permutation_app_comm _ _)); assumption.
  - inv H0; EqDep_subst.
    specialize (H _ _ _ _ _ HPSemAction); dest.
    exists x, x0, x1, x2, x3, x4, x5.
    repeat split; auto.
    econstructor; eauto.
  - inv H0; EqDep_subst.
    specialize (H _ _ _ _ _ HPSemAction); dest.
    exists x, ((r, existT (fullType type) k regV) ::x0), x1, x2, x3, x4, x5.
    repeat split; eauto.
    + rewrite HNewReads, H0; simpl; apply Permutation_middle.
    + econstructor; eauto.
  - inv H; EqDep_subst.
    specialize (IHa _ _ _ _ HPSemAction); dest.
    exists x, x0, x1, ((r, existT (fullType type) k (evalExpr e))::x2), x3, x4, x5.
    repeat split; eauto.
    + rewrite key_not_In_fst in HDisjRegs; rewrite H1, map_app, in_app_iff in HDisjRegs.
      clear - HDisjRegs H.
      intro k0; specialize (H k0); simpl.
      destruct (string_dec r k0); subst; simpl in *; firstorder.
    + rewrite HANewRegs, H1; simpl; apply Permutation_middle.
    + econstructor; auto.
      clear - H1 HDisjRegs.
      rewrite key_not_In_fst, H1, map_app, in_app_iff in *; firstorder.
  - inv H0; EqDep_subst.
    + specialize (IHa1 _ _ _ _ HAction); dest.
      specialize (H _ _ _ _ _ HPSemAction); dest.
      rewrite H2, H7 in HDisjRegs.
      exists (x++x6), (x0++x7), (x1++x8), (x2++x9), (x3++x10), (x4++x11), (x5++x12).
      repeat split; auto.
      * clear - HDisjRegs H0 H.
        intro k0; specialize (HDisjRegs k0); specialize (H0 k0); specialize (H k0).
        repeat rewrite map_app, in_app_iff in *; firstorder.
      * rewrite HUReadRegs, H1, H6.
        repeat rewrite app_assoc; apply Permutation_app_tail.
        repeat rewrite <- app_assoc; apply Permutation_app_head, Permutation_app_comm.
      * rewrite HUNewRegs, H2, H7.
        repeat rewrite app_assoc; apply Permutation_app_tail.
        repeat rewrite <- app_assoc; apply Permutation_app_head, Permutation_app_comm.
      * rewrite HUCalls, H3, H8.
        repeat rewrite app_assoc; apply Permutation_app_tail.
        repeat rewrite <- app_assoc; apply Permutation_app_head, Permutation_app_comm.
      * apply PSemAction_meth_collector_stitch; auto.
        clear - HDisjRegs.
        intro k; specialize (HDisjRegs k); repeat rewrite map_app, in_app_iff in *; firstorder.
      * econstructor.
        -- assert (DisjKey x2 x9) as P1;[|apply P1].
           clear - HDisjRegs; intro k; specialize (HDisjRegs k).
           repeat rewrite map_app, in_app_iff in *; firstorder.
        -- assumption.
        -- apply H5.
        -- apply H10.
        -- reflexivity.
        -- reflexivity.
        -- repeat rewrite <- app_assoc.
           apply Permutation_app_head.
           repeat rewrite app_assoc.
           apply Permutation_app_tail, Permutation_app_comm.
    + specialize (IHa2 _ _ _ _ HAction); dest.
      specialize (H _ _ _ _ _ HPSemAction); dest.
            rewrite H2, H7 in HDisjRegs.
      exists (x++x6), (x0++x7), (x1++x8), (x2++x9), (x3++x10), (x4++x11), (x5++x12).
      repeat split; auto.
      * clear - HDisjRegs H0 H.
        intro k0; specialize (HDisjRegs k0); specialize (H0 k0); specialize (H k0).
        repeat rewrite map_app, in_app_iff in *; firstorder.
      * rewrite HUReadRegs, H1, H6.
        repeat rewrite app_assoc; apply Permutation_app_tail.
        repeat rewrite <- app_assoc; apply Permutation_app_head, Permutation_app_comm.
      * rewrite HUNewRegs, H2, H7.
        repeat rewrite app_assoc; apply Permutation_app_tail.
        repeat rewrite <- app_assoc; apply Permutation_app_head, Permutation_app_comm.
      * rewrite HUCalls, H3, H8.
        repeat rewrite app_assoc; apply Permutation_app_tail.
        repeat rewrite <- app_assoc; apply Permutation_app_head, Permutation_app_comm.
      * apply PSemAction_meth_collector_stitch; auto.
        clear - HDisjRegs.
        intro k; specialize (HDisjRegs k); repeat rewrite map_app, in_app_iff in *; firstorder.
      * econstructor 8.
        -- assert (DisjKey x2 x9) as P1;[|apply P1].
           clear - HDisjRegs; intro k; specialize (HDisjRegs k).
           repeat rewrite map_app, in_app_iff in *; firstorder.
        -- assumption.
        -- apply H5.
        -- apply H10.
        -- reflexivity.
        -- reflexivity.
        -- repeat rewrite <- app_assoc.
           apply Permutation_app_head.
           repeat rewrite app_assoc.
           apply Permutation_app_tail, Permutation_app_comm.
  - inv H; EqDep_subst.
    specialize (IHa _ _ _ _ HPSemAction); dest.
    exists x, x0, x1, x2, x3, x4, x5; repeat split; auto.
    econstructor; eauto.
  - inv H; EqDep_subst.
    exists nil, nil, nil, nil, nil, nil, nil; simpl; repeat split; auto.
    + intro; simpl; tauto.
    + constructor.
    + constructor; auto.
Qed.

Lemma inlineSingle_Rule_in_list_notKey rn0 rn rb f l:
  rn <> rn0 ->
  In (rn0, rb) (inlineSingle_Rule_in_list f rn l) ->
  In (rn0, rb) l.
Proof.
  induction l; intros; simpl in *; auto.
  destruct string_dec, a; simpl in *; subst.
  - destruct H0.
    + inversion H0;contradiction.
    + right; apply IHl; auto.
  - destruct H0; auto.
Qed.

Lemma PPlusSubsteps_PPlusSubsteps_inline_Rule_NoExec f m o rn upds execs calls :
  NoDup (map fst (getRules m)) ->
  ~In (Rle rn) execs ->
  PPlusSubsteps (inlineSingle_Rule_BaseModule f rn m) o upds execs calls ->
  PPlusSubsteps m o upds execs calls.
Proof.
  induction 3; simpl in *.
  - econstructor 1; eauto.
  - rewrite HUpds, HExecs, HCalls.
    econstructor 2; eauto.
    + assert (rn <> rn0);[intro; subst; apply H0; rewrite HExecs; left; reflexivity|].
      eapply inlineSingle_Rule_in_list_notKey; eauto.
    + apply IHPPlusSubsteps.
      intro; apply H0; rewrite HExecs; right; auto.
  - rewrite HUpds, HExecs, HCalls.
    econstructor 3; eauto.
    apply IHPPlusSubsteps.
    intro; apply H0; rewrite HExecs; right; auto.
Qed.

Lemma Rle_injective rn rn0 :
  Rle rn = Rle rn0 <-> rn = rn0.
Proof.
  split; intro; subst; auto; inv H; auto.
Qed.

Lemma PPlus_inlineSingle_BaseModule_with_action f m o rn rb upds execs calls:
  PPlusSubsteps (inlineSingle_Rule_BaseModule f rn m) o upds ((Rle rn)::execs) calls ->
  In (rn, rb) (getRules m) ->
  In f (getMethods m) ->
  NoDup (map fst (getMethods m)) ->
  NoDup (map fst (getRules m)) ->
  exists upds1 upds2 calls1 calls2 reads,
    upds [=] upds1++upds2 /\
    calls [=] calls1++calls2 /\
    DisjKey upds2 upds1 /\
    SubList (getKindAttr reads) (getKindAttr (getRegisters m)) /\
    SubList (getKindAttr upds1) (getKindAttr (getRegisters m)) /\
    PSemAction o (inlineSingle f (rb type)) reads upds1 calls1 WO /\
    PPlusSubsteps m o upds2 execs calls2.
Proof.
  intros.
  rewrite (inlineSingle_Rule_preserves_names f rn) in H3.
  apply (inlineSingle_Rule_BaseModule_dec2 f) in H0; dest.
  eapply (ExtractRuleAction) in H; simpl in *; eauto; dest.
  simpl in *.
  exists x1, x2, x3, x4, x; repeat split; auto.
  - rewrite shatter_word_0 in H; assumption.
  - apply Permutation_cons_inv in H9.
    rewrite H9.
    rewrite <- (inlineSingle_Rule_preserves_names) in H3.
    apply (PPlusSubsteps_PPlusSubsteps_inline_Rule_NoExec (rn:=rn)(f:=f)); auto.
Qed.

Lemma place_execs_PPlus f m o reads upds1 calls1 fcalls :
  PSemAction_meth_collector f o reads upds1 calls1 fcalls ->
  NoDup (map fst (getMethods m)) ->
  In f (getMethods m) ->
  SubList (getKindAttr upds1) (getKindAttr (getRegisters m)) ->
  SubList (getKindAttr reads) (getKindAttr (getRegisters m)) ->
  forall upds2 execs calls2,
  DisjKey upds1 upds2 ->
  PPlusSubsteps m o upds2 execs calls2 ->
  PPlusSubsteps m o (upds1++upds2) ((map Meth fcalls) ++ execs) (calls1++calls2).
Proof.
  induction 1; simpl in *; auto.
  intros; destruct f; simpl in *.
  assert (upds ++ upds0 [=] upds2 ++ (upds1++upds0)) as P1;
    [rewrite H2, app_assoc; apply Permutation_app_tail, Permutation_app_comm
    |rewrite P1; clear P1].
  assert (calls ++ calls0 [=] calls2 ++ (calls1++calls0)) as P1;
    [rewrite H3, app_assoc; apply Permutation_app_tail, Permutation_app_comm
    |rewrite P1; clear P1].
  rewrite H4; simpl.
  assert (SubList (getKindAttr upds1) (getKindAttr (getRegisters m))) as P2;
    [repeat intro; apply H8; rewrite H2, map_app, in_app_iff; left; auto|].
  assert (SubList (getKindAttr reads1) (getKindAttr (getRegisters m))) as P3;
    [repeat intro; apply H9; rewrite H1, map_app, in_app_iff; left; auto|].
  assert (DisjKey upds1 upds0) as P4;
    [intro k; specialize (H10 k); rewrite H2, map_app, in_app_iff in H10;
     clear - H10; firstorder|].
  specialize (IHPSemAction_meth_collector H6 H7 P2 P3 _ _ _ P4 H11).
  econstructor 3; eauto.
  - inv H11; auto.
  - repeat intro; apply H9.
    rewrite H1, map_app, in_app_iff; auto.
  - repeat intro; apply H8.
    rewrite H2, map_app, in_app_iff; auto.
  - rewrite H2 in H10.
    clear - H0 H10.
    intro k; specialize (H0 k); specialize (H10 k).
    rewrite map_app, in_app_iff in *; firstorder.
Qed.

Lemma MatchingExecCalls_Base_add_fcalls m calls fcalls execs :
  MatchingExecCalls_flat calls execs m ->
  MatchingExecCalls_flat (fcalls++calls) ((map Meth fcalls)++execs) m.
Proof.
  induction fcalls; simpl; auto; intros.
  specialize (IHfcalls H); clear H.
  unfold MatchingExecCalls_flat in *; intros; specialize (IHfcalls _ H).
  destruct (MethT_dec f a);[rewrite getNumFromCalls_eq_cons, getNumFromExecs_eq_cons
                           |rewrite getNumFromCalls_neq_cons, getNumFromExecs_neq_cons]; auto.
  omega.
Qed.

Lemma InRule_In_inlined_neq2 f rn1 rn2 rb m:
  rn1 <> rn2 ->
  In (rn2, rb) (getRules (inlineSingle_Rule_BaseModule f rn1 m)) ->
  In (rn2, rb) (getRules m).
Proof.
  simpl.
  apply inlineSingle_Rule_in_list_notKey.
Qed.

Lemma PPlusStep_NotIn_inline_Rule f m o rn upds execs calls :
  NoDup (map fst (getRules m)) ->
  In f (getMethods m) ->
  ~In (Rle rn) execs ->
  PPlusStep (inlineSingle_Rule_BaseModule f rn m) o upds execs calls ->
  PPlusStep m o upds execs calls.
Proof.
  induction 4; econstructor.
  - induction H2.
    + econstructor 1; auto.
    + rewrite HUpds, HExecs, HCalls.
      econstructor 2; eauto.
      * eapply InRule_In_inlined_neq2; eauto.
        intro; subst; apply H1; rewrite HExecs; left; reflexivity.
      * eapply PPlusSubsteps_PPlusSubsteps_inline_Rule_NoExec; eauto.
        intro; apply H1; rewrite HExecs; right; assumption.
    + rewrite HUpds, HExecs, HCalls.
      econstructor 3; eauto.
      eapply PPlusSubsteps_PPlusSubsteps_inline_Rule_NoExec; eauto.
      intro; apply H1; rewrite HExecs; right; assumption.
  - intros g P1.
    apply H3; simpl; auto.
Qed.

Lemma PPlusSubsteps_undef_inline_Rule f m o rn upds execs calls:
  ~In rn (map fst (getRules m)) ->
  PPlusSubsteps (inlineSingle_Rule_BaseModule f rn m) o upds execs calls ->
  PPlusSubsteps m o upds execs calls.
Proof.
  induction 2.
  - econstructor 1; eauto.
  - econstructor 2; eauto.
    apply InRule_In_inlined_neq2 in HInRules; auto.
    apply (in_map fst) in HInRules; simpl in *.
    rewrite <-inlineSingle_Rule_preserves_names in HInRules.
    intro; subst; contradiction.
  - econstructor 3; eauto.
Qed.

Lemma PPlusStep_undef_inline_Rule f m o rn upds execs calls:
  ~In rn (map fst (getRules m)) ->
  PPlusStep (inlineSingle_Rule_BaseModule f rn m) o upds execs calls ->
  PPlusStep m o upds execs calls.
Proof.
  induction 2.
  econstructor.
  - eapply PPlusSubsteps_undef_inline_Rule; eauto.
  - apply H1.
Qed.

Lemma PPlusTrace_undef_inline_Rule f m rn l:
  ~In rn (map fst (getRules m)) ->
  forall o,
  PPlusTrace (inlineSingle_Rule_BaseModule f rn m) o l ->
  PPlusTrace m o l.
Proof.
  induction l; subst.
  - intros; inv H0; simpl in *.
    + econstructor 1; eauto.
    + discriminate.
  - intros.
    inv H0;[discriminate|].
    inv HPPlusTrace.
    econstructor 2; eauto.
    eapply PPlusStep_undef_inline_Rule; eauto.
Qed.

Lemma PPlusStep_In_inline_Rule f m o rn upds execs calls:
  In rn (map fst (getRules m)) ->
  In f (getMethods m) ->
  NoDup (map fst (getRules m)) ->
  NoDup (map fst (getMethods m)) ->
  In (Rle rn) execs ->
  PPlusStep (inlineSingle_Rule_BaseModule f rn m) o upds execs calls ->
  exists fcalls,
    PPlusStep m o upds ((map Meth fcalls)++execs) (fcalls++calls).
Proof.
  induction 6.
  rewrite in_map_iff in H; destruct H as [x TMP]; destruct TMP as [fst_eq H]; destruct x; subst.
  specialize (in_split _ _ H3) as P1; dest.
  assert (execs [=] (Rle s)::(x++x0)) as P1;[rewrite H6; rewrite Permutation_middle; reflexivity
                                             | rewrite P1 in *].
  specialize (PPlus_inlineSingle_BaseModule_with_action _ H4 H H0 H2 H1) as P2; dest.
  specialize (PSemAction_In_inline _ _ H12) as P2; dest.
  exists x12.
  econstructor.
  - assert (SubList (getKindAttr x6) (getKindAttr (getRegisters m))) as P2;
      [repeat intro; apply H10; rewrite H15, map_app, in_app_iff; auto|].
    assert (SubList (getKindAttr x8) (getKindAttr (getRegisters m))) as P3;
      [repeat intro; apply H11; rewrite H16, map_app, in_app_iff; auto|].
    assert (DisjKey x8 x2) as P4;
      [rewrite H16 in H9; clear - H9; intro k; specialize (H9 k);
       rewrite map_app, in_app_iff in *; firstorder|].
    specialize (place_execs_PPlus H18 H2 H0 P3 P2 P4 H13) as P5.
    assert (map Meth x12 ++ execs [=] ((Rle s)::(map Meth x12 ++ x ++ x0))) as TMP;
      [simpl; rewrite P1; repeat rewrite Permutation_middle; apply Permutation_app_tail; auto
      |rewrite TMP; clear TMP].
    assert (x12++calls [=] ((x12++x11)++(x10++x4))) as TMP;
      [rewrite H8, <- app_assoc; apply Permutation_app_head; rewrite app_assoc;
       apply Permutation_app_tail; rewrite H17; apply Permutation_app_comm
      |rewrite TMP; clear TMP].
    assert (upds [=] (x9 ++(x8++x2))) as TMP;
      [rewrite H7, H16, app_assoc; apply Permutation_app_tail, Permutation_app_comm
      |rewrite TMP; clear TMP].
    econstructor 2; eauto.
    + inv P5; auto.
    + repeat intro; apply H10; rewrite H15, map_app, in_app_iff; auto.
    + repeat intro; apply H11; rewrite H16, map_app, in_app_iff; auto.
    + rewrite H16 in H9; clear - H9 H14.
      intro k; specialize (H9 k); specialize (H14 k); rewrite map_app, in_app_iff in *;
        firstorder.
    + assert (NoDup (map fst (getRules (inlineSingle_Rule_BaseModule f s m)))) as P6;
        [simpl; rewrite <-inlineSingle_Rule_preserves_names; auto|].
      assert (NoDup (map fst (getMethods (inlineSingle_Rule_BaseModule f s m)))) as P7;
        [auto|].
      assert ((Rle s :: x ++ x0) [=] ([Rle s]++(x++x0))) as TMP;
        [auto|rewrite TMP in H4; clear TMP].
      specialize (PPlusSubsteps_split_execs_OneRle P7 P6 _ _ H4).
      intros.
      rewrite in_app_iff in H21.
      destruct H21.
      * clear - H21.
        induction x12; simpl in *;[contradiction|destruct H21; subst; auto; apply IHx12; auto].
      * assert (In (Rle s) [Rle s]) as P8;[left; reflexivity|].
        specialize (H20 _ _ P8 H21); simpl in *;  assumption.
  - apply MatchingExecCalls_Base_add_fcalls.
    intros f0 P2.
    apply H5; auto.
Qed.

Lemma PPlusStrongTraceInclusion_inlining_Rules_l m f rn :
  In f (getMethods m) ->
  (WfMod (Base m)) ->
  StrongPPlusTraceInclusion (inlineSingle_Rule_BaseModule f rn m) m.
Proof.
  unfold StrongPPlusTraceInclusion; induction 3; subst.
  - exists nil; split.
    + econstructor; eauto.
    + constructor.
  - dest.
    pose proof H0 as sth.
    specialize (H0).
      destruct (in_dec (RuleOrMeth_dec) (Rle rn) execs),(in_dec string_dec rn (map fst (getRules m))); inv H0.
    * destruct HWfBaseModule as [? [? [NoDupMeths [NoDupRegisters NoDupRle]]]].
      specialize (PPlusStep_In_inline_Rule i0 H NoDupRle NoDupMeths i HPPlusStep) as TMP; dest.
      exists ((upds, ((map Meth x0 ++ execs), (x0++calls)))::x); split.
      -- econstructor 2; eauto.
      -- constructor; auto.
         unfold WeakInclusion_flat, getListFullLabel_diff_flat.
         split; intros; simpl.
         ++ symmetry; rewrite getNumFromExecs_app, getNumFromCalls_app, (call_execs_counts_eq);
            omega.
         ++ simpl in *.
            destruct H6; exists x1; rewrite in_app_iff in *.
            destruct H6; auto.
            exfalso; clear -H6; induction x0; simpl in *; eauto.
            destruct H6;[discriminate|auto].
    * exists ((upds, (execs, calls))::x); split.
      -- econstructor 2; eauto.
         eapply PPlusStep_undef_inline_Rule; eauto.
      -- econstructor; eauto.
         unfold WeakInclusion_flat; split; intros; auto.
    * exists ((upds, (execs, calls))::x); split.
      -- econstructor 2; eauto.
         eapply PPlusStep_NotIn_inline_Rule; eauto.
         inv HWfBaseModule; dest; auto.
      -- econstructor; eauto.
         unfold WeakInclusion_flat; split; intros; auto.
    * exists ((upds, (execs, calls))::x); split.
      -- econstructor 2; eauto.
         eapply (PPlusStep_NotIn_inline_Rule); eauto.
         inv HWfBaseModule; dest; auto.
      -- econstructor; eauto.
         unfold WeakInclusion_flat; split; intros; auto.
Qed.

Theorem TraceInclusion_inlining_Rules_l m f rn:
  In f (getMethods m) ->
  WfMod m ->
  TraceInclusion (inlineSingle_Rule_BaseModule f rn m) m.
Proof.
  intros.
  apply PPlusTraceInclusion_TraceInclusion; auto.
  - apply WfMod_Rule_inlined; auto.
  - apply StrongPPlusTraceInclusion_PPlusTraceInclusion.
    apply PPlusStrongTraceInclusion_inlining_Rules_l; auto.
Qed.

Theorem TraceInclusion_inlining_Rules_Wf_l {f} {m : BaseModuleWf} rn
        (inMeths: In f (getMethods m)):
  TraceInclusion (inlineSingle_Rule_BaseModuleWf rn inMeths) m.
Proof.
  simpl; apply TraceInclusion_inlining_Rules_l; eauto.
  constructor; apply wfBaseModule.
Qed.

Lemma inlineSingle_Meth_in_list_body fb f gn l:
  (fst f) <> gn->
  In (gn, fb) (inlineSingle_Meth_in_list f gn l) ->
  exists (fb' : {x : Signature & MethodT x}),
    (fb = existT
         (fun sig : Signature => forall ty : Kind -> Type, ty (fst sig) -> ActionT ty (snd sig))
         (projT1 fb') (fun (ty : Kind -> Type) (X : ty (fst (projT1 fb'))) => inlineSingle f ((projT2 fb') ty X))) /\
    In (gn, fb') l.
Proof.
  intros.
  induction l;[contradiction| destruct a].
  simpl in H0; destruct string_dec.
  - destruct H0; subst; auto.
    + exists s0; simpl.
      destruct string_dec;[contradiction|simpl in *; inversion H0].
      destruct fb; inv H0.
      split; auto.
      destruct s0; simpl in *; reflexivity.
    + specialize (IHl H0); dest.
      exists x; split; auto.
      right; assumption.
  - destruct H0;[exfalso;inv H0;apply n; reflexivity|auto].
    specialize (IHl H0); dest.
    exists x; split; auto.
    right; assumption.
Qed.

Lemma PPlus_uninline_meths f gn m o:
  (fst f) <> gn ->
  NoDup (map fst (getMethods m)) ->
  forall gexecs,
    (forall g, In g gexecs -> (fst g = gn)) ->
    forall upds calls,
      PPlusSubsteps (inlineSingle_Meth_BaseModule f gn m) o upds (map Meth gexecs) calls ->
      exists upds1 upds2 calls1 calls2 fcalls reads,
        upds [=] upds1++upds2 /\
        calls [=] calls1++calls2 /\
        DisjKey upds2 upds1 /\
        SubList (getKindAttr reads) (getKindAttr (getRegisters m)) /\
        SubList (getKindAttr upds1) (getKindAttr (getRegisters m)) /\
        PPlusSubsteps m o upds2 (map Meth gexecs) (fcalls++calls2) /\
        PSemAction_meth_collector f o reads upds1 calls1 fcalls.
Proof.
  induction gexecs.
  intros; inv H2.
  - exists nil, nil, nil, nil, nil, nil; simpl; repeat split; auto.
    + intro; simpl; auto.
    + repeat intro; simpl in *; contradiction.
    + repeat intro; simpl in *; contradiction.
    + constructor; auto.
    + constructor.
  - exfalso; simpl in *.
    apply Permutation_nil in HExecs.
    discriminate.
  - exfalso; simpl in *.
    apply Permutation_nil in HExecs.
    discriminate.
  - simpl in *; intros.
    inv H2.
    + exfalso.
      subst.
      specialize (in_eq (Rle rn) (oldExecs)) as P1; rewrite <-HExecs in P1.
      clear - P1; simpl in *.
      destruct P1;[discriminate|].
      induction gexecs; simpl in *; auto.
      destruct H;[discriminate|auto].
    + assert ((fn, existT _ (projT1 fb) (argV, retV)) = a \/
              In (fn, existT _ (projT1 fb) (argV, retV)) gexecs) as P1;
        [specialize (in_eq (Meth (fn, existT _ (projT1 fb) (argV, retV))) oldExecs)  as TMP;
         rewrite <- HExecs in TMP; destruct TMP as [TMP|TMP];
         [inversion TMP; auto| rewrite in_map_iff in TMP; dest; inversion H2; subst; auto]|].
      assert (forall g, In g gexecs -> fst g = gn) as P2;[intros; apply H1; auto|].
      destruct P1 as [P1|P1].
      * subst.
        apply Permutation_cons_inv in HExecs.
        rewrite <- HExecs in HPSubstep.
        specialize (IHgexecs P2 _ _ HPSubstep); dest.
        simpl in *.
        assert (fn = gn);[clear - H1; specialize (H1 _ (or_introl eq_refl)); auto|subst].
        specialize (inlineSingle_Meth_in_list_body _ _ _ H HInMeths) as TMP; dest.
        destruct fb; inv H9; EqDep_subst; simpl in *.
        apply PSemAction_In_inline in HPAction; dest.
        exists (x++x8), (x9++x0), (x1++x10), (x2++x11), (x3++x12), (x4++x6).
        repeat split.
        -- rewrite HUpds, H2, H12; repeat rewrite app_assoc.
           apply Permutation_app_tail; rewrite Permutation_app_comm, app_assoc; reflexivity.
        -- rewrite HCalls, H3, H13, app_assoc; rewrite Permutation_app_comm.
           symmetry; rewrite Permutation_app_comm, <-app_assoc.
           apply Permutation_app_head.
           rewrite <-app_assoc, Permutation_app_comm, <-app_assoc,
           Permutation_app_comm, app_assoc.
           reflexivity.
        -- rewrite H2, H12 in HDisjRegs; intro k; specialize (HDisjRegs k);
             specialize (H9 k); specialize (H4 k); clear - HDisjRegs H9 H4.
           repeat rewrite map_app, in_app_iff in *; firstorder.
        -- rewrite H11, map_app in *; clear - HReadsGood H5; rewrite SubList_app_l_iff in *;
            firstorder.
        -- rewrite H12, map_app in *; clear - HUpdGood H6; rewrite SubList_app_l_iff in *;
             firstorder.
        -- assert ((x3++x12)++x2++x11 [=] (x12++x11)++(x3++x2)) as P3;
             [rewrite Permutation_app_comm, <-app_assoc; symmetry;
              rewrite app_assoc, Permutation_app_comm; apply Permutation_app_head;
              rewrite <-app_assoc; symmetry; rewrite app_assoc, Permutation_app_comm;
              reflexivity|rewrite P3].
           econstructor 3; eauto.
           ++ rewrite H11 in HReadsGood; clear - HReadsGood; rewrite map_app, SubList_app_l_iff in *; firstorder.
           ++ rewrite H12 in HUpdGood; clear - HUpdGood; rewrite map_app, SubList_app_l_iff in *; firstorder.
           ++ rewrite H12, H2 in HDisjRegs; intro k; clear - HDisjRegs H9 H4;
                specialize (HDisjRegs k); specialize (H9 k); specialize (H4 k).
              repeat rewrite map_app, in_app_iff in *; firstorder.
        -- apply PSemAction_meth_collector_stitch; auto.
           rewrite H12, H2 in HDisjRegs; intro k; clear - HDisjRegs H9 H4;
             specialize (HDisjRegs k); specialize (H9 k); specialize (H4 k);
               repeat rewrite map_app, in_app_iff in *; firstorder.
      * specialize (in_split _ _ P1) as TMP; destruct TMP as [l1 [l2 TMP]].
        rewrite TMP, map_app, Permutation_middle in HExecs; simpl in HExecs.
        rewrite perm_swap, Permutation_app_comm, <-app_comm_cons in HExecs.
        apply Permutation_cons_inv in HExecs.
        rewrite <-app_comm_cons, Permutation_app_comm in HExecs.
        rewrite <- HExecs in HPSubstep.
        destruct a.
        assert (NoDup (map fst (getMethods (inlineSingle_Meth_BaseModule f gn m)))) as P3;
          [simpl; rewrite SameKeys_inline_Meth; auto|].
        specialize (H1 _ (or_introl eq_refl)) as TMP2; simpl in TMP2; rewrite TMP2 in *; clear TMP2.
        assert (fn = gn) as TMP2; [specialize (H1 _ (or_intror P1));
                                   assumption|rewrite TMP2 in *; clear TMP2].
        specialize (extract_exec_PPlus _ P3 HInMeths HPSubstep) as TMP2; dest;
          rewrite H2 in *; clear H2.
        assert (DisjKey x1 u) as P4;
          [rewrite H4 in HDisjRegs; clear - HDisjRegs H6;
           intro k; specialize (HDisjRegs k); specialize (H6 k);
           rewrite map_app, in_app_iff in *; firstorder
          |].
        specialize (PPlusAddMeth HRegs _ HInMeths HPAction HReadsGood HUpdGood
                                 (Permutation_refl _) (Permutation_refl _) (Permutation_refl _)
                                 P4 H9) as P5.
        rewrite Permutation_middle in P5.
        rewrite TMP, map_app in IHgexecs; rewrite TMP in P2; simpl in IHgexecs.
        specialize (IHgexecs P2 _ _ P5); dest.
        specialize (inlineSingle_Meth_in_list_body _ _ _ H HInMeths) as TMP2; dest; subst;
          simpl in *.
        apply (PSemAction_In_inline) in H3; dest.
        exists (x6++x15), (x16++x7), (x8++x17), (x18++x9), (x10++x19), (x11++x13); repeat split.
        --  rewrite HUpds, H4, H18, Permutation_app_comm, <-app_assoc.
            rewrite Permutation_app_comm in H2; rewrite H2; repeat rewrite app_assoc.
            apply Permutation_app_tail.
            rewrite Permutation_app_comm, <-app_assoc; reflexivity.
        -- rewrite HCalls, H5, H19, Permutation_app_comm, <-app_assoc.
           rewrite Permutation_app_comm in H10; rewrite H10; repeat rewrite app_assoc.
           apply Permutation_app_tail.
           rewrite Permutation_app_comm, <-app_assoc; reflexivity.
        -- intro k; specialize (H6 k); specialize (H3 k); specialize (HDisjRegs k);
             specialize (H11 k).
           rewrite H4, H18 in HDisjRegs. rewrite H18 in H6.
           clear - H2 H10 H11 HDisjRegs H3 H6.
           repeat rewrite map_app, in_app_iff in *.
           firstorder.
           ++ assert (~In k (map fst (x6++x7)));[rewrite <-H2, map_app, in_app_iff;firstorder
                                                |rewrite map_app, in_app_iff in *].
              firstorder.
           ++ assert (~In k (map fst (x6++x7)));[rewrite <-H2, map_app, in_app_iff;firstorder
                                                |rewrite map_app, in_app_iff in *].
              firstorder.
        -- rewrite H16, map_app, SubList_app_l_iff in *; clear - H8 H12; firstorder.
        -- rewrite H18, map_app, SubList_app_l_iff in *; clear - H7 H13; firstorder.
        -- econstructor 3; eauto.
           ++ rewrite H16, map_app, SubList_app_l_iff in *; clear - H8; dest; auto.
           ++ rewrite H18, map_app, SubList_app_l_iff in *; clear - H7; dest; auto.
           ++ repeat rewrite <-app_assoc; rewrite Permutation_app_comm, <-app_assoc.
              apply Permutation_app_head.
              rewrite <-app_assoc; apply Permutation_app_head, Permutation_app_comm.
           ++ rewrite H4, H18 in HDisjRegs; rewrite H18 in H6.
              clear - H6 H3 HDisjRegs H11 H2.
              intro k; specialize (H6 k); specialize (H3 k); specialize (HDisjRegs k);
                specialize (H11 k).
              repeat rewrite map_app, in_app_iff in *.
              firstorder.
              ** assert (~In k (map fst (x6++x7)));[rewrite <-H2, map_app, in_app_iff;firstorder
                                                |rewrite map_app, in_app_iff in *].
                 firstorder.
           ++ rewrite map_app; simpl; auto.
        -- apply PSemAction_meth_collector_stitch; auto.
           ++ rewrite H4, H18 in HDisjRegs; rewrite H18 in H6.
              clear - H6 H3 HDisjRegs H11 H2.
              intro k; specialize (H6 k); specialize (H3 k); specialize (HDisjRegs k);
                specialize (H11 k).
              repeat rewrite map_app, in_app_iff in *.
              firstorder.
              ** assert (~In k (map fst (x6++x7)));[rewrite <-H2, map_app, in_app_iff;firstorder
                                                |rewrite map_app, in_app_iff in *].
                 firstorder.
Qed.

Corollary PPlus_uninline_meths2 f gn m o:
  In f (getMethods m) ->
  (fst f) <> gn ->
  NoDup (map fst (getMethods m)) ->
  forall gexecs,
    (forall g, In g gexecs -> (fst g = gn)) ->
    forall upds calls,
      PPlusSubsteps (inlineSingle_Meth_BaseModule f gn m) o upds (map Meth gexecs) calls ->
      exists fcalls,
        PPlusSubsteps m o upds (map Meth (fcalls++gexecs)) (fcalls++calls).
Proof.
  intros.
  apply PPlus_uninline_meths in H3; auto; dest.
  apply DisjKey_Commutative in H5.
  exists x3; rewrite map_app.
  specialize (place_execs_PPlus H9 H1 H H7 H6 H5 H8) as P1.
  rewrite H3, H4.
  assert (x3++x1++x2 [=] x1++x3++x2) as TMP;
    [repeat rewrite app_assoc; apply Permutation_app_tail, Permutation_app_comm
    |rewrite TMP; clear TMP].
  assumption.
Qed.
  
Lemma key_neq_inlineSingle_Meth fn fb f gn l:
  fn <> gn ->
  In (fn, fb) (inlineSingle_Meth_in_list f gn l) ->
  In (fn, fb) l.
Proof.
  intros;induction l; simpl in *; auto.
  destruct string_dec.
  - destruct H0, a; simpl in *; subst; auto.
    exfalso; inv H0; apply H; reflexivity.
  - destruct H0; auto.
Qed.
      
Lemma PPlusSubsteps_NoExec_PPlusSubsteps_inline_Meth f m o gn upds execs calls :
  NoDup (map fst (getMethods m)) ->
  In f (getMethods m) ->
  (forall g,  In (Meth g) execs -> fst g <> gn) ->
  PPlusSubsteps (inlineSingle_Meth_BaseModule f gn m) o upds execs calls ->
  PPlusSubsteps m o upds execs calls.
Proof.
  induction 4.
  - econstructor 1; eauto.
  - rewrite HUpds, HExecs, HCalls.
    econstructor 2; eauto.
    apply IHPPlusSubsteps; repeat intro.
    eapply H1; eauto; rewrite HExecs; right; auto.
  - rewrite HUpds, HExecs, HCalls.
    econstructor 3; eauto.
    + simpl in HInMeths.
      eapply key_neq_inlineSingle_Meth; eauto.
      intro; subst.
      eapply H1; eauto;[rewrite HExecs; left; reflexivity|];auto.
    + apply IHPPlusSubsteps; repeat intro.
      eapply H1;[rewrite HExecs; right|]; eauto.
Qed.

Lemma PPlusSubsteps_split  m o execs1:
  forall execs2 upds calls,
    NoDup (map fst (getMethods m)) ->
    NoDup (map fst (getRules m)) ->
    PPlusSubsteps m o upds (execs1++execs2) calls ->
    exists upds1 upds2 calls1 calls2,
      DisjKey upds1 upds2 /\
      upds [=] upds1++upds2 /\
      calls [=] calls1++calls2 /\
      PPlusSubsteps m o upds1 execs1 calls1 /\
      PPlusSubsteps m o upds2 execs2 calls2.
Proof.
  induction execs1; intros; simpl in *.
  - exists nil, upds, nil, calls.
    repeat split; auto.
    + intro; simpl; auto.
    + econstructor; inv H1; auto.
  - destruct a.
    + specialize (PPlusSubsteps_exec_Rule_defined _ (in_eq (Rle rn) (execs1++execs2)) H1) as TMP;
        dest.
      specialize (ExtractRuleAction _ H0 H2 (in_eq (Rle rn) (execs1++execs2)) H1) as TMP; dest.
      simpl in *; apply Permutation_cons_inv in H9; rewrite <-H9 in H11.
      specialize (IHexecs1 _ _ _ H H0 H11); dest.
      exists (x2++x7), x8, (x4++x9), x10.
      repeat split.
      * rewrite H13 in H6; intro; clear - H6 H12.
        specialize (H12 k); specialize (H6 k).
        rewrite map_app, in_app_iff in *; firstorder.
      * rewrite H4, H13, app_assoc; reflexivity.
      * rewrite H5, H14, app_assoc; reflexivity.
      * econstructor 2; auto.
        -- inv H11; auto.
        -- apply H2.
        -- rewrite shatter_word_0 in H3; apply H3.
        -- assumption.
        -- assumption.
        -- rewrite H13 in H6; clear - H6; intro k.
           specialize (H6 k); rewrite map_app, in_app_iff in *; firstorder.
        -- setoid_rewrite <- H9 in H10.
           intro; destruct x11; auto.
           intro; eapply H10; rewrite in_app_iff; left; apply H17.
      * apply H16.
    + destruct f.
      specialize (PPlusSubsteps_exec_Meth_defined _ _ (in_eq (Meth (s, s0)) (execs1++execs2)) H1)as TMP; dest.
      specialize (extract_exec_PPlus _ H H2 H1) as TMP; dest; subst; simpl in *.
      specialize (IHexecs1 _ _ _ H H0 H10); dest.
      exists (x1++x7), x8, (x3++x9), x10.
      repeat split; auto.
      * rewrite H11 in H7; intro k; clear - H7 H3.
        specialize (H3 k); specialize (H7 k); rewrite map_app, in_app_iff in *; firstorder.
      * rewrite H5, H11, app_assoc; reflexivity.
      * rewrite H6, H12, app_assoc; reflexivity.
      * econstructor 3.
        -- inv H10; eauto.
        -- apply H2.
        -- apply H4.
        -- assumption.
        -- assumption.
        -- reflexivity.
        -- reflexivity.
        -- reflexivity.
        -- rewrite H11 in H7.
           intro k; specialize (H7 k); clear - H7; rewrite map_app, in_app_iff in *.
           firstorder.
        -- assumption.
Qed.

Lemma PPlusSubsteps_PPlusSubsteps_inline_Meth_NotDef f gn m o:
  forall execs upds calls,
    ~In gn (map fst (getMethods m)) ->
    PPlusSubsteps (inlineSingle_Meth_BaseModule f gn m) o upds execs calls ->
    PPlusSubsteps m o upds execs calls.
Proof.
  induction 2.
  - econstructor 1; eauto.
  - rewrite HUpds, HExecs, HCalls.
    econstructor 2; eauto.
  - rewrite HUpds, HExecs, HCalls.
    econstructor 3; eauto.
    simpl in HInMeths.
    rewrite <-Method_list_invariance in HInMeths; auto.
Qed.

Definition gexecs (gn : string) (exec : RuleOrMeth) : bool :=
  match exec with
  | Rle _ => false
  | Meth f => (getBool (string_dec gn (fst f)))
  end.

Lemma gexecs_all_Meth_correct gn execs :
  exists meths,
    (filter (gexecs gn) execs) = (map Meth meths) /\
    (forall g, In g meths -> fst g = gn).
Proof.
  induction execs.
  - exists nil; simpl; split; intros; auto; contradiction.
  - destruct a; auto.
    unfold gexecs; simpl.
    destruct string_dec; simpl; auto.
    dest; exists (f::x).
    simpl; rewrite <-H; split; intros; auto.
    destruct H1; subst; auto.
Qed.

Lemma gexecs_correct gn execs:
  (forall g, In (Meth g) (filter (gexecs gn) execs) -> fst g = gn).
Proof.
  induction execs; intros; simpl in *; try contradiction.
  unfold gexecs in H; destruct a; simpl in *; auto.
  destruct string_dec; simpl in *; auto.
  destruct H;[inv H|]; auto.
Qed.

Lemma gexecs_complement_correct gn execs:
  (forall g, In (Meth g) (filter (complement (gexecs gn)) execs) -> fst g <> gn).
Proof.
  induction execs; intros; simpl in *; try contradiction.
  unfold gexecs in H; destruct a; simpl in *.
  - destruct H;[discriminate|auto].
  - destruct string_dec; simpl in *; auto.
    destruct H; auto.
    inv H;intro; apply n; auto.
Qed.

Lemma  inlineSingle_Meth_in_list_key_match f gn l:
  (fst f) = gn ->
  inlineSingle_Meth_in_list f gn l = l.
Proof.
  induction l; simpl; auto.
  intros.
  destruct string_dec.
  - unfold inlineSingle_Meth.
    destruct a; simpl in *; subst.
    destruct string_dec.
    + rewrite IHl; auto.
    + exfalso; apply n; reflexivity.
  - rewrite IHl; auto.
Qed.

Lemma PPlusSubsteps_Meth_key_match f gn m o upds execs calls:
  (fst f) = gn ->
  PPlusSubsteps (inlineSingle_Meth_BaseModule f gn m) o upds execs calls ->
  PPlusSubsteps m o upds execs calls.
Proof.
  induction 2.
  - econstructor 1; eauto.
  - rewrite HUpds, HExecs, HCalls.
    econstructor 2; eauto.
  - rewrite HUpds, HExecs, HCalls.
    econstructor 3; eauto.
    clear - H HInMeths.
    simpl in *; rewrite inlineSingle_Meth_in_list_key_match in HInMeths; auto.
Qed.

Lemma PPlusSubsteps_PPlusSubsteps_inline_Meth f gn m o :
  forall execs upds calls,
    In f (getMethods m) ->
    NoDup (map fst (getMethods m)) ->
    NoDup (map fst (getRules m)) ->
    PPlusSubsteps (inlineSingle_Meth_BaseModule f gn m) o upds execs calls ->
    exists fcalls,
      PPlusSubsteps m o upds ((map Meth (fcalls))++execs) (fcalls++calls).
Proof.
  destruct (in_dec string_dec gn (map fst (getMethods m))).
  - destruct (string_dec (fst f) gn).
    + intros.
      exists nil; simpl in *.
      eapply PPlusSubsteps_Meth_key_match; eauto.
    + rewrite in_map_iff in i; dest; destruct x; subst; simpl in *.
      intros; specialize (separate_calls_by_filter execs (gexecs s)) as P1.
      rewrite P1 in H3.
      assert (NoDup (map fst (getMethods (inlineSingle_Meth_BaseModule f s m)))) as P2;
        [simpl; rewrite SameKeys_inline_Meth; auto|].
      assert (NoDup (map fst (getRules (inlineSingle_Meth_BaseModule f s m)))) as P3; auto.
      specialize (PPlusSubsteps_split_execs_OneRle P2 P3 _ _ H3) as P4.
      specialize (gexecs_all_Meth_correct s execs) as P5; dest.
      rewrite H4 in H3.
      apply PPlusSubsteps_split in H3; auto.
      * dest; specialize (PPlus_uninline_meths2 H n H1 _ H5 H8) as P5; dest.
        specialize (gexecs_complement_correct (gn:=s) execs) as P5.
        specialize (PPlusSubsteps_NoExec_PPlusSubsteps_inline_Meth H1 H P5 H9) as P6.
        exists x4; rewrite H6, H7, P1, H4, app_assoc, <-map_app, app_assoc.
        eapply PPlusSubsteps_merge; eauto.
        intros; destruct x5;[exfalso; clear -H11; induction (x4++x)|];auto.
        apply IHl; simpl in H11; destruct H11; auto; discriminate.
  - intros; exists nil; simpl.
    eapply PPlusSubsteps_PPlusSubsteps_inline_Meth_NotDef; eauto.
Qed.

Lemma PPlusStep_PPlusStep_inline_Meth f gn m o :
  forall execs upds calls,
    In f (getMethods m) ->
    NoDup (map fst (getMethods m)) ->
    NoDup (map fst (getRules m)) ->
    PPlusStep (inlineSingle_Meth_BaseModule f gn m) o upds execs calls ->
    exists fcalls,
      PPlusStep m o upds ((map Meth (fcalls))++execs) (fcalls++calls).
Proof.
  induction 4.
  apply PPlusSubsteps_PPlusSubsteps_inline_Meth in H2; auto.
  dest; exists x.
  econstructor; eauto.
  intros f0 P1.
  rewrite getNumFromCalls_app, getNumFromExecs_app, call_execs_counts_eq.
  specialize (H3 f0); simpl in *; rewrite SameKeys_inline_Meth in *.
  specialize (H3 P1); omega.
Qed.

Lemma PPlusStrongTraceInclusion_inlining_Meths_l m f rn :
  In f (getMethods m) ->
  (WfMod (Base m)) ->
  StrongPPlusTraceInclusion (inlineSingle_Meth_BaseModule f rn m) m.
Proof.
  unfold StrongPPlusTraceInclusion; induction 3; subst.
  - exists nil; split.
    + econstructor; eauto.
    + constructor.
  - inv H0; inv HWfBaseModule; dest.
    apply (PPlusStep_PPlusStep_inline_Meth) in HPPlusStep; auto; dest.
    exists ((upds, ((map Meth x0 ++ execs), (x0++calls)))::x); split.
    + econstructor 2; eauto.
    + constructor; auto.
      unfold WeakInclusion_flat; unfold getListFullLabel_diff_flat; simpl; split; intros.
      * rewrite getNumFromCalls_app, getNumFromExecs_app.
        repeat rewrite call_execs_counts_eq; omega.
      * dest; exists x1; rewrite in_app_iff in H9.
        destruct H9; auto.
        clear - H9; induction x0; simpl in *;[contradiction|].
        destruct H9;[discriminate|auto].
Qed.

Theorem TraceInclusion_inlining_Meths_l m f rn:
  In f (getMethods m) ->
  WfMod m ->
  TraceInclusion (inlineSingle_Meth_BaseModule f rn m) m.
Proof.
  intros.
  apply PPlusTraceInclusion_TraceInclusion; auto.
  - apply WfMod_Meth_inlined; auto.
  - apply StrongPPlusTraceInclusion_PPlusTraceInclusion.
    apply PPlusStrongTraceInclusion_inlining_Meths_l; auto.
Qed.

Theorem TraceInclusion_inlining_Meths_Wf_l {f} {m : BaseModuleWf} rn
        (inMeths: In f (getMethods m)):
  TraceInclusion (inlineSingle_Meth_BaseModuleWf rn inMeths) m.
Proof.
  simpl; apply TraceInclusion_inlining_Meths_l; eauto.
  constructor; apply wfBaseModule.
Qed.

Theorem inline_meth_transform_l f regs rules meths:
  (WfMod (Base (BaseMod regs rules meths))) ->
  In f meths ->
  forall i,
    TraceInclusion (Base (BaseMod regs rules (transform_nth_right (inlineSingle_Meth f) i meths))) (Base (BaseMod regs rules meths)).
Proof.
  intros; destruct (lt_dec i (length meths)).
  - pose proof H as H'.
    inv H; simpl in *.
    destruct HWfBaseModule as [? [? [NoDupMeths [NoDupRegisters NoDupRle]]]].
    simpl in *.
    specialize (inlineSingle_Meth_transform_nth f _ NoDupMeths l) as TMP; dest.
    rewrite H3.
    assert (In f (getMethods (BaseMod regs rules meths))); auto.
    specialize (TraceInclusion_inlining_Meths_l (rn:=(fst x)) H4 H') as P1.
    unfold inlineSingle_Meth_BaseModule in P1; simpl in *; assumption.
  - apply Nat.nlt_ge in n.
    rewrite inlineSingle_transform_gt; auto.
    apply TraceInclusion_refl.
Qed.

Theorem inline_meth_transform_Wf_l {f} {m : BaseModuleWf} i (inMeths : In f (getMethods m)):
    TraceInclusion (inline_nth_Meth_BaseModuleWf i inMeths) m.
Proof.
  intros; simpl.
  specialize (TraceInclusion_flatten_l m) as P1.
  specialize (wfMod (flatten_ModWf m)) as P2; simpl in *.
  unfold flatten, getFlat in *; simpl in *.
  specialize (inline_meth_transform_l f P2 inMeths i) as P3.
  eauto using TraceInclusion_trans.
Qed.

Theorem inline_rule_transform_l f regs rules meths:
  (WfMod (Base (BaseMod regs rules meths))) ->
  In f meths ->
  forall i,
    TraceInclusion (Base (BaseMod regs (transform_nth_right (inlineSingle_Rule f) i rules) meths)) (Base (BaseMod regs rules meths)).
Proof.
  intros; destruct (lt_dec i (length rules)).
  - pose proof H as H'.
    inv H; simpl in *.
    destruct HWfBaseModule as [? [? [NoDupMeths [NoDupRegisters NoDupRle]]]].
    simpl in *.
    specialize (inlineSingle_Rule_transform_nth f _ NoDupRle l) as TMP; dest.
    rewrite H3.
    assert (In f (getMethods (BaseMod regs rules meths))); auto.
    specialize (TraceInclusion_inlining_Rules_l (rn:=fst x) H4 H') as P1.
    unfold inlineSingle_Rule_BaseModule in P1; simpl in *; assumption.
  - apply Nat.nlt_ge in n.
    rewrite inlineSingle_transform_gt; auto.
    apply TraceInclusion_refl.
Qed.

Theorem inline_rule_transform_Wf_l {f} {m : BaseModuleWf} i (inMeths : In f (getMethods m)):
    TraceInclusion (inline_nth_Rule_BaseModuleWf i inMeths) m.
Proof.
  intros; simpl.
  specialize (TraceInclusion_flatten_l m) as P1.
  specialize (wfMod (flatten_ModWf m)) as P2; simpl in *.
  unfold flatten, getFlat in *; simpl in *.
  specialize (inline_rule_transform_l f P2 inMeths i) as P3.
  eauto using TraceInclusion_trans.
Qed.

Section inlineSingle_nth_l.
  Variable (f : DefMethT).
  Variable (regs: list RegInitT) (rules: list RuleT) (meths: list DefMethT).
  Variable (Wf : WfMod (Base (BaseMod regs rules meths))).

  Theorem inline_meth_fold_right_l xs:
    In f meths ->
    TraceInclusion (Base (BaseMod regs rules (fold_right (transform_nth_right (inlineSingle_Meth f)) meths xs))) (Base (BaseMod regs rules meths)).
  Proof.
    induction xs; intros.
    - simpl; apply TraceInclusion_refl.
    - simpl.
      specialize (IHxs H).
      specialize (WfMod_inline_all_Meth _ xs H Wf) as P1.
      specialize (inlined_Meth_not_transformed_fold_right _ xs _ H) as P2.
      specialize (inline_meth_transform_l _ P1 P2 a) as P3.
      apply (TraceInclusion_trans P3 IHxs).
  Qed.
  
  Theorem inline_rule_fold_right_l xs:
    In f meths ->
    TraceInclusion (Base (BaseMod regs (fold_right (transform_nth_right (inlineSingle_Rule f)) rules xs) meths)) (Base (BaseMod regs rules meths)).
  Proof.
    induction xs; intros.
    - simpl; apply TraceInclusion_refl.
    - simpl.
      specialize (IHxs H).
      specialize (WfMod_inline_all_Rule _ xs H Wf) as P1.
      specialize (inline_rule_transform_l _ P1 H a) as P2.
      apply (TraceInclusion_trans P2 IHxs).
  Qed.
End inlineSingle_nth_l.

Theorem inline_meth_fold_right_Wf_l {f} {m : BaseModuleWf} xs (inMeth : In f (getMethods m)):
  TraceInclusion (inline_all_Meth_BaseModuleWf xs inMeth) m.
Proof.
  specialize (TraceInclusion_flatten_l m) as P1.
  simpl in *; unfold flatten, getFlat in P1; simpl in *.
  assert (WfMod m) as TMP;[constructor; apply wfBaseModule
                          |specialize (WfMod_getFlat TMP) as P2; clear TMP].
  specialize (inline_meth_fold_right_l f P2 xs inMeth) as P3.
  eauto using TraceInclusion_trans.
Qed.

Theorem inline_rule_fold_right_Wf_l {f} {m : BaseModuleWf} xs (inMeth : In f (getMethods m)):
  TraceInclusion (inline_all_Rule_BaseModuleWf xs inMeth) m.
Proof.
  specialize (TraceInclusion_flatten_l m) as P1.
  simpl in *; unfold flatten, getFlat in P1; simpl in *.
  assert (WfMod m) as TMP;[constructor; apply wfBaseModule
                          |specialize (WfMod_getFlat TMP) as P2; clear TMP].
  specialize (inline_rule_fold_right_l f P2 xs inMeth) as P3.
  eauto using TraceInclusion_trans.
Qed.

Theorem TraceInclusion_inline_BaseModule_rules_l regs rules meths f:
  (WfMod (Base (BaseMod regs rules meths))) ->
  In f meths ->
  TraceInclusion (Base (BaseMod regs (map (inlineSingle_Rule f) rules) meths)) (Base (BaseMod regs rules meths)).
Proof.
  intros.
  unfold inlineSingle_BaseModule.
  specialize (inline_rule_fold_right_l f H (seq 0 (length rules)) H0) as P1.
  specialize (WfMod_inline_all_Rule _ (seq 0 (length rules)) H0 H) as P2.
  repeat rewrite map_fold_right_eq in *.
  assumption.
Qed.

Theorem TraceInclusion_inline_BaseModule_rules_Wf_l {f} {m : BaseModuleWf}
        (inMeth : In f (getMethods m)):
  TraceInclusion (inline_BaseModule_rules_BaseModuleWf inMeth) m.
Proof.
  specialize (TraceInclusion_flatten_l m) as P1.
  simpl in *; unfold flatten, getFlat in P1; simpl in *.
  assert (WfMod m) as TMP;[constructor; apply wfBaseModule
                          |specialize (WfMod_getFlat TMP) as P2; clear TMP].
  specialize (TraceInclusion_inline_BaseModule_rules_l f P2 inMeth) as P3.
  eauto using TraceInclusion_trans.
Qed.

Theorem TraceInclusion_inline_BaseModule_meths_l regs rules meths f:
  (WfMod (Base (BaseMod regs rules meths))) ->
  In f meths ->
  TraceInclusion (Base (BaseMod regs rules (map (inlineSingle_Meth f) meths))) (Base (BaseMod regs rules meths)).
Proof.
  intros.
  unfold inlineSingle_BaseModule.
  specialize (inline_meth_fold_right_l f H (seq 0 (length meths)) H0) as P1.
  repeat rewrite map_fold_right_eq in *.
  assumption.
Qed.

Theorem TraceInclusion_inline_BaseModule_meths_Wf_l {f} {m : BaseModuleWf}
        (inMeth : In f (getMethods m)):
  TraceInclusion (inline_BaseModule_meths_BaseModuleWf inMeth) m.
Proof.
  specialize (TraceInclusion_flatten_l m) as P1.
  simpl in *; unfold flatten, getFlat in P1; simpl in *.
  assert (WfMod m) as TMP;[constructor; apply wfBaseModule
                          |specialize (WfMod_getFlat TMP) as P2; clear TMP].
  specialize (TraceInclusion_inline_BaseModule_meths_l f P2 inMeth) as P3.
  eauto using TraceInclusion_trans.
Qed.

Theorem TraceInclusion_inline_BaseModule_all_l regs rules meths f:
  (WfMod (Base (BaseMod regs rules meths))) ->
  In f meths ->
  TraceInclusion (Base (inlineSingle_BaseModule f regs rules meths)) (Base (BaseMod regs rules meths)).
Proof.
  intros.
  unfold inlineSingle_BaseModule.
  specialize (TraceInclusion_inline_BaseModule_rules_l f H H0) as P1.
  specialize (WfMod_inline_all_Rule _ (seq 0 (length rules)) H0 H) as P2.
  specialize (TraceInclusion_inline_BaseModule_meths_l f P2 H0) as P3.
  repeat rewrite map_fold_right_eq in *.
  apply (TraceInclusion_trans P3 P1).
Qed.

Theorem TraceInclusion_inline_BaseModule_all_Wf_l {f} {m : BaseModuleWf}
        (inMeth : In f (getMethods m)):
  TraceInclusion (inlineSingle_BaseModuleWf inMeth) m.
Proof.
  specialize (TraceInclusion_flatten_l m) as P1.
  specialize (wfMod (flatten_ModWf m)) as P2.
  simpl in *; unfold flatten, getFlat in *; simpl in *.
  specialize (TraceInclusion_inline_BaseModule_all_l P2 inMeth) as P3.
  eauto using TraceInclusion_trans.
Qed.

Section inline_all_all_l.
  Theorem TraceInclusion_inlineSingle_pos_Rules_l regs rules meths:
    (WfMod (Base (BaseMod regs rules meths))) ->
    forall n,
      (WfMod (Base (BaseMod regs (inlineSingle_Rules_pos meths n rules) meths))) /\
      TraceInclusion (Base (BaseMod regs (inlineSingle_Rules_pos meths n rules) meths)) (Base (BaseMod regs rules meths)).
  Proof.
    intros WfH n.
    unfold inlineSingle_Rules_pos.
    case_eq (nth_error meths n); intros sth; [intros sthEq|split; [assumption | apply TraceInclusion_refl]].
    split.
    - apply nth_error_In in sthEq.
      pose proof (WfMod_inline_all_Rule sth (seq 0 (length rules)) sthEq WfH).
      repeat rewrite map_fold_right_eq in *.
      assumption.
    - apply TraceInclusion_inline_BaseModule_rules_l; auto.
      eapply nth_error_In; eauto.
  Qed.

  Theorem TraceInclusion_inlineSingle_pos_Rules_Wf_l (m : BaseModuleWf) n :
    TraceInclusion (inlineSingle_Rules_pos_BaseModuleWf m n) m.
  Proof.
    specialize (TraceInclusion_flatten_l m) as P1.
    specialize (wfMod (flatten_ModWf m)) as P2.
    simpl in *; unfold flatten, getFlat in *; simpl in *.
    specialize (TraceInclusion_inlineSingle_pos_Rules_l P2 n) as TMP; dest.
    eauto using TraceInclusion_trans.
  Qed.
  
  Theorem TraceInclusion_inlineAll_pos_Rules_l regs rules meths:
    (WfMod (Base (BaseMod regs rules meths))) ->
    (WfMod (Base (BaseMod regs (inlineAll_Rules meths rules) meths))) /\
    TraceInclusion (Base (BaseMod regs (inlineAll_Rules meths rules) meths))  (Base (BaseMod regs rules meths)).
  Proof.
    intros WfH.
    unfold inlineAll_Rules.
    induction (Datatypes.length meths); [simpl in *; split; [assumption | apply TraceInclusion_refl]|].
    rewrite seq_eq.
    rewrite fold_left_app; simpl in *.
    destruct IHn as [IHn1 IHn2].
    pose proof (TraceInclusion_inlineSingle_pos_Rules_l IHn1 n) as [sth1 sth2].
    destruct n; simpl in *; auto.
    split; auto.
    eapply TraceInclusion_trans; eauto.
  Qed.
  
  Theorem TraceInclusion_inlineAll_pos_Rules_Wf_l (m : BaseModuleWf) :
    TraceInclusion (inlineAll_Rules_BaseModuleWf m) m.
  Proof.
    specialize (TraceInclusion_flatten_l m) as P1.
    specialize (wfMod (flatten_ModWf m)) as P2.
    simpl in *; unfold flatten, getFlat in *; simpl in *.
    specialize (TraceInclusion_inlineAll_pos_Rules_l P2) as TMP; dest.
    eauto using TraceInclusion_trans.
  Qed.
  
  Theorem TraceInclusion_inlineSingle_pos_Meths_l regs rules meths:
    (WfMod (Base (BaseMod regs rules meths))) ->
    forall n,
      (WfMod (Base (BaseMod regs rules (inlineSingle_Meths_pos meths n)))) /\
      TraceInclusion (Base (BaseMod regs rules (inlineSingle_Meths_pos meths n))) (Base (BaseMod regs rules meths)).
  Proof.
    intros WfH n.
    unfold inlineSingle_Meths_pos.
    case_eq (nth_error meths n); intros sth; [intros sthEq|split; [assumption | apply TraceInclusion_refl]].
    split.
    - apply nth_error_In in sthEq.
      pose proof (WfMod_inline_all_Meth sth (seq 0 (length meths)) sthEq WfH).
      repeat rewrite map_fold_right_eq in *.
      assumption.
    - apply TraceInclusion_inline_BaseModule_meths_l; auto.
      eapply nth_error_In; eauto.
  Qed.
  
  Theorem TraceInclusion_inlineSingle_pos_Meths_Wf_l (m : BaseModuleWf) n :
    TraceInclusion (inlineSingle_Meths_pos_BaseModuleWf m n) m.
  Proof.
    specialize (TraceInclusion_flatten_l m) as P1.
    specialize (wfMod (flatten_ModWf m)) as P2.
    simpl in *; unfold flatten, getFlat in *; simpl in *.
    specialize (TraceInclusion_inlineSingle_pos_Meths_l P2 n) as TMP; dest.
    eauto using TraceInclusion_trans.
  Qed.
  
  Theorem TraceInclusion_inlineAll_pos_Meths_l regs rules meths:
    (WfMod (Base (BaseMod regs rules meths))) ->
    (WfMod (Base (BaseMod regs rules (inlineAll_Meths meths)))) /\
    TraceInclusion (Base (BaseMod regs rules (inlineAll_Meths meths))) (Base (BaseMod regs rules meths)).
  Proof.
    intros WfH.
    unfold inlineAll_Meths.
    induction (Datatypes.length meths); [simpl; split; [assumption | apply TraceInclusion_refl]|].
    rewrite seq_eq.
    rewrite fold_left_app; simpl.
    destruct IHn as [IHn1 IHn2].
    pose proof (TraceInclusion_inlineSingle_pos_Meths_l IHn1 n) as [sth1 sth2].
    destruct n; simpl in *; auto.
    split; auto.
    eapply TraceInclusion_trans; eauto.
  Qed.
  
  Theorem TraceInclusion_inlineAll_pos_Meths_Wf_l (m : BaseModuleWf) :
    TraceInclusion (inlineAll_Meths_BaseModuleWf m) m.
  Proof.
    specialize (TraceInclusion_flatten_l m) as P1.
    specialize (wfMod (flatten_ModWf m)) as P2.
    simpl in *; unfold flatten, getFlat in *; simpl in *.
    specialize (TraceInclusion_inlineAll_pos_Meths_l P2) as TMP; dest.
    eauto using TraceInclusion_trans.
  Qed.
  
  Theorem TraceInclusion_inlineAll_pos_l regs rules meths:
    (WfMod (Base (BaseMod regs rules meths))) ->
    (WfMod (Base (inlineAll_All regs rules meths))) /\
    TraceInclusion (Base (inlineAll_All regs rules meths)) (Base (BaseMod regs rules meths)).
  Proof.
    unfold inlineAll_All in *.
    intros WfH1.
    pose proof (TraceInclusion_inlineAll_pos_Meths_l WfH1) as [WfH2 P2].
    pose proof (TraceInclusion_inlineAll_pos_Rules_l WfH2) as [WfH3 P3].
    split; auto.
    eapply TraceInclusion_trans; eauto.
  Qed.

  Theorem TraceInclusion_inlineAll_pos_Wf_l (m : BaseModuleWf) :
    TraceInclusion (inlineAll_All_BaseModuleWf m) m.
  Proof.
    specialize (TraceInclusion_flatten_l m) as P1.
    specialize (wfMod (flatten_ModWf m)) as P2.
    simpl in *; unfold flatten, getFlat in *; simpl in *.
    specialize (TraceInclusion_inlineAll_pos_l P2) as TMP; dest.
    eauto using TraceInclusion_trans.
  Qed.
End inline_all_all_l.

Theorem TraceInclusion_flatten_inline_everything_l (m : ModWf) :
  TraceInclusion (flatten_inline_everything_ModWf m) m.
Proof.
  specialize (wfMod (flatten_inline_everything_ModWf m)) as Wf1.
  simpl.
  specialize (TraceInclusion_flatten_l m) as P1.
  unfold flatten, getFlat in *.
  assert (WfMod (Base (getFlat m))). {
    intros.
    apply (WfMod_WfBase_getFlat (wfMod m)).
  }
  unfold getFlat in *.
  specialize (TraceInclusion_inlineAll_pos_l H) as TMP; dest.
  unfold inlineAll_All in *.
  apply (Trace_createHide (getHidden m)) in H1.
  eauto using TraceInclusion_trans.
Qed.

Theorem inlineSingle_Rule_map_TraceInclusion_l {m : ModWf} {f : DefMethT} (inMeths : In f (getAllMethods m)):
  TraceInclusion (inlineSingle_Rule_map_ModWf inMeths) m.
Proof.
  intros.
  specialize (TraceInclusion_flatten_l m) as TI_flatten; simpl in *.
  unfold flatten, inlineSingle_Rule_map_BaseModule, getFlat in *; simpl in *.
  specialize (TraceInclusion_inline_BaseModule_rules_l f (WfMod_WfBase_getFlat (wfMod m)) inMeths) as P1.
  specialize (Trace_createHide (getHidden m) P1) as P2.
  eauto using TraceInclusion_trans.
Qed.

Theorem inlineSingle_Meth_map_TraceInclusion_l {m : ModWf}  {f : DefMethT} (inMeths : In f (getAllMethods m)) :
  TraceInclusion (inlineSingle_Meth_map_ModWf inMeths) m.
Proof.
  intros.
  specialize (TraceInclusion_flatten_l m) as TI_flatten; simpl in *.
  unfold flatten, inlineSingle_Meth_map_BaseModule, getFlat in *; simpl in *.
  specialize (TraceInclusion_inline_BaseModule_meths_l f (WfMod_WfBase_getFlat (wfMod m)) inMeths) as P1.
  specialize (Trace_createHide (getHidden m) P1) as P2.
  eauto using TraceInclusion_trans.
Qed.

Theorem inlineSingle_BaseModule_TraceInclusion_l {m : ModWf} {f : DefMethT} (inMeths : In f (getAllMethods m)) :
  TraceInclusion (inlineSingle_Module_ModWf inMeths) m.
Proof.
  specialize (TraceInclusion_flatten_l  m) as TI_flatten; simpl in *.
  unfold flatten, getFlat in *; simpl in *.
  specialize (flatten_WfMod (wfMod m)) as P1; unfold flatten, getFlat in P1; simpl in P1.
  rewrite WfMod_createHide in P1; dest.
  specialize (TraceInclusion_inline_BaseModule_all_l H0 inMeths) as P2.
  specialize (Trace_createHide (getHidden m) P2) as P3.
  eauto using TraceInclusion_trans.
Qed.

Theorem inlineSingle_BaseModule_nth_Meth_TraceInclusion_l {m : ModWf} {f : DefMethT} (inMeths : In f (getAllMethods m)) (xs : list nat) :
  TraceInclusion (inlineSingle_BaseModule_nth_Meth_ModWf inMeths xs) m.
Proof.
  specialize (TraceInclusion_flatten_l m) as TI_flatten; simpl in *.
  unfold flatten, getFlat in *; simpl in *.
  specialize (flatten_WfMod (wfMod m)) as P1; unfold flatten, getFlat in P1; simpl in P1.
  rewrite WfMod_createHide in P1; dest.
  specialize (inline_meth_fold_right_l _ H0 xs inMeths) as P2.
  specialize (Trace_createHide (getHidden m) P2) as P3.
  eauto using TraceInclusion_trans.
Qed.

Theorem inlineSingle_BaseModule_nth_Rule_TraceInclusion_l {m : ModWf} {f : DefMethT} (inMeths : In f (getAllMethods m)) (xs : list nat) :
  TraceInclusion (inlineSingle_BaseModule_nth_Rule_ModWf inMeths xs) m.
Proof.
  specialize (TraceInclusion_flatten_l m) as TI_flatten; simpl in *.
  unfold flatten, getFlat in *; simpl in *.
  specialize (flatten_WfMod (wfMod m)) as P1; unfold flatten, getFlat in P1; simpl in P1.
  rewrite WfMod_createHide in P1; dest.
  specialize (inline_rule_fold_right_l _ H0 xs inMeths) as P2.
  specialize (Trace_createHide (getHidden m) P2) as P3.
  eauto using TraceInclusion_trans.
Qed.

Theorem inlineAll_Rules_TraceInclusion_l (m : ModWf) :
  TraceInclusion (inlineAll_Rules_ModWf m) m.
Proof.
  specialize (flatten_WfMod (wfMod m)) as P1; unfold flatten, getFlat in P1; simpl in P1.
  rewrite WfMod_createHide in P1; dest.
  specialize (TraceInclusion_inlineAll_pos_Rules_l H0) as P2; dest.
  specialize (Trace_createHide (getHidden m) H2) as P1.
  specialize (TraceInclusion_flatten_l m) as TI_flatten; simpl in *.
  unfold flatten, getFlat in *; simpl in *.
  eauto using TraceInclusion_trans.
Qed.

Theorem inlineAll_Meths_TraceInclusion_l (m : ModWf) :
  TraceInclusion (inlineAll_Meths_ModWf m) m.
Proof.
  specialize (flatten_WfMod (wfMod m)) as P1; unfold flatten, getFlat in P1; simpl in P1.
  rewrite WfMod_createHide in P1; dest.
  specialize (TraceInclusion_inlineAll_pos_Meths_l H0) as P2; dest.
  specialize (Trace_createHide (getHidden m) H2) as P1.
  specialize (TraceInclusion_flatten_l m) as TI_flatten; simpl in *.
  unfold flatten, getFlat in *; simpl in *.
  eauto using TraceInclusion_trans.
Qed.

Theorem flatten_inline_remove_TraceInclusion_l_lemma (m : ModWf) :
  NoSelfCallBaseModule (inlineAll_All_mod m) ->
  TraceInclusion (flatten_inline_remove_ModWf m) (flatten_inline_everything m).
Proof.
  simpl; unfold flatten_inline_everything, flatten_inline_remove.
  intros.
  specialize (WfMod_WfBase_getFlat (wfMod m)) as P1; unfold getFlat in *.
  specialize (TraceInclusion_inlineAll_pos_l P1) as P2; inv P2.
  inv H0.
  assert (SubList (getHidden m) (map fst (getMethods (Build_BaseModuleWf (HWfBaseModule))))) as P2;
    [repeat intro; simpl; rewrite <- SameKeys_inlineAll_Meths; eapply WfMod_Hidden;
     eauto using (wfMod m)|].
  apply (removeHides_createHide_TraceInclusion P2 H).
Qed.

Theorem TraceInclusion_flatten_inline_remove_ModWf_l_lemma (m : ModWf):
  NoSelfCallBaseModule (inlineAll_All_mod m) ->
  TraceInclusion (flatten_inline_remove_ModWf m) (flatten_inline_everything_ModWf m).
Proof.
  intros.
  unfold flatten_inline_everything_ModWf.
  eauto using flatten_inline_remove_TraceInclusion_l_lemma.
Qed.

Theorem TraceInclusion_flatten_inline_remove_ModWf_r_lemma (m : ModWf):
  NoSelfCallBaseModule (inlineAll_All_mod m) ->
  TraceInclusion (flatten_inline_everything_ModWf m) (flatten_inline_remove_ModWf m).
Proof.
  intros.
  unfold flatten_inline_everything_ModWf.
  eauto using flatten_inline_remove_TraceInclusion_r_lemma.
Qed.

Theorem flatten_inline_remove_TraceInclusion_l (m : ModWf) :
  NoSelfCallBaseModule (inlineAll_All_mod m) ->
  TraceInclusion (flatten_inline_remove_ModWf m) m.
Proof.
  intros H.
  eapply TraceInclusion_trans.
  - eapply TraceInclusion_flatten_inline_remove_ModWf_l_lemma; eauto.
  - eapply TraceInclusion_flatten_inline_everything_l.
Qed.
  
Theorem flatten_inline_remove_TraceInclusion_r (m : ModWf) :
  NoSelfCallBaseModule (inlineAll_All_mod m) ->
  TraceInclusion m (flatten_inline_remove_ModWf m).
Proof.
  intros H.
  eapply TraceInclusion_trans.
  - eapply TraceInclusion_flatten_inline_everything_r.
  - eapply TraceInclusion_flatten_inline_remove_ModWf_r_lemma; eauto.
Qed.
  
Theorem TraceInclusion_flatten_inline_remove_ModWf_l (m : ModWf):
  NoSelfCallBaseModule (inlineAll_All_mod m) ->
  TraceInclusion (flatten_inline_remove_ModWf m) m.
Proof.
  intros.
  unfold flatten_inline_remove_ModWf.
  eauto using flatten_inline_remove_TraceInclusion_l.
Qed.

Theorem TraceInclusion_flatten_inline_remove_ModWf_r (m : ModWf):
  NoSelfCallBaseModule (inlineAll_All_mod m) ->
  TraceInclusion m (flatten_inline_remove_ModWf m).
Proof.
  intros.
  unfold flatten_inline_remove_ModWf.
  eauto using flatten_inline_remove_TraceInclusion_r.
Qed.

Theorem TraceEquiv_flatten_inline_remove_ModWf (m: ModWf):
  NoSelfCallBaseModule (inlineAll_All_mod m) ->
  TraceEquiv m (flatten_inline_remove_ModWf m).
Proof.
  unfold TraceEquiv.
  intros.
  split.
  - eapply TraceInclusion_flatten_inline_remove_ModWf_r; auto.
  - eapply TraceInclusion_flatten_inline_remove_ModWf_l; auto.
Qed.

Lemma distributeHideWf (m1 m2 : Mod) (h : string) (HNeverCall : NeverCallMod m1):
  WfMod (HideMeth (ConcatMod m1 m2) h) ->
  ~ In h (map fst (getAllMethods m1)) ->
  WfMod (ConcatMod m1 (HideMeth m2 h)).
Proof.
  intros; inv H.
  inv HWf.
  econstructor; simpl in *; eauto.
  - econstructor; eauto.
    rewrite map_app, in_app_iff in *.
    destruct HHideWf; auto.
    exfalso; tauto.
  - inv WfConcat1; econstructor; intros.
    + specialize (H _ H2).
      induction HNeverCall.
      -- inv HNCBaseModule.
         specialize (H3 _ H2).
         induction H; inv H3; EqDep_subst; econstructor; eauto.
         tauto.
      -- eapply IHHNeverCall; eauto.
         ++ inv HWf1; assumption.
         ++ assert (forall f, In f (getHidden m) -> In f (getHidden (HideMeth m s))) as P0;
              [intros; simpl in *; right; assumption|];inv WfConcat2; split.
            ** intros; specialize (H3 _ H5).
               clear - H3 P0.
               induction H3; econstructor; eauto.
            ** intros; specialize (H4 _ H5 v).
               clear - H4 P0.
               induction H4; econstructor; eauto.
      -- simpl in *.
         rewrite map_app, in_map_iff, in_app_iff in *.
         apply Decidable.not_or in H0; dest.
         destruct H2.
         ++ eapply IHHNeverCall1; eauto.
            ** intro; dest.
               apply H0.
               rewrite in_map_iff.
               eauto.
            ** right.
               destruct HHideWf; auto.
               exfalso.
               rewrite map_app, in_app_iff in *.
               clear - H0 H3 H4; tauto.
            ** clear - HDisjRegs.
               intro k; specialize (HDisjRegs k).
               rewrite map_app, in_app_iff in *.
               firstorder.
            ** clear - HDisjRules.
               intro k; specialize (HDisjRules k).
               rewrite map_app, in_app_iff in *.
               firstorder.
            ** clear - HDisjMeths.
               intro k; specialize (HDisjMeths k).
               rewrite map_app, in_app_iff in *.
               firstorder.
            ** inv HWf1; auto.
            ** clear - WfConcat2.
               inv WfConcat2.
               assert (forall f, ~In f (getHidden (ConcatMod m1 m0))
                                 -> ~In f (getHidden m1)) as P0;
                 [intros; simpl in *; intro; apply H1; rewrite in_app_iff; firstorder|].
               split.
               --- intros; specialize (H _ H1).
                   clear - H P0. 
                   induction H; econstructor; eauto.
               --- intros; specialize (H0 _ H1 v).
                   clear - H0 P0.
                   induction H0; econstructor; eauto.
            ** intros; eapply H1.
               rewrite in_app_iff; left; assumption.
         ++ eapply IHHNeverCall2; eauto.
            ** intro; dest.
               apply H3.
               rewrite in_map_iff.
               eauto.
                        ** right.
               destruct HHideWf; auto.
               exfalso.
               rewrite map_app, in_app_iff in *.
               clear - H0 H3 H4; tauto.
            ** clear - HDisjRegs.
               intro k; specialize (HDisjRegs k).
               rewrite map_app, in_app_iff in *.
               firstorder.
            ** clear - HDisjRules.
               intro k; specialize (HDisjRules k).
               rewrite map_app, in_app_iff in *.
               firstorder.
            ** clear - HDisjMeths.
               intro k; specialize (HDisjMeths k).
               rewrite map_app, in_app_iff in *.
               firstorder.
            ** inv HWf1; auto.
            ** clear - WfConcat2.
               inv WfConcat2.
               assert (forall f, ~In f (getHidden (ConcatMod m1 m0))
                                 -> ~In f (getHidden m0)) as P0;
                 [intros; simpl in *; intro; apply H1; rewrite in_app_iff; firstorder|].
               split.
               --- intros; specialize (H _ H1).
                   clear - H P0. 
                   induction H; econstructor; eauto.
               --- intros; specialize (H0 _ H1 v).
                   clear - H0 P0.
                   induction H0; econstructor; eauto.
            ** intros; eapply H1.
               rewrite in_app_iff; right; assumption.
    + specialize (H1 _ H2 v).
      induction HNeverCall.
      -- inv HNCBaseModule.
         specialize (H4 _ H2 v).
         induction H1; inv H4; EqDep_subst; econstructor; eauto.
         tauto.
      -- eapply IHHNeverCall; eauto.
         ++ inv HWf1; assumption.
         ++ assert (forall f, In f (getHidden m) -> In f (getHidden (HideMeth m s))) as P0;
              [intros; simpl in *; right; assumption|];inv WfConcat2; split.
            ** intros; specialize (H3 _ H5).
               clear - H3 P0.
               induction H3; econstructor; eauto.
            ** intros; specialize (H4 _ H5 v0).
               clear - H4 P0.
               induction H4; econstructor; eauto.
      -- simpl in *.
         rewrite map_app, in_map_iff, in_app_iff in *.
         apply Decidable.not_or in H0; dest.
         destruct H2.
         ++ eapply IHHNeverCall1; eauto.
            ** intro; dest.
               apply H0.
               rewrite in_map_iff.
               eauto.
            ** right.
               destruct HHideWf; auto.
               exfalso.
               rewrite map_app, in_app_iff in *.
               clear - H0 H3 H4; tauto.
            ** clear - HDisjRegs.
               intro k; specialize (HDisjRegs k).
               rewrite map_app, in_app_iff in *.
               firstorder.
            ** clear - HDisjRules.
               intro k; specialize (HDisjRules k).
               rewrite map_app, in_app_iff in *.
               firstorder.
            ** clear - HDisjMeths.
               intro k; specialize (HDisjMeths k).
               rewrite map_app, in_app_iff in *.
               firstorder.
            ** inv HWf1; auto.
            ** clear - WfConcat2.
               inv WfConcat2.
               assert (forall f, ~In f (getHidden (ConcatMod m1 m0))
                                 -> ~In f (getHidden m1)) as P0;
                 [intros; simpl in *; intro; apply H1; rewrite in_app_iff; firstorder|].
               split.
               --- intros; specialize (H _ H1).
                   clear - H P0. 
                   induction H; econstructor; eauto.
               --- intros; specialize (H0 _ H1 v).
                   clear - H0 P0.
                   induction H0; econstructor; eauto.
            ** intros; eapply H.
               rewrite in_app_iff; left; assumption.
         ++ eapply IHHNeverCall2; eauto.
            ** intro; dest.
               apply H3.
               rewrite in_map_iff.
               eauto.
                        ** right.
               destruct HHideWf; auto.
               exfalso.
               rewrite map_app, in_app_iff in *.
               clear - H0 H3 H4; tauto.
            ** clear - HDisjRegs.
               intro k; specialize (HDisjRegs k).
               rewrite map_app, in_app_iff in *.
               firstorder.
            ** clear - HDisjRules.
               intro k; specialize (HDisjRules k).
               rewrite map_app, in_app_iff in *.
               firstorder.
            ** clear - HDisjMeths.
               intro k; specialize (HDisjMeths k).
               rewrite map_app, in_app_iff in *.
               firstorder.
            ** inv HWf1; auto.
            ** clear - WfConcat2.
               inv WfConcat2.
               assert (forall f, ~In f (getHidden (ConcatMod m1 m0))
                                 -> ~In f (getHidden m0)) as P0;
                 [intros; simpl in *; intro; apply H1; rewrite in_app_iff; firstorder|].
               split.
               --- intros; specialize (H _ H1).
                   clear - H P0. 
                   induction H; econstructor; eauto.
               --- intros; specialize (H0 _ H1 v).
                   clear - H0 P0.
                   induction H0; econstructor; eauto.
            ** intros; eapply H.
               rewrite in_app_iff; right; assumption.
Qed.

Lemma distributeHidesWf (m1 m2 : Mod) (hl1 hl2 : list string)
      (HNeverCall : NeverCallMod m1):
  WfMod (createHideMod (ConcatMod m1 m2) (hl1++hl2)) ->
  (forall h, In h hl1 -> ~ In h (map fst (getAllMethods m1))) ->
  WfMod (createHideMod (ConcatMod m1 (createHideMod m2 hl1)) hl2).
Proof.
  induction hl1; simpl; intros; auto.
  rewrite WfMod_createHideMod; split.
  - simpl.
    repeat intro.
    rewrite map_app, in_app_iff.
    rewrite getAllMethods_createHideMod.
    inv H.
    rewrite WfMod_createHideMod in HWf; dest.
    specialize (H x (in_or_app _ _ _(or_intror _ H1))); simpl in *.
    rewrite map_app, in_app_iff in *; destruct H; auto.
  - apply distributeHideWf; auto.
    constructor; inv H.
    + rewrite getAllMethods_createHideMod in *; simpl in *.
      rewrite map_app, in_app_iff, getAllMethods_createHideMod in *; assumption.
    + assert (forall h : string, In h hl1 -> ~ In h (map fst (getAllMethods m1))) as P0;
      [intros; apply H0; auto|].
      specialize (IHhl1 HWf P0).
      rewrite WfMod_createHideMod in IHhl1; dest; assumption.
Qed.

Lemma WfMod_perm (m : Mod) (hl1 hl2: list string):
  hl1 [=] hl2 ->
  WfMod (createHideMod m hl1) ->
  WfMod (createHideMod m hl2).
Proof.
  intros.
  rewrite WfMod_createHideMod in *; dest; split; auto.
  repeat intro.
  rewrite <- H in H2.
  specialize (H0 _ H2).
  assumption.
Qed.

Definition StrongTraceInclusion' (m m' : Mod) : Prop :=
  forall (o : RegsT) (ls : list (list FullLabel)),
    Trace m o ls ->
    exists (ls' : list (list FullLabel)),
      Trace m' o ls' /\ WeakInclusions ls ls'.

Lemma StrongTI'_TI' (m m' : Mod) :
  StrongTraceInclusion' m m' -> TraceInclusion' m m'.
Proof.
  repeat intro.
  specialize (H _ _ H0).
  dest.
  exists x; split;[exists o|];assumption.
Qed.

Lemma action_noCalls {k : Kind} (o : RegsT) (a : ActionT type k) (reads u : RegsT)
      (cs : MethsT) (fret : type k) (HNeverCallAct : NeverCallActionT a):
  SemAction o a reads u cs fret ->
  cs = [].
Proof.
  induction 1; auto; try inv HNeverCallAct; EqDep_subst; eauto.
  - tauto.
  - rewrite IHSemAction1, IHSemAction2; auto.
  - rewrite IHSemAction1, IHSemAction2; auto.
  - rewrite IHSemAction1, IHSemAction2; auto.
Qed.

Lemma Substeps_NeverCall_getNumCalls_0 (m : BaseModule)(o : RegsT)(l : list FullLabel)
      (HNeverCallBase : NeverCallBaseModule m) :
  Substeps m o l ->
  forall (f : MethT), getNumCalls f l = 0%Z.
Proof.
  induction 1; intros; simpl.
  - apply getNumCalls_nil.
  - subst.
    rewrite getNumCalls_cons, IHSubsteps; simpl.
    inv HNeverCallBase.
    specialize (H0 _ HInRules); simpl in *.
    rewrite (action_noCalls H0 HAction); simpl.
    reflexivity.
  - subst.
    rewrite getNumCalls_cons, IHSubsteps; simpl.
    inv HNeverCallBase.
    specialize (H1 _ HInMeths argV).
    rewrite (action_noCalls H1 HAction); simpl.
    reflexivity.
Qed.

Lemma Step_NeverCall_getNumCalls_0 (m : Mod)(o : RegsT)(l : list FullLabel)
      (HNeverCall : NeverCallMod m) :
  Step m o l ->
  forall (f : MethT), getNumCalls f l = 0%Z.
Proof.
  induction 1; simpl; intros.
  - inv HNeverCall.
    rewrite (Substeps_NeverCall_getNumCalls_0 HNCBaseModule HSubsteps).
    reflexivity.
  - inv HNeverCall.
    rewrite IHStep; auto.
  - subst.
    inv HNeverCall.
    rewrite getNumCalls_app, IHStep1, IHStep2; auto.
Qed.

Lemma distributeHide_TraceInclusion (m1 m2 : Mod) (h : string)
      (HNeverCall : NeverCallMod m1):
  ~ In h (map fst (getAllMethods m1)) ->
  TraceInclusion (HideMeth (ConcatMod m1 m2) h)
                 (ConcatMod m1 (HideMeth m2 h)).
Proof.
  intros.
  apply TraceInclusion'_TraceInclusion, StrongTI'_TI'.
  unfold StrongTraceInclusion'.
  intros.
  induction H0; subst.
  - exists nil; split;[|apply WeakInclusionsRefl].
    econstructor; eauto.
  - dest.
    exists (l::x).
    split;[|constructor; [assumption|apply WeakInclusionRefl]].
    econstructor 2; eauto.
    clear - HStep HNeverCall H.
    inv HStep.
    inv HStep0.
    econstructor 3; eauto.
    + econstructor 2; eauto.
      intros; simpl in *.
      rewrite map_app, in_app_iff in *.
      specialize (HHidden (or_intror H0) v).
      unfold getListFullLabel_diff in *.
      rewrite getNumExecs_app, getNumCalls_app in *.
      rewrite (Step_NeverCall_getNumCalls_0 HNeverCall HStep1) in *.
      clear - HStep1 HStep2 HHidden HNeverCall H H0.
      rewrite (NotInDef_ZeroExecs_Step (m:=m1)(o:=o1)(ls:=l1) (h, v)) in *; auto.
    + unfold MatchingExecCalls_Concat in *; intros; simpl in *.
      split; [|eapply HMatching1; eauto].
      intro; apply H0.
      rewrite (Step_NeverCall_getNumCalls_0 HNeverCall HStep1) in *.
      reflexivity.
Qed.

Lemma distributeHides_TraceInclusion (m1 m2 : Mod) (hl : list string)
      (HNeverCall : NeverCallMod m1) :
  (forall h, In h hl -> ~In h (map fst (getAllMethods m1))) ->
  TraceInclusion (createHideMod (ConcatMod m1 m2) hl)
                 (ConcatMod m1 (createHideMod m2 hl)).
Proof.
  induction hl; simpl; intros.
  - apply TraceInclusion_refl.
  - assert (forall h : string, In h hl -> ~ In h (map fst (getAllMethods m1))) as P0;
      [intros; apply (H _ (or_intror H0))|].
    specialize (IHhl P0).
    apply TraceInclusion_TraceInclusion' in IHhl.
    specialize (TraceInclusion'_HideMeth (s:=a) IHhl) as P1.
    apply TraceInclusion'_TraceInclusion in P1.
    specialize (H a (or_introl eq_refl)).
    specialize (distributeHide_TraceInclusion HNeverCall H (m2:=(createHideMod m2 hl))) as P2.
    eauto using TraceInclusion_trans.
Qed.

Lemma createHides_perm_TraceInclusion (m : Mod) (hl1 hl2: list string):
  hl1 [=] hl2 ->
  TraceInclusion (createHideMod m hl1) (createHideMod m hl2).
Proof.
  induction 1.
  - apply TraceInclusion_refl.
  - simpl.
    apply TraceInclusion'_TraceInclusion, TraceInclusion'_HideMeth,
    TraceInclusion_TraceInclusion'; assumption.
  - simpl.
    apply TraceInclusion'_TraceInclusion, StrongTI'_TI'.
    unfold StrongTraceInclusion'; intros.
    exists ls; split;[|apply WeakInclusionsRefl].
    induction H.
    + econstructor 1; auto.
    + econstructor 2; eauto.
      clear - HStep.
      inv HStep.
      inv HStep0.
      constructor; auto.
      constructor; auto.
  - eauto using TraceInclusion_trans.
Qed.
    
Lemma distributeHides_app_TraceInclusion (m1 m2 : Mod) (hl1 hl2 : list string)
      (HNeverCall : NeverCallMod m1) :
  (forall h, In h hl1 -> ~In h (map fst (getAllMethods m1))) ->
  TraceInclusion (createHideMod (ConcatMod m1 m2) (hl1++hl2))
                 (createHideMod (ConcatMod m1 (createHideMod m2 hl1)) hl2).
Proof.
  intros.
  induction hl2; simpl; [rewrite app_nil_r|].
  - apply distributeHides_TraceInclusion; auto.
  - apply TraceInclusion_TraceInclusion' in IHhl2.
    specialize (TraceInclusion'_HideMeth (s:=a) IHhl2) as P1.
    specialize (createHides_perm_TraceInclusion
                  (ConcatMod m1 m2)
                  (Permutation_sym (Permutation_middle hl1 hl2 a))) as P2;
      simpl in *.
    apply TraceInclusion'_TraceInclusion in P1.
    eauto using TraceInclusion_trans.
Qed.

Lemma factorHideWf (m1 m2 : Mod) (h : string) (HNeverCall : NeverCallMod m1):
  WfMod (ConcatMod m1 (HideMeth m2 h)) ->
  WfMod (HideMeth (ConcatMod m1 m2) h) /\
  ~ In h (map fst (getAllMethods m1)).
Proof.
  intros.
  inv H.
  split.
  - constructor; simpl; inv HWf2.
    + rewrite map_app, in_app_iff.
      right; assumption.
    + constructor; auto.
      clear - WfConcat1 HNeverCall.
      inv WfConcat1; constructor; intros.
      * induction HNeverCall; simpl in *; eauto.
        -- inv HNCBaseModule.
           specialize (H _ H1).
           specialize (H2 _ H1).
           clear - H H2.
           induction H; inv H2; EqDep_subst; econstructor; eauto.
           tauto.
        -- rewrite in_app_iff in *.
           destruct H1.
           ++ apply IHHNeverCall1; intros; eauto;
                [eapply H| eapply H0];rewrite in_app_iff; left; assumption.
           ++ apply IHHNeverCall2; intros; eauto;
                [eapply H| eapply H0];rewrite in_app_iff; right; assumption.
      * induction HNeverCall; simpl in *; eauto.
        -- inv HNCBaseModule.
           specialize (H0 _ H1 v).
           specialize (H3 _ H1 v).
           clear - H0 H3.
           induction H0; inv H3; EqDep_subst; econstructor; eauto.
           tauto.
        -- rewrite in_app_iff in *.
           destruct H1.
           ++ apply IHHNeverCall1; intros; eauto;
                [eapply H| eapply H0];rewrite in_app_iff; left; assumption.
           ++ apply IHHNeverCall2; intros; eauto;
                [eapply H| eapply H0];rewrite in_app_iff; right; assumption.
  - intro.
    inv HWf2.
    simpl in *.
    clear - HDisjMeths H HHideWf.
    specialize (HDisjMeths h); firstorder.
Qed.

Lemma factorHidesWf (m1 m2 : Mod) (hl1 hl2: list string)
      (HNeverCall : NeverCallMod m1):
  WfMod (createHideMod (ConcatMod m1 (createHideMod m2 hl1)) hl2) ->
  WfMod (createHideMod (ConcatMod m1 m2) (hl1++hl2)) /\
  (forall h, In h hl1 -> ~ In h (map fst (getAllMethods m1))).
Proof.
  induction hl1; simpl in *; auto.
  intros.
  rewrite WfMod_createHideMod in H; dest; split; intros;[constructor|].
  - rewrite getAllMethods_createHideMod; simpl in *.
    rewrite map_app, in_app_iff, getAllMethods_createHideMod in *.
    inv H0; inv HWf2.
    rewrite getAllMethods_createHideMod in *.
    right; assumption.
  - specialize (factorHideWf HNeverCall H0) as P0; dest.
    eapply IHhl1.
    rewrite WfMod_createHideMod; split; auto.
    inv H1; assumption.
  - destruct H1; subst.
    + inv H0; inv HWf2.
      rewrite getAllMethods_createHideMod in *.
      specialize (HDisjMeths h); simpl in *; rewrite getAllMethods_createHideMod in *.
      clear - HHideWf HDisjMeths; firstorder.
    + eapply IHhl1; auto.
      rewrite WfMod_createHideMod; split; auto.
      specialize (factorHideWf HNeverCall H0) as P0; dest.
      inv H2; assumption.
Qed.

Lemma factorHide_TraceInclusion (m1 m2 : Mod) (h : string)
      (HNeverCall : NeverCallMod m1):
  ~In h (map fst (getAllMethods m1)) ->
  TraceInclusion (ConcatMod m1 (HideMeth m2 h) ) (HideMeth (ConcatMod m1 m2) h).
Proof.
  intros.
  apply TraceInclusion'_TraceInclusion, StrongTI'_TI'.
  repeat intro.
  induction H0; subst; simpl in *.
  - exists nil; split;[econstructor; eauto|apply WeakInclusionsRefl].
  - dest.
    exists (l::x); split.
    + econstructor 2; eauto.
      econstructor 2; inv HStep.
      * inv HStep2.
        econstructor 3; eauto.
        clear - HMatching1 HNeverCall.
        unfold MatchingExecCalls_Concat in *.
        intros; simpl in *; split;[|eapply HMatching1; eauto].
        specialize (HMatching1 _ H H0); dest.
        apply Decidable.not_or in H1; dest; assumption.
      * intros; inv HStep2.
        unfold MatchingExecCalls_Concat, getListFullLabel_diff in *; simpl in *.
        rewrite map_app, in_app_iff in *; destruct H3;[tauto|specialize (HHidden H3 v)].
        rewrite getNumExecs_app, getNumCalls_app.
        specialize (Step_NeverCall_getNumCalls_0 HNeverCall HStep1 (h, v)) as P0.
        specialize (NotInDef_ZeroExecs_Step (h, v) H HStep1) as P1.
        clear - HHidden P0 P1; omega.
    + constructor;[assumption |apply WeakInclusionRefl].
Qed.

Lemma factorHides_TraceInclusion1 (m1 m2 : Mod) (hl : list string)
      (HNeverCall : NeverCallMod m1):
  (forall h, In h hl -> ~In h (map fst (getAllMethods m1))) ->
  TraceInclusion (ConcatMod m1 (createHideMod m2 hl))
                 (createHideMod (ConcatMod m1 m2) hl).
Proof.
  induction hl; simpl; intros.
  - apply TraceInclusion_refl.
  - assert (forall h : string, In h hl -> ~ In h (map fst (getAllMethods m1))) as TMP.
    {intros; eapply H; right; assumption. }
    specialize (IHhl TMP); clear TMP.
    specialize (TraceInclusion_HideMeth IHhl (s:=a)) as P1.
    specialize (factorHide_TraceInclusion (m2:=createHideMod m2 hl)
                                          HNeverCall (H _ (or_introl eq_refl))) as P2.
    eauto using TraceInclusion_trans.
Qed.

Lemma factorHides_TraceInclusion_app (m1 m2 : Mod) (hl1 hl2 : list string)
      (HNeverCall : NeverCallMod m1):
  (forall h, In h hl1 -> ~In h (map fst (getAllMethods m1))) ->
  TraceInclusion (createHideMod (ConcatMod m1 (createHideMod m2 hl1)) hl2)
                 (createHideMod (ConcatMod m1 m2) (hl1++hl2)).
Proof.
  induction hl2; simpl;[rewrite app_nil_r|].
  - intros.
    apply factorHides_TraceInclusion1; auto.
  - intros; specialize (TraceInclusion_HideMeth (IHhl2 H) (s:=a)) as P0.
    specialize (createHides_perm_TraceInclusion
                  (ConcatMod m1 m2) (Permutation_middle hl1 hl2 a)) as P1.
    simpl in *.
    eauto using TraceInclusion_trans.
Qed.

Lemma removeMeth_neg (m : BaseModule) (f g : string):
  (g <> f /\ In f (map fst (getMethods m))) <->
  In f (map fst (getMethods (removeMeth m g))).
Proof.
  intros.
  split; intros.
  - simpl in *.
    rewrite in_map_iff in *; dest.
    exists x; split; subst; auto.
    rewrite filter_In; split; auto.
    destruct string_dec; simpl in *; auto.
  - split; simpl in *; rewrite in_map_iff in *; dest.
    + rewrite filter_In in H0; dest.
      destruct string_dec; subst; auto.
      discriminate.
    + exists x; split; auto; rewrite filter_In in *; dest; assumption.
Qed.

Lemma removeHides_neg (m : BaseModule) (l : list string):
  forall f, In f (map fst (getMethods m)) /\ ~ In f l <->
            In f (map fst (getMethods (removeHides m l))).
Proof.
  intros; split; dest.
  - intros; induction l; dest.
    + simpl in *; rewrite (filter_true_list); auto.
    + rewrite removeMeth_removeHides_cons.
      simpl in H0; apply Decidable.not_or in H0; dest.
      rewrite <- removeMeth_neg; eauto.
  - intros; split; auto; induction l; auto.
    + simpl in H; rewrite in_map_iff in *; dest.
      rewrite filter_true_list in H0; auto.
      exists x; split; auto.
    + rewrite removeMeth_removeHides_cons in H.
      rewrite <- removeMeth_neg in H; dest; auto.
    + rewrite removeMeth_removeHides_cons in H.
      rewrite <- removeMeth_neg in H; dest.
      intro; inv H1; auto.
      apply IHl; assumption. 
Qed.

Lemma createHideMod_createHide_BaseModule (m : BaseModule) (l : list string) :
  (createHide m l) = (createHideMod m l).
Proof.
  induction l; simpl in *; auto.
  rewrite IHl; reflexivity.
Qed.

Lemma Concat_removeHide (m1 : Mod) {m2 : BaseModule} (hl1 hl2 : list string)
      (NoSelfCall : NoSelfCallBaseModule m2):
  WfMod (createHideMod (ConcatMod m1 (createHideMod m2 hl1)) hl2) ->
  TraceInclusion (createHideMod (ConcatMod m1 (createHideMod m2 hl1)) hl2)
                 (createHideMod (ConcatMod m1 (removeHides m2 hl1)) hl2).
Proof.
  intros.
  rewrite WfMod_createHideMod in H; dest.
  apply TraceInclusion_createHideMod.
  apply ModularSubstitution; auto.
  - intros; apply iff_refl.
  - intros; split; intros; split; dest; auto.
    + apply removeHides_neg; split.
      * rewrite getAllMethods_createHideMod in *; assumption.
      * rewrite getHidden_createHideMod, in_app_iff in *; apply Decidable.not_or in H2;
          dest; assumption.
    + assert (getAllMethods (removeHides m2 hl1) = getMethods (removeHides m2 hl1)) as P0;
        auto; rewrite P0, <- removeHides_neg, getAllMethods_createHideMod in *; dest; assumption.
    + assert (getAllMethods (removeHides m2 hl1) = getMethods (removeHides m2 hl1)) as P0;
        auto; rewrite P0, <- removeHides_neg, getHidden_createHideMod, app_nil_r in *; dest;
          assumption.
  - inv H0; constructor; simpl in *; auto.
    + rewrite getAllRegisters_createHideMod in *; assumption.
    + rewrite getAllRules_createHideMod in *; assumption.
    + repeat intro; specialize (HDisjMeths k).
      destruct HDisjMeths; auto.
      right; intro; apply H0.
      rewrite in_map_iff in *; dest; rewrite filter_In in *; dest.
      exists x; split; auto; rewrite getAllMethods_createHideMod.
      assumption.
    + constructor; apply removeHidesWf.
      rewrite WfMod_createHideMod in HWf2; dest; inv H1.
      assumption.
    + inv WfConcat1; constructor.
      * intros; specialize (H0 _ H2).
        clear - H0.
        induction H0; econstructor; eauto.
      * intros; specialize (H1 _ H2 v).
        clear - H1.
        induction H1; econstructor; eauto.
    + inv WfConcat2; constructor.
      * intros; simpl in *.
        rewrite getAllRules_createHideMod in *.
        specialize (H0 _ H2); assumption.
      * intros; simpl in *.
        rewrite filter_In in *; dest.
        rewrite getAllMethods_createHideMod in *.
        specialize (H1 _ H2 v); assumption.
  - apply TraceInclusion_refl.
  - inv H0.
    rewrite WfMod_createHideMod in *; dest.
    inv H1.
    specialize (createHide_removeHides_TraceInclusion (Build_BaseModuleWf HWfBaseModule)) as P0.
    simpl in *.
    rewrite <- createHideMod_createHide_BaseModule.
    apply P0; auto.
Qed.

Lemma removeMeth_removes (m : BaseModule) (f : string):
  ~In f (map fst (getMethods (removeMeth m f))).
Proof.
  rewrite in_map_iff; intro; dest.
  simpl in *; rewrite filter_In in *; dest.
  destruct string_dec; simpl in *; auto.
  discriminate.
Qed.

Lemma removeHides_removes (m : BaseModule) (hl : list string):
  forall f, In f hl -> ~In f (map fst (getMethods (removeHides m hl))).
Proof.
  intros.
  induction hl.
  - simpl in *; tauto.
  - rewrite removeMeth_removeHides_cons.
    inv H.
    + apply removeMeth_removes.
    + specialize (IHhl H0).
      intro; apply IHhl.
      rewrite in_map_iff in *; dest; simpl in *.
      exists x; split; auto.
      repeat rewrite filter_In in *; dest; split; auto.
Qed.

Lemma Concat_createHide (m1 : Mod) {m2 : BaseModule} (hl1 hl2 : list string)
      (NoSelfCall : NoSelfCallBaseModule m2):
  WfMod (createHideMod (ConcatMod m1 (createHideMod m2 hl1)) hl2) ->
  TraceInclusion (createHideMod (ConcatMod m1 (removeHides m2 hl1)) hl2)
                 (createHideMod (ConcatMod m1 (createHideMod m2 hl1)) hl2).
Proof.
  intros.
  rewrite WfMod_createHideMod in H; dest.
  apply TraceInclusion_createHideMod.
  apply ModularSubstitution; auto.
  - intros; apply iff_refl.
  - intro; split; intro; split; dest; auto.
    + assert (getAllMethods (removeHides m2 hl1) = getMethods (removeHides m2 hl1)) as P0;
        auto; rewrite P0, <- removeHides_neg, getAllMethods_createHideMod in *; dest; assumption.
    + assert (getAllMethods (removeHides m2 hl1) = getMethods (removeHides m2 hl1)) as P0;
        auto; rewrite P0, <- removeHides_neg, getHidden_createHideMod, app_nil_r in *; dest;
          assumption.
    + assert (getAllMethods (removeHides m2 hl1) = getMethods (removeHides m2 hl1)) as P0;
        auto; rewrite P0, <- removeHides_neg, getAllMethods_createHideMod in *; split; auto.
      rewrite getHidden_createHideMod, app_nil_r in H2; assumption.
  - inv H0; constructor; simpl in *; auto.
    + rewrite getAllRegisters_createHideMod in *; assumption.
    + rewrite getAllRules_createHideMod in *; assumption.
    + repeat intro; specialize (HDisjMeths k).
      destruct HDisjMeths; auto.
      right; intro; apply H0.
      rewrite in_map_iff in *; dest; rewrite filter_In in *; dest.
      exists x; split; auto; rewrite getAllMethods_createHideMod.
      assumption.
    + constructor; apply removeHidesWf.
      rewrite WfMod_createHideMod in HWf2; dest; inv H1.
      assumption.
    + inv WfConcat1; constructor.
      * intros; specialize (H0 _ H2).
        clear - H0.
        induction H0; econstructor; eauto.
      * intros; specialize (H1 _ H2 v).
        clear - H1.
        induction H1; econstructor; eauto.
    + inv WfConcat2; constructor.
      * intros; simpl in *.
        rewrite getAllRules_createHideMod in *.
        specialize (H0 _ H2); assumption.
      * intros; simpl in *.
        rewrite filter_In in *; dest.
        rewrite getAllMethods_createHideMod in *.
        specialize (H1 _ H2 v); assumption.
  - apply TraceInclusion_refl.
  - inv H0.
    rewrite WfMod_createHideMod in *; dest.
    inv H1.
    specialize (removeHides_createHide_TraceInclusion
                  (m := (Build_BaseModuleWf HWfBaseModule)) H0) as P0.
    simpl in *.
    rewrite <- createHideMod_createHide_BaseModule.
    apply P0; auto.
Qed.

Lemma RegFileBase_noCalls (rf : RegFileBase) :
  NeverCallMod (BaseRegFile rf).
Proof.
  constructor; split; simpl; intros;[tauto|].
  unfold getRegFileMethods in *.
  destruct rf; simpl in *.
  destruct H; subst; simpl in *.
  - destruct rfIsWrMask; repeat econstructor; eauto.
  - destruct rfRead; induction reads; simpl in *.
    + tauto.
    + destruct H; subst.
      * repeat econstructor.
      * eauto.
    + unfold readSyncRegFile in *.
      destruct isAddr; simpl in *;tauto.
    + unfold readSyncRegFile in *; simpl in *.
      destruct isAddr.
      * simpl in H; destruct H; subst.
        -- repeat econstructor.
        -- repeat rewrite in_app_iff in *.
           destruct H.
           ++ apply IHreads; auto.
           ++ inv H; [repeat econstructor| eauto].
      * inv H.
        -- repeat econstructor.
        -- rewrite in_app_iff in *.
           destruct H0; eauto.
           inv H;[repeat econstructor|eauto].
Qed.

Corollary mergeFile_noCalls (rfl : list RegFileBase) :
  NeverCallMod (mergeSeparatedBaseFile rfl).
Proof.
  induction rfl.
  - simpl.
    constructor; split; simpl; intros; tauto.
  - simpl.
    constructor; auto.
    apply RegFileBase_noCalls.
Qed.

Lemma WfConcatActionT_inlineSingle_Meth {k : Kind} (f: DefMethT) (a : ActionT type k) m:
  (forall v, WfConcatActionT (projT2 (snd f) type v) m) ->
  WfConcatActionT a m ->
  WfConcatActionT (inlineSingle f a) m.
Proof.
  intros.
  induction a; unfold inlineSingle; inv H0; EqDep_subst; try econstructor; eauto.
  destruct string_dec;[destruct Signature_dec|]; subst; simpl in *; econstructor; eauto.
  econstructor; eauto.
Qed.

Lemma WfConcatActionT_inlineSingle_Rule_map rule (f : DefMethT) rules m:
  (forall v, WfConcatActionT (projT2 (snd f) type v) m) ->
  In rule (map (inlineSingle_Rule f) rules) ->
  (forall rule', In rule' rules ->
                 WfConcatActionT (snd rule' type) m) ->
  WfConcatActionT (snd rule type) m.
Proof.
  intros.
  induction rules; simpl in *;[tauto|].
  destruct H0; subst; eauto.
  specialize (H1 _ (or_introl (eq_refl _))).
  unfold inlineSingle_Rule; destruct a, f; simpl in *.
  eapply WfConcatActionT_inlineSingle_Meth; eauto.
Qed.

Lemma WfConcatActionT_inlineSingle_Meth_map meth (f : DefMethT) meths m:
  (forall v, WfConcatActionT (projT2 (snd f) type v) m) ->
  In meth (map (inlineSingle_Meth f) meths) ->
  (forall meth', In meth' meths ->
                 (forall v', WfConcatActionT (projT2 (snd meth') type v') m)) ->
  (forall v, WfConcatActionT (projT2 (snd meth) type v) m).
Proof.
  intros.
  induction meths; simpl in *;[tauto|].
  destruct H0; subst; eauto.
  specialize (H1 _ (or_introl (eq_refl _))).
  unfold inlineSingle_Meth; destruct a, f; simpl in *.
  destruct (string_dec s1 s), s0; subst; simpl; eauto.
  eapply WfConcatActionT_inlineSingle_Meth; eauto.
Qed.

Lemma WfConcatActionT_inlineSingle_Rule_pos rule meths m xs:
    (forall (f : DefMethT), In f meths ->
                            (forall v, WfConcatActionT (projT2 (snd f) type v) m)) ->
    forall (rules : list RuleT),
      (forall rule', In rule' rules ->
                     WfConcatActionT (snd rule' type) m) ->
      In rule (fold_left
                 (fun (newRules : list RuleT) (n : nat) =>
                    inlineSingle_Rules_pos meths n newRules) xs rules) ->
      WfConcatActionT (snd rule type) m.
Proof.
  induction xs; simpl; intros; simpl in *; auto.
  eapply IHxs;[ | | apply H1]; eauto.
  unfold inlineSingle_Rules_pos in *.
  case_eq (nth_error meths a); intros; eauto.
  rewrite H2 in H1.
  eapply WfConcatActionT_inlineSingle_Rule_map; eauto.
  apply H.
  apply (nth_error_In _ _ H2).
Qed.

Lemma WfConcatActionT_inlineSingle_Meth_pos meth m xs:
  forall meths,
    (forall (f : DefMethT), In f meths ->
                            (forall v, WfConcatActionT (projT2 (snd f) type v) m)) ->
    In meth (fold_left inlineSingle_Meths_pos xs meths) ->
    (forall v, WfConcatActionT (projT2 (snd meth) type v) m).
Proof.
  induction xs; simpl; intros; simpl in *; auto.
  eapply IHxs;[|apply H0].
  intros.
  unfold inlineSingle_Meths_pos in H1.
  case_eq (nth_error meths a); intros.
  - rewrite H2 in H1.
    eapply WfConcatActionT_inlineSingle_Meth_map; eauto.
    eapply H.
    apply (nth_error_In _ _ H2).
  - rewrite H2 in H1.
    apply H; auto.
Qed.

Corollary WfConcatActionT_inlineAll_Meths meth meths m:
    (forall (f : DefMethT), In f meths ->
                            (forall v, WfConcatActionT (projT2 (snd f) type v) m)) ->
    In meth (inlineAll_Meths meths) ->
    (forall v, WfConcatActionT (projT2 (snd meth) type v) m).
Proof.
  unfold inlineAll_Meths.
  eauto using WfConcatActionT_inlineSingle_Meth_pos.
Qed.

Corollary WfConcatActionT_inlineAll_Rules rule (rules : list RuleT) meths m:
    (forall (f : DefMethT), In f meths ->
                            (forall v, WfConcatActionT (projT2 (snd f) type v) m)) ->
    (forall rule', In rule' rules ->
                   WfConcatActionT (snd rule' type) m) ->
    In rule (inlineAll_Rules meths rules) ->
    WfConcatActionT (snd rule type) m.
Proof.
  unfold inlineAll_Rules.
  eauto using WfConcatActionT_inlineSingle_Rule_pos.
Qed.

Lemma mergeSeparatedDistributed_Wf (m : ModWf):
  let t := separateModHides m in
  WfMod (createHideMod (ConcatMod (mergeSeparatedBaseFile (fst (snd t))) (snd (snd t))) (fst t)).
Proof.
  specialize (WfMod_merge (wfMod m)) as P0.
  unfold mergeSeparatedMod, separateMod in P0; simpl in *.
  unfold separateModHides, separateMod.
  destruct separateBaseMod; simpl in *.
  specialize (separate_calls_by_filter
                (getHidden m)
                (hiddenByBase (map BaseRegFile l))) as P1.
  rewrite Permutation_app_comm in P1.
  apply (WfMod_perm _ P1) in P0.
  apply distributeHidesWf in P0.
  - rewrite WfMod_createHideMod in *; dest; split.
    + clear - H; simpl in *.
      unfold flatten_inline_everything.
      rewrite createHide_Meths.
      unfold inlineAll_All_mod; simpl.
      rewrite map_app, <-SameKeys_inlineAll_Meths, getAllMethods_createHideMod in *.
      assumption.
    + clear - H0.
      inv H0; constructor; auto.
      * rewrite createHide_Regs, getAllRegisters_createHideMod in *; assumption.
      * rewrite createHide_Rules, getAllRules_createHideMod in *; simpl.
        intro k; destruct (HDisjRules k); auto; right.
        rewrite <- SameKeys_inlineAll_Rules; assumption.
      * rewrite createHide_Meths, getAllMethods_createHideMod in *; simpl.
        intro k; destruct (HDisjMeths k); auto; right.
        rewrite <- SameKeys_inlineAll_Meths; assumption.
      * rewrite WfMod_createHideMod in HWf2; dest.
        rewrite WfMod_createHide; split; auto.
        -- unfold inlineAll_All_mod; simpl.
           rewrite <- SameKeys_inlineAll_Meths; assumption.
        -- unfold inlineAll_All_mod; constructor.
           specialize (WfMod_WfBaseMod_flat H0) as P0.
           unfold getFlat in P0.
           apply (WfBaseMod_inlineAll_All P0).
      * clear - WfConcat1.
        assert (getHidden (createHide (inlineAll_All_mod (mergeSeparatedBaseMod l0))
                                      (filter (complement (hiddenByBase (map BaseRegFile l)))
                                              (getHidden m)))
                =
                getHidden (createHideMod
                             (mergeSeparatedBaseMod l0)
                             (filter (complement (hiddenByBase (map BaseRegFile l)))
                                     (getHidden m)))
               ) as P0.
        { rewrite createHide_hides, getHidden_createHideMod, mergeSeparatedBaseMod_noHides,
          app_nil_r; reflexivity. }
        inv WfConcat1; split; intros.
        -- specialize (H _ H1).
           clear - H P0.
           induction H; econstructor; eauto.
           rewrite P0; assumption.
        -- specialize (H0 _ H1 v).
           clear - H0 P0.
           induction H0; econstructor; eauto.
           rewrite P0; assumption.
      * clear - WfConcat2.
        inv WfConcat2; split; intros.
        -- rewrite createHide_Rules in H1; simpl in H1.
           rewrite getAllRules_createHideMod in *.
           rewrite getAllMethods_createHideMod in *.
           assert
             (forall meth,
                 In meth (inlineAll_Meths (getAllMethods (mergeSeparatedBaseMod l0))) ->
                 forall v : type (fst (projT1 (snd meth))),
                   WfConcatActionT (projT2 (snd meth) type v) (mergeSeparatedBaseFile l)).
           { intros. eapply WfConcatActionT_inlineAll_Meths; eauto. }
           clear H0.
           eapply WfConcatActionT_inlineAll_Rules; eauto.
        -- rewrite createHide_Meths in H1; simpl in H1.
           rewrite getAllMethods_createHideMod in *.
           eapply  WfConcatActionT_inlineAll_Meths; eauto.
  - apply mergeFile_noCalls.
  - intros.
    clear - H.
    unfold hiddenByBase, hiddenBy in *.
    rewrite filter_In in *; dest.
    destruct in_dec; simpl in *;[discriminate|].
    intro; apply n; clear n H0 H.
    induction l; simpl in *; auto.
    unfold getAllBaseMethods; simpl.
    rewrite map_app, in_app_iff in *.
    destruct H1;[left|right];auto.
Qed.

Definition mergeSeparatedDistributed_ModWf (m : ModWf) : ModWf :=
  Build_ModWf (mergeSeparatedDistributed_Wf m).

Lemma ConcatMod_CreateHide_RemoveHides (m1 : Mod) (m2 : BaseModule) (hl1 hl2 : list string):
  (forall h, ~In h hl1 \/ ~In h hl2) ->
  WfMod (createHideMod (ConcatMod m1 (createHide m2 hl1)) hl2)->
  WfMod (createHideMod (ConcatMod m1 (removeHides m2 hl1)) hl2).
Proof.
  intros.
  rewrite WfMod_createHideMod in *; split; dest.
  - repeat intro.
    specialize (H0 _ H2).
    simpl in *; rewrite map_app, in_app_iff in *.
    destruct H0; auto.
    right.
    rewrite createHide_Meths in *.
    rewrite in_map_iff in *; dest.
    exists x0; split; auto.
    rewrite filter_In; split; auto.
    destruct in_dec; simpl in *; auto.
    exfalso.
    clear - H H0 H2 i; specialize (H x); subst.
    firstorder. 
  - clear - H1.
    inv H1; rewrite createHide_Rules, createHide_Meths, createHide_Regs in *.
    constructor; simpl; auto.
    + intro; destruct (HDisjMeths k); auto.
      clear - H; right; rewrite in_map_iff in *; intro; apply H; dest.
      rewrite filter_In in *; dest.
      exists x; auto.
    + rewrite WfMod_createHide in HWf2; dest.
      clear - H0.
      inv H0; constructor.
      apply removeHidesWf; auto.
    + unfold WfConcat in *; dest; repeat split.
      * clear - H1; intros.
        specialize (H1 _ H).
        induction H1; econstructor; eauto.
      * clear - H2; intros.
        specialize (H2 _ H v).
        induction H2; econstructor; eauto.
    + unfold WfConcat in *; dest; repeat split.
      * clear - H; intros.
        rewrite createHide_Rules in *.
        simpl in *.
        specialize (H _ H0).
        induction H; econstructor; eauto.
      * clear - H0; intros.
        rewrite createHide_Meths in *.
        simpl in *.
        rewrite filter_In in *; dest.
        specialize (H0 _ H v).
        induction H0; econstructor; eauto.
Qed.

Lemma mergeSeparatedRemoved_Wf (m : ModWf):
  let t := separateModRemove m in
  WfMod (createHideMod (ConcatMod (mergeSeparatedBaseFile (fst (snd t))) (snd (snd t))) (fst t)).
Proof.
  intros.
  specialize (mergeSeparatedDistributed_Wf m); intros.
  unfold separateModHides, separateModRemove in *.
  unfold t; destruct separateMod, p; simpl in *.
  apply ConcatMod_CreateHide_RemoveHides; auto.
  clear.
  specialize (filter_complement_disj string_dec (hiddenByBase (map BaseRegFile l0)) l) as P0.
  intro h; specialize (P0 h); destruct P0; auto.
Qed.

Definition mergeSeparatedRemoved_ModWf (m : ModWf) : ModWf :=
  Build_ModWf (mergeSeparatedRemoved_Wf m).

Theorem mergeSeparatedRemoved_TraceInclusion_l (m : ModWf):
  baseNoSelfCalls m ->
  TraceInclusion (mergeSeparatedRemoved_ModWf m) m.
Proof.
  specialize (WfMod_merge (wfMod m)) as P0.
  specialize (TraceInclusion_Merge_r m) as P1; simpl in *;
    unfold mergeSeparatedMod in *.
  specialize (mergeSeparatedDistributed_Wf m) as P2.
  intros; simpl; unfold separateModRemove, separateModHides, baseNoSelfCalls in *.
  destruct separateMod, p; simpl in *.
  rewrite createHideMod_createHide_BaseModule in P2.
  specialize (Concat_createHide _ _ _ H P2) as P3.
  specialize (mergeFile_noCalls l0) as P4.
  assert (forall h, In h (filter (complement (hiddenByBase (map BaseRegFile l0))) l) ->
                    ~ In h (map fst (getAllMethods (mergeSeparatedBaseFile l0)))) as P5.
  { repeat intro.
    rewrite filter_In in H0; dest.
    unfold hiddenByBase, getAllBaseMethods, hiddenBy in H2.
    destruct in_dec; [discriminate|].
    clear - n H1.
    induction l0; simpl in *; auto.
    rewrite map_app, in_app_iff in *.
    apply Decidable.not_or in n; dest.
    destruct H1; auto.
  }
  specialize (factorHides_TraceInclusion_app
                (inlineAll_All_mod (mergeSeparatedBaseMod l1))
                _ (filter (hiddenByBase (map BaseRegFile l0)) l) P4 P5) as P6.
  specialize (createHides_perm_TraceInclusion
                (ConcatMod (mergeSeparatedBaseFile l0)
                           (inlineAll_All_mod (mergeSeparatedBaseMod l1)))
                (Permutation_sym
                   (Permutation_trans
                      (separate_calls_by_filter l (hiddenByBase (map BaseRegFile l0)))
                      (Permutation_app_comm _ _)))) as P7.
  assert (TraceInclusion
            (createHideMod
               (ConcatMod (mergeSeparatedBaseFile l0)
                          (inlineAll_All_mod (mergeSeparatedBaseMod l1))) l)
            (createHideMod
               (ConcatMod (mergeSeparatedBaseFile l0)
                          (mergeSeparatedBaseMod l1)) l)).
  { apply TraceInclusion_createHideMod.
    apply ModularSubstitution.
    - reflexivity.
    - simpl; rewrite <-SameKeys_inlineAll_Meths, mergeSeparatedBaseMod_noHides.
      reflexivity.
    - rewrite WfMod_createHideMod in P0; dest.
      inv H1.
      constructor; auto.
      + clear - HDisjRules.
        intro k; specialize (HDisjRules k); simpl.
        rewrite <-SameKeys_inlineAll_Rules.
        assumption.
      + clear - HDisjMeths.
        intro k; specialize (HDisjMeths k); simpl.
        rewrite <-SameKeys_inlineAll_Meths.
        assumption.
      + unfold inlineAll_All_mod.
        specialize (WfMod_WfBase_getFlat HWf2) as TMP2.
        unfold getFlat in TMP2.
        apply (TraceInclusion_inlineAll_pos TMP2).
      + clear - WfConcat1.
        unfold WfConcat in *; split; dest; intros.
        * specialize (H _ H1); induction H; econstructor; eauto.
        * specialize (H0 _ H1 v); induction H0; econstructor; eauto.
      + clear - WfConcat2.
        unfold WfConcat in *; split; dest; intros.
        * induction (snd rule type); econstructor; eauto.
          rewrite mergeSeparatedBaseFile_noHides; auto.
        * induction (projT2 (snd meth) type v); econstructor; eauto.
          rewrite mergeSeparatedBaseFile_noHides; auto.
    - rewrite WfMod_createHideMod in P0; dest.
      assumption.
    - apply TraceInclusion_refl.
    - unfold inlineAll_All_mod.
      rewrite WfMod_createHideMod in P0; dest.
      inv H1.
      specialize (TraceInclusion_inlineAll_pos_l (WfMod_WfBase_getFlat HWf2)) as TMP2; dest.
      specialize (TraceInclusion_flatten_l (Build_ModWf HWf2)) as TMP3; simpl in *.
      unfold flatten, getFlat in *.
      rewrite mergeSeparatedBaseMod_noHides in TMP3; simpl in *.
      eauto using TraceInclusion_trans.
  }
  eauto using TraceInclusion_trans.
Qed.

Theorem mergeSeparatedRemoved_TraceInclusion_r (m : ModWf):
  baseNoSelfCalls m ->
  TraceInclusion m (mergeSeparatedRemoved_ModWf m).
Proof.
  specialize (WfMod_merge (wfMod m)) as P0.
  specialize (TraceInclusion_Merge_l m) as P1; simpl in *;
    unfold mergeSeparatedMod in *.
  specialize (mergeSeparatedDistributed_Wf m) as P2.
  intros; simpl; unfold separateModRemove, separateModHides, baseNoSelfCalls in *.
  destruct separateMod, p; simpl in *.
  rewrite createHideMod_createHide_BaseModule in P2.
  specialize (Concat_removeHide _ _ _ H P2) as P3.
  specialize (mergeFile_noCalls l0) as P4.
  assert (forall h, In h (filter (complement (hiddenByBase (map BaseRegFile l0))) l) ->
                    ~ In h (map fst (getAllMethods (mergeSeparatedBaseFile l0)))) as P5.
  { repeat intro.
    rewrite filter_In in H0; dest.
    unfold hiddenByBase, getAllBaseMethods, hiddenBy in H2.
    destruct in_dec; [discriminate|].
    clear - n H1.
    induction l0; simpl in *; auto.
    rewrite map_app, in_app_iff in *.
    apply Decidable.not_or in n; dest.
    destruct H1; auto.
  }
  specialize (distributeHides_app_TraceInclusion
                (inlineAll_All_mod (mergeSeparatedBaseMod l1))
                _ (filter (hiddenByBase (map BaseRegFile l0)) l) P4 P5) as P6.
  specialize (createHides_perm_TraceInclusion
                (ConcatMod (mergeSeparatedBaseFile l0)
                           (inlineAll_All_mod (mergeSeparatedBaseMod l1)))
                (Permutation_trans
                   (separate_calls_by_filter l (hiddenByBase (map BaseRegFile l0)))
                   (Permutation_app_comm _ _))) as P7.
  assert (TraceInclusion
            (createHideMod
               (ConcatMod (mergeSeparatedBaseFile l0)
                          (mergeSeparatedBaseMod l1)) l)
            (createHideMod
               (ConcatMod (mergeSeparatedBaseFile l0)
                          (inlineAll_All_mod (mergeSeparatedBaseMod l1))) l)).
  { apply TraceInclusion_createHideMod.
    apply ModularSubstitution.
    - reflexivity.
    - simpl; rewrite <-SameKeys_inlineAll_Meths, mergeSeparatedBaseMod_noHides.
      reflexivity.
    - rewrite WfMod_createHideMod in P0; dest.
      assumption.
    - rewrite WfMod_createHideMod in P0; dest.
      inv H1.
      constructor; auto.
      + clear - HDisjRules.
        intro k; specialize (HDisjRules k); simpl.
        rewrite <-SameKeys_inlineAll_Rules.
        assumption.
      + clear - HDisjMeths.
        intro k; specialize (HDisjMeths k); simpl.
        rewrite <-SameKeys_inlineAll_Meths.
        assumption.
      + unfold inlineAll_All_mod.
        specialize (WfMod_WfBase_getFlat HWf2) as TMP2.
        unfold getFlat in TMP2.
        apply (TraceInclusion_inlineAll_pos TMP2).
      + clear - WfConcat1.
        unfold WfConcat in *; split; dest; intros.
        * specialize (H _ H1); induction H; econstructor; eauto.
        * specialize (H0 _ H1 v); induction H0; econstructor; eauto.
      + clear - WfConcat2.
        unfold WfConcat in *; split; dest; intros.
        * induction (snd rule type); econstructor; eauto.
          rewrite mergeSeparatedBaseFile_noHides; auto.
        * induction (projT2 (snd meth) type v); econstructor; eauto.
          rewrite mergeSeparatedBaseFile_noHides; auto.
    - apply TraceInclusion_refl.
    - unfold inlineAll_All_mod.
      rewrite WfMod_createHideMod in P0; dest.
      inv H1.
      specialize (TraceInclusion_inlineAll_pos (WfMod_WfBase_getFlat HWf2)) as TMP2; dest.
      specialize (TraceInclusion_flatten_r (Build_ModWf HWf2)) as TMP3; simpl in *.
      unfold flatten, getFlat in *.
      rewrite mergeSeparatedBaseMod_noHides in TMP3; simpl in *.
      eauto using TraceInclusion_trans.
  }
  eauto using TraceInclusion_trans.
Qed.
