Require Import Kami.Syntax.
Require Import Kami.Properties Kami.PProperties.
Import ListNotations.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.PermutEq.
Require Import RelationClasses Setoid Morphisms.


Section BaseModule.
  Variable m: BaseModule.
  Variable o: RegsT.

  Inductive PPlusSubsteps: RegsT -> list RuleOrMeth -> MethsT -> Prop :=
  | NilPPlusSubstep (HRegs: getKindAttr o [=] getKindAttr (getRegisters m)) : PPlusSubsteps nil nil nil
  | PPlusAddRule (HRegs: getKindAttr o [=] getKindAttr (getRegisters m))
            rn rb
            (HInRules: In (rn, rb) (getRules m))
            reads u cs
            (HPAction: PSemAction o (rb type) reads u cs WO)
            (HReadsGood: SubList (getKindAttr reads)
                                 (getKindAttr (getRegisters m)))
            (HUpdGood: SubList (getKindAttr u)
                               (getKindAttr (getRegisters m)))
            upds execs calls oldUpds oldExecs oldCalls
            (HUpds: upds [=] u ++ oldUpds)
            (HExecs: execs [=] Rle rn :: oldExecs)
            (HCalls: calls [=] cs ++ oldCalls)
            (HDisjRegs: DisjKey oldUpds u)
            (HNoRle: forall x, In x oldExecs -> match x with
                                                | Rle _ => False
                                                | _ => True
                                                end)
            (HNoCall: forall c, In c cs -> In c oldCalls -> False)
            (HPSubstep: PPlusSubsteps oldUpds oldExecs oldCalls):
      PPlusSubsteps upds execs calls
  | PPlusAddMeth (HRegs: getKindAttr o [=] getKindAttr (getRegisters m))
            fn fb
            (HInMeths: In (fn, fb) (getMethods m))
            reads u cs argV retV
            (HPAction: PSemAction o ((projT2 fb) type argV) reads u cs retV)
            (HReadsGood: SubList (getKindAttr reads)
                                 (getKindAttr (getRegisters m)))
            (HUpdGood: SubList (getKindAttr u)
                               (getKindAttr (getRegisters m)))
            upds execs calls oldUpds oldExecs oldCalls
            (HUpds: upds [=] u ++ oldUpds)
            (HExecs: execs [=] Meth (fn, existT _ _ (argV, retV)) :: oldExecs)
            (HCalls: calls [=] cs ++ oldCalls)
            (HDisjRegs: DisjKey oldUpds u)
            (HNoCall: forall c, In c cs -> In c oldCalls -> False)
            (HNoExec: In (Meth (fn, existT _ _ (argV, retV))) oldExecs -> False)
            (HPSubstep: PPlusSubsteps oldUpds oldExecs oldCalls):
      PPlusSubsteps upds execs calls.
  
  Definition getLabelUpds (ls: list FullLabel) :=
    concat (map (fun x => fst x) ls).
  
  Definition getLabelExecs (ls: list FullLabel) :=
    map (fun x => fst (snd x)) ls.
  
  Definition getLabelCalls (ls: list FullLabel) :=
    concat (map (fun x => (snd (snd x))) ls).
  
  Lemma PPlusSubsteps_PSubsteps:
    forall upds execs calls,
      PPlusSubsteps upds execs calls ->
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
        * clear - H3 H4 H5 HCalls HNoCall.
          apply HNoCall with (c := c); auto.
          rewrite H3.
          rewrite <- flat_map_concat_map.
          setoid_rewrite in_flat_map.
          unfold InCall in *; dest.
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
        * clear - H3 H4 H5 HCalls HNoCall.
          apply HNoCall with (c := c); auto.
          rewrite H3.
          rewrite <- flat_map_concat_map.
          setoid_rewrite in_flat_map.
          unfold InCall in *; dest.
          firstorder fail.
        * clear - H2 H4 HExecs HNoExec.
          apply HNoExec; unfold InExec in *.
          rewrite H2; assumption.
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
    + eapply HNoCall; eauto.
      rewrite in_flat_map in H1; dest.
      firstorder.
  - rewrite HLabel; simpl; setoid_rewrite <- flat_map_concat_map in IHPSubsteps.
    econstructor 3; intros; eauto.
    + clear - HDisjRegs.
      induction ls.
      * firstorder.
      * intro; simpl in *; rewrite map_app, in_app_iff, DeM1.
        assert (DisjKey (flat_map (fun x : FullLabel => fst x) ls) u);[eapply IHls; eauto|].
        specialize (HDisjRegs a (or_introl _ eq_refl) k); specialize (H k).
        firstorder fail.
    + eapply HNoCall; eauto.
      rewrite in_flat_map in H1; dest.
      firstorder.
Qed.

Section PPlusStep.
  Variable m: BaseModule.
  Variable o: RegsT.
  
  Definition MatchingExecCalls_flat (calls : MethsT) (exec : list RuleOrMeth) (m : BaseModule) :=
    forall (f : MethT),
      In f calls ->
      In (fst f) (map fst (getMethods m)) ->
      In (Meth f) exec.
  
  Inductive PPlusStep :  RegsT -> list RuleOrMeth -> MethsT -> Prop :=
  | BasePPlusStep upds execs calls:
      PPlusSubsteps m o upds execs calls ->
      MatchingExecCalls_flat calls execs m -> PPlusStep upds execs calls.
  
  Lemma PPlusStep_PStep:
    forall upds execs calls,
      PPlusStep upds execs calls ->
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
    repeat intro; specialize (H0 f) ; simpl; split; auto.
    unfold InCall, InExec, getLabelUpds, getLabelExecs, getLabelCalls in *; dest.
    rewrite <- flat_map_concat_map in *.
    rewrite H2 in H0; apply H0; eauto.
    rewrite H3, in_flat_map; firstorder.
  Qed.

  Lemma PStep_PPlusStep :
  forall l,
    PStep (Base m) o l ->
    PPlusStep (getLabelUpds l) (getLabelExecs l) (getLabelCalls l).
  Proof.
    intros; inv H; econstructor.
    - apply PSubsteps_PPlusSubsteps in HPSubsteps; assumption.
    - repeat intro; specialize (HMatching f).
      unfold InCall, InExec, getLabelUpds, getLabelExecs, getLabelCalls in *.
      rewrite <- flat_map_concat_map, in_flat_map in *; dest.
      eapply HMatching; eauto.
  Qed.
End PPlusStep.

Section PPlusTrace.
  Variable m: BaseModule.
  
  Definition PPlusUpdRegs (u o o' : RegsT) :=
    getKindAttr o [=] getKindAttr o' /\
    (forall s v, In (s, v) o' -> In (s, v) u \/ (~ In s (map fst u) /\ In (s, v) o)).
  
  Inductive PPlusTrace : RegsT -> list (RegsT * ((list RuleOrMeth) * MethsT)) -> Prop :=
  | PPlusInitTrace (o' o'' : RegsT) ls'
                   (HPerm : o' [=] o'')
                   (HUpdRegs : Forall2 regInit o'' (getRegisters m))
                   (HTrace : ls' = nil):
      PPlusTrace o' ls'
  | PPlusContinueTrace (o o' : RegsT)
                       (upds : RegsT)
                       (execs : list RuleOrMeth)
                       (calls : MethsT)
                       (ls ls' : list (RegsT * ((list RuleOrMeth) * MethsT)))
                       (PPlusOldTrace : PPlusTrace o ls)
                       (HPPlusStep : PPlusStep m o upds execs calls)
                       (HUpdRegs : PPlusUpdRegs upds o o')
                       (HPPlusTrace : ls' = ((upds, (execs, calls))::ls)):
      PPlusTrace o' ls'.

  Notation PPT_upds := (fun x => fst x).
  Notation PPT_execs := (fun x => fst (snd x)).
  Notation PPT_calls := (fun x => snd (snd x)).
  
  Lemma PPlusTrace_PTrace o ls :
    PPlusTrace o ls ->
    exists ls',
      PTrace (Base m) o ls' /\
      PermutationEquivLists (map PPT_upds ls) (map getLabelUpds ls') /\
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
      PPlusTrace o (extractTriples ls).
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
  Notation PPT_upds := (fun x => fst x).
  Notation PPT_execs := (fun x => fst (snd x)).
  Notation PPT_calls := (fun x => snd (snd x)).
  
  Definition WeakInclusion_flat (t1 t2 : (RegsT *((list RuleOrMeth) * MethsT))) :=
    (forall (f : MethT), In (Meth f) (PPT_execs t1) /\ ~In f (PPT_calls t1) <->
                         In (Meth f) (PPT_execs t2) /\ ~In f (PPT_calls t2)) /\
    (forall (f : MethT), ~In (Meth f) (PPT_execs t1) /\ In f (PPT_calls t1) <->
                         ~In (Meth f) (PPT_execs t2) /\ In f (PPT_calls t2)) /\
    (forall (f : MethT), ((In (Meth f) (PPT_execs t1) /\ In f (PPT_calls t1)) \/
                          (~In (Meth f) (PPT_execs t1) /\ ~In f (PPT_calls t1))) <->
                         ((In (Meth f) (PPT_execs t2) /\ In f (PPT_calls t2)) \/
                          (~In (Meth f) (PPT_execs t2) /\ ~In f (PPT_calls t2)))) /\
    ((exists rle, In (Rle rle) (PPT_execs t2)) ->
     (exists rle, In (Rle rle) (PPT_execs t1))).

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
    WeakInclusion_flat (extractTriple l1) (extractTriple l2) ->
    WeakInclusion l1 l2.
  Proof.
    unfold WeakInclusion_flat, extractTriple; simpl.
    setoid_rewrite InExec_rewrite; setoid_rewrite InCall_rewrite.
    intros; assumption.
  Qed.
  
  Inductive WeakInclusions_flat : list (RegsT * ((list RuleOrMeth) * MethsT)) -> list (RegsT *((list RuleOrMeth) * MethsT)) -> Prop :=
  |WIf_Nil : WeakInclusions_flat nil nil
  |WIf_Cons : forall (lt1 lt2 : list (RegsT *((list RuleOrMeth) * MethsT))) (t1 t2 : RegsT *((list RuleOrMeth) * MethsT)),
      WeakInclusions_flat lt1 lt2 -> WeakInclusion_flat t1 t2 -> WeakInclusions_flat (t1::lt1) (t2::lt2).

  
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
  
  Definition PPlusTraceList (m : BaseModule)(lt : list (RegsT * ((list RuleOrMeth) * MethsT))) :=
    (exists (o : RegsT), PPlusTrace m o lt).

  Definition PPlusTraceInclusion (m m' : BaseModule) :=
    forall (o : RegsT)(tl : list (RegsT *((list RuleOrMeth) * MethsT))),
      PPlusTrace m o tl -> exists (tl' : list (RegsT * ((list RuleOrMeth) * MethsT))),  PPlusTraceList m' tl' /\ WeakInclusions_flat tl tl'.

  Lemma WeakInclusions_flat_PermutationEquivLists_r ls1:
    forall l ls2,
      WeakInclusions_flat (extractTriples ls1) l ->
      PermutationEquivLists (map PPT_upds l) (map getLabelUpds ls2) ->
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
        split;[|split;[|split]];setoid_rewrite <- H10;auto; setoid_rewrite <- H9; auto.
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

  Corollary PPlusTraceInclusion_TraceInclusion (m m' : BaseModule) (Wfm : WfMod (Base m)) (Wfm' : WfMod (Base m')):
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

Lemma PSemAction_NoDup_Calls k  o (a : ActionT type k) readRegs newRegs calls (fret : type k) :
  PSemAction o a readRegs newRegs calls fret ->
  NoDup calls.
Proof.
  induction 1; eauto;[rewrite HAcalls; econstructor;eauto| | | |subst;econstructor];
    rewrite HUCalls; rewrite NoDup_app_iff; repeat split;eauto;firstorder.
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

Lemma PPlusSubsteps_NoDup_Calls m o upds execs calls:
  PPlusSubsteps m o upds execs calls ->
  NoDup calls.
Proof.
  induction 1;[econstructor| |];
    rewrite HCalls; rewrite NoDup_app_iff; repeat split;
      auto; eauto using PSemAction_NoDup_Calls.
Qed.

Lemma PPlusSubsteps_NoDup_Key_Writes m o upds execs calls:
  PPlusSubsteps m o upds execs calls ->
  NoDup (map fst upds).
Proof.
  induction 1;[econstructor| |];
    rewrite HUpds; rewrite map_app,NoDup_app_iff; repeat split;
      auto; eauto using PSemAction_NoDup_Key_Writes; repeat intro;
        specialize (HDisjRegs a);firstorder.
Qed.

Corollary PPlusSubsteps_NoDup_Writes m o upds execs calls :
  PPlusSubsteps m o upds execs calls ->
  NoDup upds.
Proof.
  intros; apply PPlusSubsteps_NoDup_Key_Writes in H;
    apply NoDup_map_inv in H; assumption.
Qed.

Lemma PPlusSubsteps_NoDup_Execs m o upds execs calls :
  PPlusSubsteps m o upds execs calls ->
  NoDup execs.
Proof.
  induction 1.
  - econstructor.
  - rewrite HExecs; econstructor; eauto.
    intro; specialize (HNoRle _ H0); simpl in *; contradiction.
  - rewrite HExecs; econstructor; eauto.
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

Definition called_by (f : DefMethT) (call :MethT) : bool := (getBool (string_dec (fst f) (fst call))).

Notation complement f := (fun x => negb (f x)).

Definition methcmp (m1 m2 : MethT) : bool := getBool (MethT_dec m1 m2).

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

Lemma key_not_In_filter (f : DefMethT) (calls : MethsT) :
  key_not_In (fst f) calls ->
  filter (complement (called_by f)) calls = calls.
Proof.
  induction calls; unfold key_not_In in *; simpl in *; intros; auto.
  unfold called_by in *; destruct string_dec; pose proof (H (snd a)); simpl in *.
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
  - econstructor 11; eauto.
Qed.

Inductive PSemAction_meth_collector (f : DefMethT) (o : RegsT) : RegsT -> RegsT -> MethsT -> MethsT -> Prop :=
|NilCalls : PSemAction_meth_collector f o nil nil nil nil
|ConsCalls reads1 reads2 reads upds1 upds2
           upds calls1 calls2 calls calls'
           calls'' argV retV:
   PSemAction_meth_collector f o reads1 upds1 calls1 calls' ->
   DisjKey upds1 upds2 ->
   (forall x, ~In x calls1 \/ ~In x calls2) ->
   (forall x, ~In x calls'' \/ ~In x calls) ->
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
    (forall x, ~In x calls1 \/ ~In x calls2) /\
    (forall x, ~In x calls' \/ ~In x calls) /\
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
  - rewrite H7 in H.
    destruct H.
    + exists reads1, reads2, upds1, upds2, calls1, calls2, calls', argV, retV; subst.
      repeat split; auto; (rewrite H3 || rewrite H4 || rewrite H5 || rewrite H6); subst; auto; apply Permutation_app_comm.
    + specialize (IHPSemAction_meth_collector H); dest.
      rewrite H16, H12, H13, H14 in *.
      exists (reads2++x), x0, (upds2++x1), x2, (calls2++x3), x4, ((fst f, existT _ (projT1 (snd f)) (argV, retV))::x5), x6, x7.
      repeat split; auto.
      * intro; destruct (H9 k), (H1 k); rewrite map_app,in_app_iff, DeM1 in *; dest; firstorder fail.
      * intro; destruct (H10 x8), (H2 x8); rewrite in_app_iff, DeM1 in *;[right|left; firstorder|right| right;assumption];
          rewrite H13, in_app_iff, DeM1 in H20; firstorder.
      * rewrite H5, <-app_assoc; apply Permutation_app_head, Permutation_app_comm.
      * rewrite H6, <-app_assoc; apply Permutation_app_head, Permutation_app_comm.
      * rewrite H4, <-app_assoc; apply Permutation_app_head, Permutation_app_comm.
      * rewrite H7; apply perm_swap.
      * econstructor.
        -- apply H18.
        -- assert (DisjKey x1 upds2).
           ++ intro; destruct (H1 k);[rewrite map_app,in_app_iff,DeM1 in *; dest; left; assumption|right; assumption].
           ++ apply H19.
        -- intro; specialize (H2 x8).
           rewrite H13, in_app_iff, DeM1 in H2; destruct H2;[dest; left; assumption|right; apply H2].
        -- intro; specialize (H3 x8).
           rewrite H6, H7 in H3; repeat rewrite in_app_iff, DeM1 in H3; simpl in *; destruct H3;[left; intro; apply H3|right;rewrite in_app_iff, DeM1]; firstorder.
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
  - rewrite H8 in H6.
    setoid_rewrite H8 in H2.
    econstructor; eauto.
Qed.

Global Instance collector_perm_rewrite' :
  Proper (eq ==> eq ==> eq ==> eq ==> eq ==> (@Permutation MethT) ==> iff) (@PSemAction_meth_collector) | 10.
Proof.
  repeat red; intro; split; intros; subst; eauto using collector_perm_rewrite, Permutation_sym.
Qed.


Lemma DeM2 (P Q : Prop) :
  ~(P \/ Q) <-> ~P /\ ~Q.
Proof.
  firstorder.
Qed.

Lemma collector_DisjCalls1 (f : DefMethT) o reads upds calls calls' :
  PSemAction_meth_collector f o reads upds calls calls' ->
  (forall x, ~In x calls \/ ~In x calls').
Proof.
  intros.
  inv H; auto.
  apply or_comm; apply H3.
Qed.

Lemma collector_NoDupCalls2 (f : DefMethT) o reads upds calls calls' :
  PSemAction_meth_collector f o reads upds calls calls' ->
  NoDup calls.
Proof.
  induction 1.
  - constructor.
  - rewrite H5, NoDup_app_iff.
    specialize (PSemAction_NoDup_Calls H7) as ND2.
    repeat split; auto; repeat intro; specialize (H1 a); firstorder.
Qed.

Lemma collector_NoDupRegs1 (f : DefMethT) o reads upds calls calls' :
  PSemAction_meth_collector f o reads upds calls calls' ->
  NoDup (map fst upds).
Proof.
  induction 1.
  - constructor.
  - rewrite H4, map_app, NoDup_app_iff.
    specialize (PSemAction_NoDup_Key_Writes H7) as ND2.
    repeat split; auto; repeat intro; specialize (H0 a); firstorder.
Qed.

Lemma collector_split (f : DefMethT) o calls1' calls2' :
  forall  reads upds calls,
  PSemAction_meth_collector f o reads upds calls (calls1'++calls2') ->
  exists reads1 reads2 upds1 upds2 calls1 calls2,
    reads [=] reads1 ++ reads2 /\
    upds [=] upds1 ++ upds2 /\
    calls [=] calls1 ++ calls2 /\
    PSemAction_meth_collector f o reads1 upds1 calls1 calls1' /\
    PSemAction_meth_collector f o reads2 upds2 calls2 calls2'.
Proof.
  induction calls1'; simpl; intros.
  - exists nil, reads, nil, upds, nil, calls.
    repeat split; auto.
    constructor.
  - specialize (Produce_action_from_collector _ (in_eq _ _) H) as TMP; dest.
    apply Permutation_cons_inv in H7.
    rewrite <- H7 in H9.
    specialize (IHcalls1' _ _ _ H9) as TMP; dest.
    exists (x0++x8), x9, (x2++x10), x11, (x4++x12), x13.
    repeat split.
    + rewrite H10, app_assoc in H5; assumption.
    + rewrite H11, app_assoc in H3; assumption.
    + rewrite H12, app_assoc in H4; assumption.
    + econstructor.
      * apply H13.
      * rewrite H11 in H0; assert (DisjKey x10  x2);[intro; specialize (H0 k);
                                                     rewrite map_app, in_app_iff, DeM2 in *;clear - H0; firstorder|apply H15].
      * setoid_rewrite H12 in H1.
        assert (forall x, ~In x x12 \/ ~In x x4);[intro; specialize (H1 x14); rewrite in_app_iff, DeM2 in *; clear - H1; firstorder| apply H15].
      * intro; specialize (H2 x14); rewrite H4, H12 in H2.
        simpl in *; repeat rewrite in_app_iff, DeM2 in *.
        clear - H2; firstorder.
      * apply Permutation_app_comm.
      * apply Permutation_app_comm.
      * apply Permutation_app_comm.
      * rewrite H6; reflexivity.
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
  destruct call; inv H7; simpl; reflexivity.
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
  apply Permutation_cons_inv in H8.
  rewrite <- H8 in H10.
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
  destruct call; inv H7; simpl; exists x6, x7; reflexivity.
Qed.

Lemma notIn_filter_nil (f : DefMethT) (calls : MethsT) :
  ~In (fst f) (map fst calls) ->
  filter (called_by f) calls = nil.
Proof.
  induction calls; auto; simpl.
  rewrite DeM2; intro; dest.
  apply not_eq_sym in H.
  unfold called_by; destruct string_dec; simpl; auto; contradiction.
Qed.

Lemma notIn_complement_filter_irrel (f : DefMethT) (calls : MethsT) :
  ~In (fst f) (map fst calls) ->
  filter (complement (called_by f)) calls = calls.
Proof.
  induction calls; auto; simpl; intros.
  rewrite DeM2 in *; dest.
  apply not_eq_sym in H.
  unfold called_by in *; destruct string_dec; simpl in *;[contradiction|].
  rewrite IHcalls; auto.
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

Lemma PSemAction_inline_In (f : DefMethT) o:
  forall {retK2} a calls1 calls2 readRegs newRegs (retV2 : type retK2),
    PSemAction o a readRegs newRegs (calls1++calls2) retV2 ->
    ~In (fst f) (map fst calls2) ->
    forall readRegs' newRegs' calls',
      DisjKey newRegs' newRegs ->
      (forall x, ~In x calls' \/ ~In x calls2) ->
      PSemAction_meth_collector f o readRegs' newRegs' calls' calls1 ->      
      PSemAction o (inlineSingle f a) (readRegs' ++ readRegs) (newRegs' ++ newRegs) (calls'++calls2) retV2.
Proof.
  induction a; intros.
  - simpl; destruct string_dec;[destruct Signature_dec|]; subst.
    + specialize (PSemAction_NoDup_Calls H0) as HPsa_nd_C.
      inv H0; EqDep_subst.
      assert (In (fst f, existT SignT (projT1 (snd f)) (evalExpr e, mret)) calls1);
        [case (in_app_or _ _ _ (Permutation_in _ (Permutation_sym (HAcalls)) (in_eq _ _))); auto; intros TMP;apply (in_map fst) in TMP; contradiction|].
      specialize (Produce_action_from_collector _ H0 H4) as TMP; destruct TMP as [creads1 [creads2 [cupds1 [cupds2 [ccalls1 [ccalls2 [ccalls'' [cargV [cretV decomp]]]]]]]]].
      destruct decomp as [HDisju12 [HDisjc12 [HDisjc1' [HNr21 [HC21 [HRr21 [Hceq [HC1 [HSa HSac]]]]]]]]].
      inv Hceq; EqDep_subst.
      econstructor.
      * rewrite HNr21 in H2.
        assert (DisjKey cupds2 (cupds1++newRegs)) as HDjk21n;[|apply HDjk21n].
        intro; specialize (H2 k); specialize (HDisju12 k); rewrite map_app,in_app_iff, DeM1 in *.
        clear - H2 HDisju12; firstorder fail.
      * assert (forall x, ~In x ccalls2 \/ ~In x (ccalls1++calls2)) as HDj221;[|apply HDj221].
        intros x; specialize (H3 x); specialize (NoDup_app_Disj MethT_dec _ _ HPsa_nd_C x) as HNd_a_d; specialize (HDisjc1' x); specialize (HDisjc12 x).
        rewrite HC21 in HDisjc1', H3; rewrite in_app_iff, DeM2 in *.
        clear - HDisjc1' HNd_a_d H3 HDisjc12; firstorder fail.
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
           intro; specialize (H2 k); rewrite map_app, in_app_iff, DeM2 in *.
           clear - H2; firstorder fail.
        -- intro x; specialize (H3 x); rewrite HC21, in_app_iff, DeM2 in H3.
           clear - H3; firstorder fail.
        -- assumption.
    + inv H0; EqDep_subst.
      specialize (Permutation_in _ (Permutation_sym HAcalls) (in_eq _ _)); rewrite in_app_iff; intro TMP.
      destruct TMP as [H0|H0];[|apply (in_map fst) in H0; contradiction].
      specialize (collector_correct_snd _ H0 H4) as TMP; dest; simpl in *.
      inv H5; EqDep_subst.
      apply False_ind; apply n; reflexivity.
    + inv H0; EqDep_subst.
      specialize (Permutation_in _ (Permutation_sym HAcalls) (in_eq _ _)); intro TMP.
      rewrite in_app_iff in TMP; destruct TMP as [H0|H0];[apply (collector_correct_fst _ H0) in H4; symmetry in H4; contradiction|].
      apply in_split in H0; dest.
      rewrite H0, <-Permutation_middle, Permutation_app_comm in HAcalls; simpl in *.
      apply Permutation_cons_inv in HAcalls.
      rewrite Permutation_app_comm in HAcalls.
      rewrite <- HAcalls,in_app_iff,DeM2 in HDisjCalls; dest.
      assert (~In (meth, existT _ s (evalExpr e, mret)) (calls'++x++x0));
        [rewrite in_app_iff, DeM2; specialize (H3 (meth, existT _ s (evalExpr e, mret))); destruct H3; split; auto;
         apply False_ind; rewrite H0 in H3; apply H3; rewrite in_app_iff; simpl; right; left; reflexivity|].
      econstructor.
      * apply H7.
      * rewrite H0, app_assoc,Permutation_app_comm; simpl.
        apply perm_skip.
        rewrite Permutation_app_comm, app_assoc.
        reflexivity.
      * eapply H; auto.
        -- apply (PSemAction_rewrite_calls (Permutation_sym HAcalls) HPSemAction).
        -- rewrite H0 in H1.
           rewrite map_app, in_app_iff in *.
           simpl in *; repeat rewrite DeM2 in *; clear - H1; firstorder fail.
        -- intro x1; specialize (H3 x1).
           rewrite H0, <-Permutation_middle in H3.
           simpl in *; rewrite DeM2 in *.
           clear - H3; firstorder fail.
        -- assumption.
  - inv H0; EqDep_subst.
    econstructor 2; eauto.
  - inv H0; EqDep_subst.
    specialize (Permutation_filter (called_by f) HUCalls) as HC1.
    rewrite filter_app, (collector_called_by_filter_irrel H4), notIn_filter_nil, app_nil_r in HC1; auto.
    specialize (Permutation_filter (complement (called_by f)) HUCalls) as HC2.
    rewrite filter_app, (collector_complement_called_by_filter_nil H4), (notIn_complement_filter_irrel) in HC2; auto; simpl in *.
    rewrite filter_app in *.
    rewrite HC1 in H4.
    specialize (collector_split _ _ H4) as TMP; destruct TMP as [sreads1 [sreads2 [supds1 [supds2 [scalls1 [scalls2 TMP]]]]]].
    destruct TMP as [HRr12 [HNr12 [HC12 [HCol1 HCol2]]]].
    econstructor 3.
    + rewrite HNr12, HUNewRegs in H2.
      specialize (collector_NoDupRegs1 H4); rewrite HNr12, map_app; intros TMP.
      assert (DisjKey (supds1++newRegs0) (supds2++newRegsCont));[|apply H0].
      intro; specialize (H2 k0); specialize (HDisjRegs k0);specialize (NoDup_app_Disj string_dec _ _ TMP k0) as TMP2.
      repeat rewrite map_app, in_app_iff, DeM2 in *.
      clear - H2 HDisjRegs TMP2; firstorder fail.
    + assert (forall x, ~In x (scalls1++(filter (complement (called_by f)) calls)) \/ ~In x (scalls2++(filter (complement (called_by f)) callsCont)));[|apply H0].
      intro x; specialize (H3 x).
      specialize (HDisjCalls x).
      specialize (collector_NoDupCalls2 H4); rewrite HC12; intro HNds12.
      specialize (NoDup_app_Disj MethT_dec _ _ HNds12 x) as Hdisjs12.
      rewrite (separate_calls_by_filter calls (called_by f)), (separate_calls_by_filter callsCont (called_by f)) in HDisjCalls.
      rewrite HC12, HC2 in H3.
      repeat rewrite in_app_iff, DeM2 in *.
      clear -  HDisjCalls H3 Hdisjs12.
      firstorder fail.
    + eapply IHa.
      * apply (PSemAction_rewrite_calls (separate_calls_by_filter calls (called_by f))) in HPSemAction.
        apply HPSemAction.
      * intro; apply H1; rewrite HC2, map_app, in_app_iff; left; assumption.
      *rewrite HNr12, HUNewRegs in H2.
       intro; specialize (H2 k0); repeat rewrite map_app, in_app_iff, DeM2 in *.
       clear - H2; firstorder fail.
      * intros x; specialize (H3 x).
        rewrite HC12, HC2 in H3.
        repeat rewrite in_app_iff, DeM2 in *.
        clear - H3; firstorder fail.
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
      repeat rewrite app_assoc.
      apply Permutation_app_tail.
      apply Permutation_app_comm.
    + eapply H; eauto.
      * apply (PSemAction_rewrite_calls (separate_calls_by_filter callsCont (called_by f)) HPSemActionCont).
      * rewrite HC2, map_app,in_app_iff,DeM2 in H1; dest; assumption.
      * rewrite HNr12, HUNewRegs in H2.
        intro k0; specialize (H2 k0).
        repeat rewrite map_app, in_app_iff, DeM2 in H2.
        clear - H2; firstorder fail.
      * intro x; specialize (H3 x).
        rewrite HC12, HC2 in H3.
        repeat rewrite in_app_iff, DeM2 in H3.
        clear - H3; firstorder fail.
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
      intro; rewrite in_app_iff, DeM2.
      specialize (HDisjRegs v).
      split; auto; intro.
      apply (in_map fst) in H; simpl in *.
      rewrite HANewRegs in H1; specialize (H1 r).
      destruct H1;[contradiction|apply H1; left; reflexivity].
    + rewrite HANewRegs.
      rewrite Permutation_app_comm; simpl.
      apply perm_skip, Permutation_app_comm.
    + eapply IHa; eauto.
      rewrite HANewRegs in H1; intro k0; specialize (H1 k0); simpl in *.
      rewrite DeM2 in H1; clear - H1; firstorder fail.
  - inv H0; EqDep_subst; simpl.
    + specialize (Permutation_filter (called_by f) HUCalls) as HC1.
      rewrite filter_app, (collector_called_by_filter_irrel H4), notIn_filter_nil, app_nil_r in HC1; auto.
      specialize (Permutation_filter (complement (called_by f)) HUCalls) as HC2.
      rewrite filter_app, (collector_complement_called_by_filter_nil H4), (notIn_complement_filter_irrel) in HC2; auto; simpl in *.
      rewrite filter_app in *.
      rewrite HC1 in H4.
      specialize (collector_split _ _ H4) as TMP; destruct TMP as [sreads1 [sreads2 [supds1 [supds2 [scalls1 [scalls2 TMP]]]]]].
      destruct TMP as [HRr12 [HNr12 [HC12 [HCol1 HCol2]]]].
      econstructor 7.
      * rewrite HNr12, HUNewRegs in H2.
        specialize (collector_NoDupRegs1 H4); rewrite HNr12, map_app; intros TMP.
        assert (DisjKey (supds1++newRegs1) (supds2++newRegs2));[|apply H0].
        intro; specialize (H2 k0); specialize (HDisjRegs k0);specialize (NoDup_app_Disj string_dec _ _ TMP k0) as TMP2.
        repeat rewrite map_app, in_app_iff, DeM2 in *.
        clear - H2 HDisjRegs TMP2; firstorder fail.
      * assert (forall x, ~In x (scalls1++(filter (complement (called_by f)) calls0)) \/ ~In x (scalls2++(filter (complement (called_by f)) calls3)));[|apply H0].
        intro x; specialize (H3 x).
        specialize (HDisjCalls x).
        specialize (collector_NoDupCalls2 H4); rewrite HC12; intro HNds12.
        specialize (NoDup_app_Disj MethT_dec _ _ HNds12 x) as Hdisjs12.
        rewrite (separate_calls_by_filter calls0 (called_by f)), (separate_calls_by_filter calls3 (called_by f)) in HDisjCalls.
        rewrite HC12, HC2 in H3.
        repeat rewrite in_app_iff, DeM2 in *.
        clear -  HDisjCalls H3 Hdisjs12.
        firstorder fail.
      * assumption.
      * eapply IHa1.
        -- apply (PSemAction_rewrite_calls (separate_calls_by_filter calls0 (called_by f))) in HAction.
           apply HAction.
        -- intro; apply H1; rewrite HC2, map_app, in_app_iff; left; assumption.
        -- rewrite HNr12, HUNewRegs in H2.
           intro; specialize (H2 k0); repeat rewrite map_app, in_app_iff, DeM2 in *.
           clear - H2; firstorder fail.
        -- intros x; specialize (H3 x).
           rewrite HC12, HC2 in H3.
           repeat rewrite in_app_iff, DeM2 in *.
           clear - H3; firstorder fail.
        -- apply HCol1.
      * eapply H.
        -- apply (PSemAction_rewrite_calls (separate_calls_by_filter calls3 (called_by f)) HPSemAction).
        -- rewrite HC2, map_app,in_app_iff,DeM2 in H1; dest; assumption.
        -- rewrite HNr12, HUNewRegs in H2.
           intro k0; specialize (H2 k0).
           repeat rewrite map_app, in_app_iff, DeM2 in H2.
           clear - H2; firstorder fail.
        -- intro x; specialize (H3 x).
           rewrite HC12, HC2 in H3.
           repeat rewrite in_app_iff, DeM2 in H3.
           clear - H3; firstorder fail.
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
      rewrite filter_app, (collector_called_by_filter_irrel H4), notIn_filter_nil, app_nil_r in HC1; auto.
      specialize (Permutation_filter (complement (called_by f)) HUCalls) as HC2.
      rewrite filter_app, (collector_complement_called_by_filter_nil H4), (notIn_complement_filter_irrel) in HC2; auto; simpl in *.
      rewrite filter_app in *.
      rewrite HC1 in H4.
      specialize (collector_split _ _ H4) as TMP; destruct TMP as [sreads1 [sreads2 [supds1 [supds2 [scalls1 [scalls2 TMP]]]]]].
      destruct TMP as [HRr12 [HNr12 [HC12 [HCol1 HCol2]]]].
      econstructor 8.
      * rewrite HNr12, HUNewRegs in H2.
        specialize (collector_NoDupRegs1 H4); rewrite HNr12, map_app; intros TMP.
        assert (DisjKey (supds1++newRegs1) (supds2++newRegs2));[|apply H0].
        intro; specialize (H2 k0); specialize (HDisjRegs k0);specialize (NoDup_app_Disj string_dec _ _ TMP k0) as TMP2.
        repeat rewrite map_app, in_app_iff, DeM2 in *.
        clear - H2 HDisjRegs TMP2; firstorder fail.
      * assert (forall x, ~In x (scalls1++(filter (complement (called_by f)) calls0)) \/ ~In x (scalls2++(filter (complement (called_by f)) calls3)));[|apply H0].
        intro x; specialize (H3 x).
        specialize (HDisjCalls x).
        specialize (collector_NoDupCalls2 H4); rewrite HC12; intro HNds12.
        specialize (NoDup_app_Disj MethT_dec _ _ HNds12 x) as Hdisjs12.
        rewrite (separate_calls_by_filter calls0 (called_by f)), (separate_calls_by_filter calls3 (called_by f)) in HDisjCalls.
        rewrite HC12, HC2 in H3.
        repeat rewrite in_app_iff, DeM2 in *.
        clear -  HDisjCalls H3 Hdisjs12.
        firstorder fail.
      * assumption.
      * eapply IHa2.
        -- apply (PSemAction_rewrite_calls (separate_calls_by_filter calls0 (called_by f))) in HAction.
           apply HAction.
        -- intro; apply H1; rewrite HC2, map_app, in_app_iff; left; assumption.
        -- rewrite HNr12, HUNewRegs in H2.
           intro; specialize (H2 k0); repeat rewrite map_app, in_app_iff, DeM2 in *.
           clear - H2; firstorder fail.
        -- intros x; specialize (H3 x).
           rewrite HC12, HC2 in H3.
           repeat rewrite in_app_iff, DeM2 in *.
           clear - H3; firstorder fail.
        -- apply HCol1.
      * eapply H.
        -- apply (PSemAction_rewrite_calls (separate_calls_by_filter calls3 (called_by f)) HPSemAction).
        -- rewrite HC2, map_app,in_app_iff,DeM2 in H1; dest; assumption.
        -- rewrite HNr12, HUNewRegs in H2.
           intro k0; specialize (H2 k0).
           repeat rewrite map_app, in_app_iff, DeM2 in H2.
           clear - H2; firstorder fail.
        -- intro x; specialize (H3 x).
           rewrite HC12, HC2 in H3.
           repeat rewrite in_app_iff, DeM2 in H3.
           clear - H3; firstorder fail.
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
    econstructor 10; eauto.
  - inv H; EqDep_subst.
    apply app_eq_nil in HCalls; dest; subst.
    inv H3; simpl in *.
    + econstructor 11; eauto.
    + apply Permutation_nil in H10; discriminate.
Qed.  

Lemma PPlusSubsteps_inline_notIn f m o upds execs calls:
  PPlusSubsteps m o upds execs calls ->
  ~In (fst f) (map fst calls) ->
  PPlusSubsteps (inlinesingle_BaseModule m f) o upds execs calls.
Proof.
  induction 1; simpl; intros.
  - econstructor 1; eauto.
  - rewrite HUpds, HExecs, HCalls.
    apply (in_map (inlinesingle_Rule f)) in HInRules.
    econstructor 2 with (u := u) (reads := reads); eauto.
    + eapply PSemAction_inline_notIn; eauto.
      intro; apply H0; rewrite HCalls, map_app, in_app_iff; left; assumption.
    + eapply IHPPlusSubsteps.
      intro; apply H0; rewrite HCalls, map_app, in_app_iff; right; assumption.
  - rewrite HUpds, HExecs, HCalls.
    apply (in_map (inlinesingle_Meth f)) in HInMeths; destruct fb.
    econstructor 3 with (u := u) (reads := reads); simpl; eauto.
    + simpl; eapply PSemAction_inline_notIn; eauto.
      intro; apply H0; rewrite HCalls, map_app, in_app_iff; left; assumption.
    + eapply IHPPlusSubsteps.
      intro; apply H0; rewrite HCalls, map_app, in_app_iff; right; assumption.
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
        -- destruct H0; dest; destruct H0; subst; simpl in *.
           ++ eapply HNoCall; eauto.
              exists (u0, (Meth (fn, existT SignT (projT1 fb) (argV, retV)), cs0)); split;
                [left; reflexivity|auto].
           ++ eapply HNoCall0; eauto.
              exists x; firstorder.
        -- unfold InExec in *; simpl in *.
           destruct H;[discriminate|auto].
        -- econstructor 2; eauto; intros.
           ++ eapply HDisjRegs; right; assumption.
           ++ eapply HNoRle; right; assumption.
           ++ eapply HNoCall; eauto.
              destruct H0; dest.
              exists x; split; auto; right; assumption.
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
        -- destruct H0; dest; destruct H0; subst; simpl in *.
           ++ eapply HNoCall; eauto.
              exists (u0, (Rle rn, cs0)); split; auto; left; reflexivity.
           ++ eapply HNoCall0; eauto.
              exists x; firstorder.
        -- econstructor 3; eauto; intros.
           ++ eapply HDisjRegs; right; assumption.
           ++ eapply HNoCall; eauto.
              destruct H0; dest.
              exists x; split; auto; right; assumption.
           ++ unfold InExec in *; simpl in *.
              eapply HNoExec; right; assumption.
      * econstructor 3; eauto; intros.
        -- destruct H; subst; simpl.
           ++ specialize (HDisjRegs _ (in_eq _ _)); simpl in *.
              apply DisjKey_Commutative; assumption.
           ++ eapply HDisjRegs0; eauto.
        -- destruct H0; dest; destruct H0; subst; simpl in *.
           ++ eapply HNoCall; eauto.
              exists (u0, (Meth (fn0, existT SignT (projT1 fb0) (argV0, retV0)), cs0));
                split; auto;left; reflexivity.
           ++ eapply HNoCall0; eauto.
              exists x; split; auto.
        -- unfold InExec in *; simpl in *.
           destruct H.
           ++ inv H; EqDep_subst.
              destruct fb, fb0; simpl in *; subst; EqDep_subst.
              apply HNoExec; left; reflexivity.
           ++ apply HNoExec0; auto.
        -- econstructor 3; auto; auto;[apply HAction | | | | ]; auto; intros.
           ++ eapply HDisjRegs; right; assumption.
           ++ eapply HNoCall; eauto.
              destruct H0; dest.
              exists x; split; auto; right; assumption.
           ++ unfold InExec in *; simpl in *.
              apply HNoExec; right; assumption.
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

Lemma extract_exec (f : DefMethT) m o l u cs fb:
  NoDup (map fst (getMethods m)) ->
  In f (getMethods m) ->
  Substeps m o ((u, (Meth ((fst f), fb), cs))::l) ->
  exists reads e mret,
    fb =  existT SignT (projT1 (snd f)) (e, mret) /\
    DisjKey u (getLabelUpds l) /\
    (forall x, ~In x cs \/ ~In x (getLabelCalls l)) /\
    SemAction o ((projT2 (snd f) type) e) reads u cs mret /\
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
    + intro x0; specialize (HNoCall x0).
      clear - HNoCall.
      destruct (in_dec MethT_dec x0 cs0), (InCall_dec x0 ls);auto.
      right; rewrite <-InCall_getLabelCalls_iff; assumption.
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
    (forall x, ~In x cs \/ ~In x (getLabelCalls l)) /\
    PSemAction o ((projT2 (snd f) type) e) reads u cs mret /\
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
  + setoid_rewrite H14.
    setoid_rewrite (List_FullLabel_perm_getLabelCalls_perm P2).
    assumption.
  + symmetry in H1, H11, H14.
    apply (PSemAction_rewrite_state H1).
    apply (PSemAction_rewrite_newRegs H11).
    apply (PSemAction_rewrite_calls H14).
    apply SemAction_PSemAction; assumption.
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
    (forall x, ~In x calls1 \/ ~In x calls2) /\
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

Lemma rewrite_called_execs:
  forall calls execs, 
    (forall f, In f calls -> In (Meth f) execs) ->
    NoDup execs ->
    NoDup calls ->
    (filter (called_execs calls) execs) [=] (map Meth calls).
Proof.
  induction calls; intros.
  - unfold called_execs; simpl.
    assert ((fun x => match x with |Rle _ | _ => false end) = (fun _ => false));[
      apply functional_extensionality; destruct x; reflexivity|].
    rewrite H2; rewrite filter_false; reflexivity.
  - unfold called_execs in *; simpl in *.
    specialize (H a (or_introl _ eq_refl)) as H'.
    apply in_split in H'; dest; rewrite H2,<-Permutation_middle.
    simpl; unfold methcmp; destruct MethT_dec;[simpl|apply False_ind; apply n; reflexivity].
    apply Permutation_cons;[reflexivity|].
    assert (~In (Meth a) (x++x0)).
    + rewrite H2 in H0; rewrite <- Permutation_middle in H0.
      inv H0; assumption.
    + specialize (reduce_called_execs_list _ _ H3 calls) as TMP.
      unfold called_execs, methcmp in *; simpl in *.
      rewrite TMP.
      eapply IHcalls.
      * intros.
        rewrite H2 in H; specialize (H _ (or_intror _ H4)).
        rewrite <- Permutation_middle in H.
        destruct H;[inv H; inv H1; contradiction| assumption].
      * rewrite H2, <-Permutation_middle in H0; inv H0; assumption.
      * inv H1; assumption.
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
  - unfold called_by in H1; simpl in *.
    destruct string_dec; subst; simpl in *.
    + destruct H1; subst.
      * apply (in_map fst) in H; rewrite e in H.
        apply (H0 _ (or_introl _ (eq_refl)) H).
      * eapply IHcalls; eauto.
    + eapply IHcalls;eauto.
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

Lemma PPlusSubsteps_inline_In f m o :
  NoDup (map fst (getMethods m)) ->
  In f (getMethods m) ->
  forall fcalls upds nfcalls execs,
    (forall m, In (Meth m) execs -> (fst m <> fst f)) ->
    (forall c, In c fcalls -> fst c = fst f) ->
    (forall c, In c nfcalls -> fst c <> fst f) ->
    PPlusSubsteps m o upds ((map Meth fcalls)++execs) (fcalls++nfcalls) ->
    exists reads upds1 upds2 calls1 calls2,
      upds [=] upds1++upds2 /\
      (fcalls++nfcalls [=] calls1++calls2) /\
      PSemAction_meth_collector f o reads upds1 calls1 fcalls /\
      PPlusSubsteps m o upds2 execs calls2.
Proof.
  induction fcalls; simpl in *; intros.
  - exists nil, nil, upds, nil, nfcalls; simpl.
    repeat split; auto.
    constructor.
  - destruct a; specialize (H2 _ (or_introl _ eq_refl)) as TMP; simpl in *; subst.
    specialize (extract_exec_PPlus _ H H0 H4) as TMP; dest; subst.
    admit.
Admitted.