Require Import Kami.Syntax.
Require Import Kami.Properties Kami.PProperties.
Import ListNotations.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.PermutEq.
Require Import RelationClasses Setoid Morphisms.
Require Import ZArith.


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
            (HPSubstep: PPlusSubsteps oldUpds oldExecs oldCalls):
      PPlusSubsteps upds execs calls.
  
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
  
  Definition MatchingExecCalls_flat (calls : MethsT) (execs : list RuleOrMeth) (m : BaseModule) :=
    forall (f : MethT),
      In (fst f) (map fst (getMethods m)) ->
      (getNumFromCalls f calls <= getNumFromExecs f execs)%Z.
  
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
    intros f HInDef; specialize (H0 f HInDef).
    unfold getNumCalls, getNumExecs, getLabelExecs, getLabelCalls in *.
    rewrite <-H3, <-H2; assumption.
  Qed.

  Lemma PStep_PPlusStep :
  forall l,
    PStep (Base m) o l ->
    PPlusStep (getLabelUpds l) (getLabelExecs l) (getLabelCalls l).
  Proof.
    intros; inv H; econstructor.
    - apply PSubsteps_PPlusSubsteps in HPSubsteps; assumption.
    - intros f HInDef; specialize (HMatching f).
      apply HMatching; auto.
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

  Definition getListFullLabel_diff_flat f (t : (RegsT *((list RuleOrMeth)*MethsT))) : Z:=
    (getNumFromExecs f (PPT_execs t) - getNumFromCalls f (PPT_calls t))%Z. 
  
  Definition WeakInclusion_flat (t1 t2 : (RegsT *((list RuleOrMeth) * MethsT))) :=
    (forall (f : MethT), (getListFullLabel_diff_flat f t1 = getListFullLabel_diff_flat f t2)%Z) /\
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
    WeakInclusion_flat (extractTriple l1) (extractTriple l2) <->
    WeakInclusion l1 l2.
  Proof.
    split; auto.
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

  Definition StrongPPlusTraceInclusion (m m' : BaseModule) :=
    forall (o : RegsT)(tl : list (RegsT *((list RuleOrMeth) * MethsT))),
      PPlusTrace m o tl -> exists (tl' : list (RegsT * ((list RuleOrMeth) * MethsT))), PPlusTrace m' o tl' /\ WeakInclusions_flat tl tl'.

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
  - econstructor 11; eauto.
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

Notation complement f := (fun x => negb (f x)).

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
    econstructor 10; eauto.
  - inv H; EqDep_subst.
    apply app_eq_nil in HCalls; dest; subst.
    inv H2; simpl in *.
    + econstructor 11; eauto.
    + apply Permutation_nil in H7; discriminate.
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

Fixpoint inlineSingle_Rule_in_list (f : DefMethT) (rn : string) (lr : list RuleT) : list RuleT :=
  match lr with
  | rle'::lr' => match string_dec rn (fst rle') with
                 | right _ => rle'::(inlineSingle_Rule_in_list f rn lr')
                 | left _ => (inlinesingle_Rule f rle')::(inlineSingle_Rule_in_list f rn lr')
                 end
  | nil => nil
  end.
                                
Definition inlineSingle_Rule_BaseModule (f : DefMethT) (rn : string) (m : BaseModule) :=
  BaseMod (getRegisters m) (inlineSingle_Rule_in_list f rn (getRules m)) (getMethods m).

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
  specialize (H1 (evalExpr e)).
  apply (WfActionT_inline_Rule); auto.
Qed.

Lemma inlineSingle_Rule_BaseModule_dec rule f rn l:
  In rule (inlineSingle_Rule_in_list f rn l) ->
  In rule l \/
  exists rule',
    In rule' l /\
    (fst rule' = fst rule) /\
    ((inlineSingle f (snd rule' type)) = snd rule type).
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

Lemma inlineSingle_Rule_preserves_names f rn l:
  (map fst l) = (map fst (inlineSingle_Rule_in_list f rn l)).
Proof.
  induction l; auto.
  simpl; destruct string_dec, a; simpl;rewrite IHl; reflexivity.
Qed.

Lemma WfMod_inlined m f rn :
  WfMod (Base m) ->
  In f (getMethods m) ->
  WfMod (Base (inlineSingle_Rule_BaseModule f rn m)).
Proof.
  intros; inv H; econstructor; eauto.
  - split; intros; simpl in *; inv WfBaseModule; eauto; pose proof (H2 _ H0).
    + destruct (inlineSingle_Rule_BaseModule_dec _ _ _ _ H).
      * specialize (H1 _ H4); apply WfActionT_inline_Rule; auto.
      * dest.
        specialize (H1 _ H4).
        rewrite <- H6.
        apply WfActionT_inline_Rule_inline_action; auto.
    + apply WfActionT_inline_Rule; auto.
  - simpl; rewrite <-inlineSingle_Rule_preserves_names; auto.
Qed.    

Lemma PPlusStrongTraceInclusion_inlining_Rules_r m f rn :
  In f (getMethods m) ->
  WfMod (Base m) ->
  StrongPPlusTraceInclusion m (inlineSingle_Rule_BaseModule f rn m).
Proof.
  unfold StrongPPlusTraceInclusion; induction 3; subst.
  - exists nil; split.
    + econstructor; eauto.
    + constructor.
  - dest;destruct (in_dec (RuleOrMeth_dec) (Rle rn) execs),(in_dec string_dec rn (map fst (getRules m)));inv H0.
    * rewrite in_map_iff in i0; dest; destruct x0; simpl in *; subst.
      specialize (PPlusStep_inline_Rule_In _ _ _ H4 H NoDupRle NoDupMeths i HPPlusStep) as TMP; dest.
      exists ((upds, (x1, x2))::x); split.
      -- econstructor 2; eauto.
      -- constructor; auto.
         unfold WeakInclusion_flat, getListFullLabel_diff_flat.
         split; intros.
         ++ simpl;rewrite H0, H5, getNumFromExecs_app, getNumFromCalls_app, (call_execs_counts_eq); Omega.omega.
         ++ simpl in *; destruct H7; exists x3; rewrite H0, in_app_iff; right; assumption.
    * exists ((upds, (execs, calls))::x); split.
      -- econstructor 2; eauto.
         apply PPlusStep_inlined_undef_Rule; auto.
      -- econstructor; eauto.
         unfold WeakInclusion_flat; split; intros; auto.
    * exists ((upds, (execs, calls))::x); split.
      -- econstructor 2; eauto.
         apply (PPlusStep_inline_Rule_NotIn); auto.
      -- econstructor; eauto.
         unfold WeakInclusion_flat; split; intros; auto.
    * exists ((upds, (execs, calls))::x); split.
      -- econstructor 2; eauto.
         apply (PPlusStep_inline_Rule_NotIn); auto.
      -- econstructor; eauto.
         unfold WeakInclusion_flat; split; intros; auto.
Qed.

Corollary TraceInclusion_inlining_Rules_r m f rn :
  In f (getMethods m) ->
  WfMod (Base m) ->
  TraceInclusion (Base m) (Base (inlineSingle_Rule_BaseModule f rn m)).
Proof.
  intros.
  apply PPlusTraceInclusion_TraceInclusion; auto.
  apply (WfMod_inlined); auto.
  eauto using StrongPPlusTraceInclusion_PPlusTraceInclusion, PPlusStrongTraceInclusion_inlining_Rules_r.
Qed.

Fixpoint inlineSingle_Meth_in_list (f : DefMethT) (gn : string) (lm : list DefMethT) : list DefMethT :=
  match (string_dec (fst f) gn) with
  | left _ => lm
  | right _ => match lm with
              | meth'::lm' => match string_dec gn (fst meth') with
                              | right _ => meth'::(inlineSingle_Meth_in_list f gn lm')
                              | left _ => (inlinesingle_Meth f meth')::(inlineSingle_Meth_in_list f gn lm')
                              end
              | nil => nil
              end
  end.
                                
Definition inlineSingle_Meth_BaseModule (f : DefMethT) (fn : string) (m : BaseModule) :=
  BaseMod (getRegisters m) (getRules m) (inlineSingle_Meth_in_list f fn (getMethods m)).

Lemma ProjT1_inline_eq (f g : DefMethT):
  (projT1 (snd g)) = (projT1 (snd (inlinesingle_Meth f g))).
Proof.
  destruct g, s0; simpl; reflexivity.
Qed.

Lemma InMeth_In_inlined f gn gb m:
  gn <> (fst f) ->
  In (gn, gb) (getMethods m) ->
  In (inlinesingle_Meth f (gn, gb)) (getMethods (inlineSingle_Meth_BaseModule f gn m)).
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
    + destruct string_dec;[|destruct string_dec]; auto.
      * left; reflexivity.
      * apply False_ind, H; subst; auto.
      * left; reflexivity.
    + destruct string_dec;[|destruct string_dec]; auto.
      * right; assumption.
      * right; apply IHl; auto.
      * right; apply IHl; auto.
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
      rewrite HUpds, HExecs, HCalls in *; econstructor 3; simpl; eauto.
      apply IHPPlusSubsteps.
      rewrite map_app, in_app_iff in H2; clear - H2; firstorder fail.
    + specialize (InMeth_In_inlined_neq f _ _ n HInMeths) as P3.
      rewrite HUpds, HExecs, HCalls in *; econstructor 3; eauto.
      apply IHPPlusSubsteps.
      rewrite map_app, in_app_iff in H2; clear - H2; firstorder fail.
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
  - simpl; destruct string_dec; simpl; auto.
  - simpl; destruct string_dec;
      [simpl
      |destruct string_dec; simpl;
       [destruct a; simpl; rewrite IHl
       |rewrite IHl]
      ];reflexivity.
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
        [|destruct string_dec; subst;[apply False_ind; simpl in H; apply H|]];left;reflexivity.
    + simpl; destruct string_dec;
        [|destruct string_dec];right;auto; apply IHl; auto; simpl in *; firstorder fail.
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
    + simpl; destruct string_dec;[left|apply False_ind, n];reflexivity.
    + simpl; destruct string_dec;[right|apply False_ind, n];auto.
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
  specialize (H1 (evalExpr e)).
  apply (WfActionT_inline_Meth); auto.
Qed.
     
Lemma inlineSingle_Meth_BaseModule_dec meth f gn l:
  In meth (inlineSingle_Meth_in_list f gn l) ->
  In meth l \/
  exists meth',
    In meth' l /\
    (inlinesingle_Meth f meth' = meth). 
Proof.
  induction l.
  - intros; simpl in H; destruct string_dec; contradiction.
  - simpl; destruct string_dec; subst; intros.
    + destruct H; subst.
      * left; left; reflexivity.
      * left; right; assumption.
    + destruct string_dec; subst.
      * destruct H; subst.
        -- right; exists a.
           split; auto.
        -- specialize (IHl H).
           destruct IHl;[left|destruct H0; dest; right; exists x];auto.
      *  destruct H; subst;[left;left|destruct (IHl H); dest; subst]; auto.
         destruct (IHl H);[left; right; auto|dest].
         right; exists x0;split; auto.
Qed.

Lemma WfMod_Meth_inlined m f gn :
  WfMod (Base m) ->
  In f (getMethods m) ->
  WfMod (Base (inlineSingle_Meth_BaseModule f gn m)).
Proof.
  intros; inv H; econstructor; eauto.
  - split; intros; simpl in *; inv WfBaseModule.
    + apply WfActionT_inline_Meth; auto.
    + destruct (inlineSingle_Meth_BaseModule_dec _ _ _ _ H).
      * specialize (H2 _ H3 v); apply WfActionT_inline_Meth; auto.
      * dest.
        destruct x, s0, meth, s1; inv H4; EqDep_subst.
        specialize (H2 _ H3) as P1.
        apply WfActionT_inline_Meth_inline_action; auto.
  - simpl; rewrite SameKeys_inline_Meth; assumption.
Qed.

Lemma PPlusStrongTraceInclusion_inlining_Meth_r m f gn :
  In f (getMethods m) ->
  WfMod (Base m) ->
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
      * rewrite in_map_iff in i; dest; inv H0; destruct x0; simpl in *.
        specialize (PPlusStep_inline_Meth_In _ _ H5 H NoDupRle NoDupMeths n HPPlusStep) as TMP; dest.
        exists ((upds, (x1, x2))::x); split.
        -- econstructor 2; eauto.
        -- constructor; auto.
           unfold WeakInclusion_flat, getListFullLabel_diff_flat; simpl; split; intros; auto.
           ++ rewrite H0, H4, getNumFromExecs_app, getNumFromCalls_app, call_execs_counts_eq; Omega.omega.
           ++ dest; exists x3; rewrite H0, in_app_iff; right; assumption.
      * exists ((upds, (execs, calls))::x); split.
        -- econstructor 2; eauto.
           apply PPlusStep_inline_Meth_NotInDef; auto.
        -- constructor; auto.
           unfold WeakInclusion_flat; split; intros; auto.
Qed.

Corollary TraceInclusion_inlining_Meth_r m f gn :
  In f (getMethods m) ->
  WfMod (Base m) ->
  TraceInclusion (Base m) (Base (inlineSingle_Meth_BaseModule f gn m)).
Proof.
  intros.
  apply PPlusTraceInclusion_TraceInclusion; auto.
  apply (WfMod_Meth_inlined); auto.
  eauto using StrongPPlusTraceInclusion_PPlusTraceInclusion, PPlusStrongTraceInclusion_inlining_Meth_r.
Qed.