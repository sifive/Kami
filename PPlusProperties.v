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
            (HNoCycle: ~In fn (map fst cs))
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
    PSemAction_meth_collector f o reads1 upds1 calls1 calls1' /\
    PSemAction_meth_collector f o reads2 upds2 calls2 calls2'.
Proof.
  induction calls1'; simpl; intros.
  - exists nil, reads, nil, upds, nil, calls.
    repeat split; auto.
    constructor.
  - specialize (Produce_action_from_collector _ (in_eq _ _) H) as TMP; dest.
    apply Permutation_cons_inv in H5.
    rewrite <- H5 in H7.
    specialize (IHcalls1' _ _ _ H7) as TMP; dest.
    exists (x0++x8), x9, (x2++x10), x11, (x4++x12), x13.
    repeat split.
    + rewrite H8, app_assoc in H3; assumption.
    + rewrite H9, app_assoc in H1; assumption.
    + rewrite H10, app_assoc in H2; assumption.
    + econstructor.
      * apply H11.
      * rewrite H9 in H0; assert (DisjKey x10  x2);[intro; specialize (H0 k);
                                                     rewrite map_app, in_app_iff in *;clear - H0; firstorder|apply H13].
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
    destruct TMP as [HRr12 [HNr12 [HC12 [HCol1 HCol2]]]].
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
      destruct TMP as [HRr12 [HNr12 [HC12 [HCol1 HCol2]]]].
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
      destruct TMP as [HRr12 [HNr12 [HC12 [HCol1 HCol2]]]].
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

Lemma SubList_app_l_iff:
  forall (A : Type) (l1 l2 ls : list A), SubList (l1 ++ l2) ls <-> SubList l1 ls /\ SubList l2 ls.
Proof.
  split; intro;[apply SubList_app_l; assumption|dest; repeat intro; auto; rewrite in_app_iff in *; firstorder fail].
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

(* Lemma Substeps_inline_Rule_PSubsteps f m o rn fb u1 u2 cs1 cs2 cs3(l : list FullLabel) : *)
(*   NoDup (map fst (getMethods m)) -> *)
(*   In f (getMethods m) -> *)
(*   Substeps m o ((u1, (Meth ((fst f),fb), cs1))::(u2, (Rle rn, cs2++((fst f), fb)::cs3))::l) -> *)
(*   PSubsteps (inlineSingle_Rule_BaseModule f rn m) o ((u1++u2, (Rle rn, cs1++cs2++cs3))::l). *)
(* Proof. *)
(*   intros. *)
(*   (* specialize (PPlusSubsteps_NoDup_Key_Calls (PSubsteps_PPlusSubsteps(Substeps_PSubsteps H1))) as NDup_Calls. *) *)
(*   apply extract_exec in H1; auto; dest; subst; simpl in *. *)
(*   inv H4. *)
(*   - inv HLabel. *)
(*     assert (DisjKey u1 u) as P1; *)
(*       [unfold getLabelUpds in H2; simpl in *; intro k; specialize (H2 k); *)
(*        rewrite map_app, in_app_iff, DeM1 in H2; clear - H2; firstorder fail|]. *)
(*     (* assert (DisjKey cs1 (cs2++(fst f,  existT _ (projT1 (snd f))(x0, x1))::cs3)) as P2; *) *)
(*     (*   [unfold getLabelCalls in H3; simpl in *; intro k; specialize (H3 k); simpl in *; *) *)
(*     (*    rewrite map_app, in_app_iff in H3;tauto|]. *) *)
(*     assert (In ((fst f, existT SignT (projT1 (snd f)) (x0, x1))) (cs2++((fst f, existT SignT (projT1 (snd f)) (x0, x1)))::cs3)) as P2; *)
(*     [rewrite in_app_iff; right;left; reflexivity|]. *)
(*     (* assert (key_not_In (fst f) (cs2++cs3)) as P4; *) *)
(*     (*   [apply SemAction_PSemAction,PSemAction_NoDup_Key_Calls in HAction; rewrite map_app, NoDup_app_iff in HAction;dest; *) *)
(*     (*    inv H8; repeat intro; apply (in_map fst) in H8; rewrite map_app,in_app_iff in H8; destruct H8; auto; *) *)
(*     (*    specialize (H10 (fst f) (in_eq _ _)); contradiction|]. *) *)
(*     (* apply key_not_In_filter in P4. *) *)
(*     econstructor 2; simpl; auto. *)
(*     + rewrite HRegs; reflexivity. *)
(*     + apply (InRule_In_inlined f _ _ _ HInRules). *)
(*     + simpl. *)
(*       apply SemAction_PSemAction in H3. *)
(*       apply SemAction_PSemAction in HAction. *)
(*       specialize (PSemAction_inline_In _ _ H3 P1 P2 HAction) as P5. *)
(*       assert ((cs1 ++ (filter (remove_calls f) (cs2 ++ (fst f, existT SignT (projT1 (snd f)) (x0, x1)) :: cs3))) *)
(*                 [=] cs1 ++ (filter (remove_calls f) ((fst f, existT _ (projT1 (snd f)) (x0, x1))::cs2++cs3))); *)
(*         [apply Permutation_app_head; rewrite Permutation_app_comm; simpl; destruct string_dec; simpl;rewrite Permutation_app_comm;[|apply perm_skip];reflexivity|]. *)
(*       apply (PSemAction_rewrite_calls H1) in P5. *)
(*       simpl in P5; destruct string_dec in P5;[|apply False_ind; apply n; reflexivity]; simpl in P5. *)
(*       setoid_rewrite P4 in P5. *)
(*       apply P5. *)
(*     + rewrite map_app,SubList_app_l_iff; auto. *)
(*     + rewrite map_app,SubList_app_l_iff; auto. *)
(*     + intros; specialize (HDisjRegs _ H1). *)
(*       intro k; specialize (HDisjRegs k); specialize (H2 k). *)
(*       unfold getLabelUpds in H2; simpl in H2. *)
(*       rewrite map_app, in_app_iff, DeM1 in *. *)
(*       specialize (in_split _ _ H1) as TMP; dest; rewrite H8 in H2. *)
(*       rewrite map_app, concat_app in H2; simpl in H2. *)
(*       repeat rewrite map_app,in_app_iff,DeM1 in H2. *)
(*       clear - H2 HDisjRegs; firstorder fail. *)
(*     + repeat setoid_rewrite in_app_iff; intros. *)
(*       destruct H1;[|destruct H1; setoid_rewrite in_app_iff in HNoCall; *)
(*                     simpl in *;simpl in *; [apply (HNoCall _ (or_introl _ H1) _ H8) *)
(*                                            |apply (HNoCall _ (or_intror _ (or_intror _ H1)) _ H8)]]. *)
(*       rewrite InCall_getLabelCalls_iff in H8. *)
(*       apply (in_map fst) in H8; apply (in_map fst) in H1; destruct f0; unfold getLabelCalls in H3; simpl in *. *)
(*       specialize (H3 s); simpl in *. *)
(*       rewrite map_app, in_app_iff in H3. *)
(*       clear - H1 H8 H3; firstorder fail. *)
(*     + unfold getLabelCalls in NDup_Calls; simpl in *. *)
(*       rewrite map_app in NDup_Calls; simpl in *; rewrite map_app in NDup_Calls. *)
(*       apply Substeps_PSubsteps in HSubstep. *)
(*       fold (getLabelCalls ls) in NDup_Calls. *)
(*       rewrite NoDup_app_iff in NDup_Calls; dest. *)
(*       rewrite map_app in H8; simpl in H8. *)
(*       rewrite NoDup_app_iff in H8; dest. *)
(*       setoid_rewrite in_app_iff in H12. *)
(*       specialize (H12 (fst f) (or_intror _ (in_eq _ _ ))). *)
(*       apply PSubsteps_inlineRule_notIn; auto. *)
(*   - inv HLabel. *)
(* Qed. *)

(* Lemma RuleOrMeth_dec : *)
(*   forall (rm1 rm2 : RuleOrMeth), *)
(*     {rm1=rm2}+{rm1<>rm2}. *)
(* Proof. *)
(*   decide equality. *)
(*   - apply string_dec. *)
(*   - apply MethT_dec. *)
(* Qed. *)

(* Corollary PSubsteps_inline_Rule_PSubsteps f m o rn fb u1 u2 cs1 cs2 cs3 (l : list FullLabel) : *)
(*   NoDup (map fst (getMethods m)) -> *)
(*   In f (getMethods m) -> *)
(*   PSubsteps m o ((u1, (Meth ((fst f),fb), cs1))::(u2, (Rle rn, cs2++((fst f), fb)::cs3))::l) -> *)
(*   PSubsteps (inlineSingle_Rule_BaseModule f rn m) o ((u1++u2, (Rle rn, cs1++cs2++cs3))::l). *)
(* Proof. *)
(*   intros. *)
(*   apply PSubsteps_Substeps in H1; dest. *)
(*   specialize (List_FullLabel_perm_in H2 _ (in_eq _ _)) as TMP; dest. *)
(*   assert (In (u2, (Rle rn, cs2++((fst f), fb)::cs3)) (((u1, (Meth (fst f, fb), cs1)) :: (u2, (Rle rn, cs2++((fst f), fb)::cs3)) :: l))); *)
(*     [simpl; right;left; reflexivity|]. *)
(*   specialize (List_FullLabel_perm_in H2 _ H7) as TMP; dest. *)
(*   inv H5; inv H8; subst. *)
(*   assert (In (fst f, fb) cs'0); *)
(*     [rewrite <- H17, <-Permutation_middle; left; reflexivity|]. *)
(*   apply in_split in H5; dest. *)
(*   rewrite H5 in H9. *)
(*   apply in_split in H9; dest; subst. *)
(*   rewrite <-Permutation_middle in H6; simpl in *. *)
(*   destruct H6;[discriminate|]. *)
(*   rewrite <-Permutation_middle in H4. *)
(*   apply in_split in H5; dest; subst. *)
(*   rewrite H5 in H4. *)
(*   assert (((u'0, (Rle rn, x1 ++ (fst f, fb) :: x2)) :: x0 ++ (u', (Meth (fst f, fb), cs')) :: x5) *)
(*             [=] ((u', (Meth (fst f, fb), cs'))::(u'0, (Rle rn, x1 ++ (fst f, fb) :: x2)) :: x0++x5)); *)
(*     [rewrite perm_swap; apply perm_skip; rewrite Permutation_app_comm; simpl;apply perm_skip, Permutation_app_comm|]. *)
(*   rewrite H6 in H4. *)
(*   specialize (Substeps_inline_Rule_PSubsteps _ _ _ H H0 H4) as Final. *)
(*   specialize (Permutation_middle x3 x4 (u'0, (Rle rn, x1 ++ (fst f, fb) :: x2))) as P1. *)
(*   rewrite <- P1 in H2. *)
(*   rewrite H5 in H2. *)
(*   rewrite H6 in H2. *)
(*   apply List_FullLabel_perm_cons_inv in H2;[|constructor; auto]. *)
(*   apply List_FullLabel_perm_cons_inv in H2;[|constructor; auto]. *)
(*   assert (FullLabel_perm (u1 ++ u2, (Rle rn, cs1 ++ cs2 ++ cs3)) (u' ++ u'0, (Rle rn, cs' ++ x1 ++ x2))). *)
(*   + constructor; auto. *)
(*     * rewrite H13, H12; reflexivity. *)
(*     * repeat rewrite <-Permutation_middle in H17. *)
(*       apply Permutation_cons_inv in H17. *)
(*       rewrite H16, H17; reflexivity. *)
(*   + rewrite (LFL_eq_cons_1 H8 H2). *)
(*     rewrite H1. *)
(*     assumption. *)
(* Qed. *)

(* Global Instance WeakInclusion_perm_rewrite' : *)
(*   Proper (@Permutation FullLabel ==> @Permutation FullLabel ==> iff) (@WeakInclusion) | 10. *)
(* Proof. *)
(*   repeat red. intros; split; intro. *)
(*   - apply Permutation_sym in H. *)
(*     apply (WeakInclusionTrans (WeakInclusionTrans (PermutationWI H) H1) (PermutationWI H0)). *)
(*   - apply Permutation_sym in H0. *)
(*     apply (WeakInclusionTrans (WeakInclusionTrans (PermutationWI H) H1) (PermutationWI H0)). *)
(* Qed. *)

(* Lemma Separate_Action (f : DefMethT) (k : Kind) (a : ActionT type k) : *)
(*   forall o reads upds calls (retV : type k), *)
(*     SemAction o (inlineSingle f a) reads upds calls retV -> *)
(*     SemAction o a reads upds calls retV \/ *)
(*     (exists reads1 reads2 upds1 upds2 calls1 calls2 (x : type (fst (projT1 (snd f))))  (y : type (snd (projT1 (snd f)))), *)
(*         reads [=] reads1 ++ reads2 /\ *)
(*         upds [=] upds1 ++ upds2 /\ *)
(*         calls [=] (fst f, existT _ (projT1 (snd f))(x, y))::calls1 ++ calls2 /\ *)
(*         SemAction o a reads1 upds1 calls1 retV /\ *)
(*         SemAction o (projT2 (snd f) _ x) reads2 upds2 calls2 y). *)
(* Proof. *)
(* Admitted. *)

(* Lemma PStep_NoDup_Key_Calls m o l: *)
(*   PStep (Base m) o l -> *)
(*   NoDup (map fst (getLabelCalls l)). *)
(* Proof. *)
(*   intros. *)
(*   apply PStep_PPlusStep in H. *)
(*   inv H. *)
(*   apply PPlusSubsteps_NoDup_Key_Calls in H0; assumption. *)
(* Qed. *)

(* Lemma PPlusSubsteps_NoDup_Execs m o upds execs calls: *)
(*   PPlusSubsteps m o upds execs calls -> *)
(*   NoDup execs. *)
(* Proof. *)
(*   induction 1. *)
(*   - constructor. *)
(*   - rewrite HExecs; constructor; auto. *)
(*     intro H1; apply (HNoRle _ H1). *)
(*   - rewrite HExecs; constructor; auto. *)
(* Qed. *)

(* Corollary PStep_NoDup_Execs m o l : *)
(*   PStep (Base m) o l -> *)
(*   NoDup (getLabelExecs l). *)
(* Proof. *)
(*   intro. *)
(*   apply PStep_PPlusStep in H. *)
(*   inv H. *)
(*   apply PPlusSubsteps_NoDup_Execs in H0. *)
(*   assumption. *)
(* Qed. *)

(* Lemma PSubsteps_NoCycle m o l u f cs: *)
(*   In (u, (Meth f, cs)) l -> *)
(*   PSubsteps m o l -> *)
(*   ~In f cs. *)
(* Proof. *)
(*   induction 2; auto. *)
(*   - rewrite HLabel in H. *)
(*     destruct H; [inv H|]. *)
(*     apply IHPSubsteps; auto. *)
(*   - rewrite HLabel in H. *)
(*     destruct H. *)
(*     + inv H. *)
(*       intro; apply (in_map fst) in H; simpl in *; contradiction. *)
(*     + apply IHPSubsteps; auto. *)
(* Qed. *)

(* Lemma DeM2 P Q : *)
(*   ~(P \/ Q) <-> ~P /\ ~Q. *)
(* Proof. tauto. Qed. *)

(* Lemma WeakInclusion_flat_add_exec_call (t : RegsT *(list RuleOrMeth * MethsT)) (f : MethT) : *)
(*   (forall v, ~In (fst f, v) (snd (snd t))) -> *)
(*   (forall v, ~In (Meth (fst f, v)) (fst (snd t))) -> *)
(*   WeakInclusion_flat (fst t, (((Meth f)::(fst (snd t))), (f::(snd (snd t))))) t. *)
(* Proof. *)
(*   unfold WeakInclusion_flat; simpl. *)
(*   repeat split; repeat intro; try rewrite DeM2 in *; dest; auto. *)
(*   - destruct H1; auto. *)
(*     apply False_ind; apply H2; inv H1;reflexivity. *)
(*   - destruct H2; auto. *)
(*     subst; destruct f0; simpl in *. *)
(*     specialize (H0 s0); contradiction. *)
(*   - destruct H2;[subst;apply False_ind, H1|];auto. *)
(*   - destruct H2; [inv H2;destruct f0; specialize (H s0)|];auto. *)
(*   - destruct H1; dest. *)
(*     + destruct f0; destruct H1, H2; auto;[subst; auto *)
(*                                          |inv H1;specialize (H s0);contradiction *)
(*                                          |subst;specialize (H0 s0); contradiction]. *)
(*     + right; split; repeat intro. *)
(*       * specialize (H1 v); rewrite DeM2 in H1; dest; contradiction. *)
(*       * specialize (H2 v); rewrite DeM2 in H2; dest; contradiction. *)
(*   - destruct H1; dest. *)
(*     + left; split; auto. *)
(*     + admit. *)
(*   - admit. *)
(* Admitted. *)

(* Lemma PStep_inline_Rule_PStep f rn m o (l : list FullLabel) : *)
(*   NoDup (map fst (getMethods m)) -> *)
(*   In f (getMethods m) -> *)
(*   PStep (Base m) o l -> *)
(*   exists l', *)
(*     WeakInclusion l l' /\ *)
(*     PStep (Base (inlineSingle_Rule_BaseModule f rn m)) o l'. *)
(* Proof. *)
(*   intros. *)
(*   specialize (PStep_NoDup_Key_Calls H1) as NDupCalls. *)
(*   specialize (PStep_NoDup_Execs H1) as NDupExecs. *)
(*   inv H1; unfold MatchingExecCalls in *. *)
(*   destruct (in_dec RuleOrMeth_dec (Rle rn) (map getRleOrMeth l)). *)
(*   - rewrite in_map_iff in i; dest. *)
(*     destruct x, p; simpl in *; subst. *)
(*     destruct (in_dec string_dec (fst f) (map fst m0)). *)
(*     + rewrite in_map_iff in i; dest. *)
(*       destruct x; simpl in *; subst. *)
(*       apply in_split in H3; dest; subst. *)
(*       assert (InCall (fst f, s0) l); *)
(*         [unfold InCall; exists  (r, (Rle rn, x ++ (fst f, s0) :: x0)); split; simpl; auto; *)
(*          rewrite in_app_iff; right;left; reflexivity|]. *)
(*       specialize (HMatching _ H1 (in_map fst _ _ H0)); dest. *)
(*       unfold InExec in H4; rewrite in_map_iff in H4; dest. *)
(*       destruct x1, p; simpl in *; subst. *)
(*       apply in_split in H5; dest; subst. *)
(*       specialize (Permutation_middle x1 x2 (r0, (Meth (fst f, s0), m0))) as RWRT. *)
(*       rewrite <-RWRT in *. *)
(*       specialize (PSubsteps_NoCycle _ _ _ (in_eq _ _) HPSubsteps) as NoCycle1. *)
(*       destruct H2;[inv H2|]. *)
(*       apply in_split in H2; dest. *)
(*       specialize (Permutation_middle x3 x4 (r, (Rle rn, x++(fst f, s0)::x0))) as RWRT2;setoid_rewrite <-H2 in RWRT2. *)
(*       rewrite <-RWRT2 in HPSubsteps. *)
(*       apply (PSubsteps_inline_Rule_PSubsteps _ _ _ H H0) in HPSubsteps. *)
(*       exists ((r0 ++ r, (Rle rn, m0 ++ x ++ x0)) :: x3 ++ x4). *)
(*       rewrite <- RWRT2 in RWRT. *)
(*       rewrite <- RWRT. *)
(*       rewrite <- RWRT2 in NDupExecs, NDupCalls. *)
(*       unfold getLabelCalls, getLabelExecs in *; simpl in *; repeat rewrite map_app in *. *)
(*       rewrite concat_app, map_app in NDupCalls; simpl in *. *)
(*       split. *)
(*       * admit. *)
(*       * admit. *)
(*     + apply in_split in H2; dest; subst. *)
(*       rewrite <- Permutation_middle in *. *)
(*       apply (PSubsteps_inline_Rule_NoCall_PSubsteps f) in HPSubsteps; auto. *)
(*       exists ((r, (Rle rn, m0))::x++x0); split;[|econstructor 1; auto]. *)
(*       * apply PermutationWI, Permutation_sym, Permutation_middle. *)
(*       *  rewrite Permutation_middle; auto. *)
(*   - apply (PSubsteps_inline_Rule_NoExec_PSubsteps f rn) in HPSubsteps; auto. *)
(*     exists l; split;[apply WeakInclusionRefl|econstructor 1; auto]. *)
(* Admitted. *)

(* Lemma PPlusSubsteps_inline_MatchingIn f m o upds execs calls fb: *)
(*   NoDup (map fst (getMethods m)) -> *)
(*   In f (getMethods m) -> *)
(*   PPlusSubsteps m o upds ((Meth ((fst f), fb))::execs) (((fst f), fb)::calls) -> *)
(*   PPlusSubsteps (inlinesingle_BaseModule m f) o upds execs calls. *)
(* Proof. *)
(*   intros; apply extract_exec_PPlus in H1; auto; dest; subst; simpl in *. *)
(*   inv H10; subst; simpl in *. *)
(*   - rewrite app_nil_r in H4. *)
(*     specialize (in_map fst _ _ (Permutation_in _ H4 (in_eq _ _))) as contrad; contradiction. *)
(*   - rewrite HExecs. *)
(*     specialize (Permutation_in _ H4 (in_eq _ _)) as TMP. *)
(*     rewrite in_app_iff in TMP; simpl in *; destruct TMP as [H1 | H1] ;[apply (in_map fst) in H1; contradiction|]. *)
(*     rewrite HCalls, in_app_iff in H1; destruct H1. *)
(*     + destruct (in_dec MethT_dec (fst f, existT _ (projT1 (snd f)) (x4, x5)) oldCalls); *)
(*         [specialize (HNoCall _ H1 _ i); contradiction|]. *)
(*       assert (~In (fst f) (map fst oldCalls));[intro; rewrite in_map_iff in H10; dest; destruct x6; *)
(*                                                simpl in *; subst; specialize (HNoCall _ H1 _ H11); contradiction|]. *)
(*       specialize (PPlusSubsteps_inline_notIn _ HPSubstep H10) as HNotIn_Substep. *)
(*       specialize (in_map (inlinesingle_Rule f) _ _ HInRules) as HInRules_inline; simpl in *. *)
(*       assert (DisjKey x0 u) as P1; *)
(*         [intro k; specialize (H5 k); rewrite HUpds,map_app,in_app_iff,DeM1 in H5; clear - H5; firstorder fail|]. *)
(*       assert (DisjKey x2 cs) as P2; *)
(*         [intro k; specialize (H6 k); rewrite HCalls,map_app,in_app_iff,DeM1 in H6; clear - H6; firstorder fail|]. *)
(*       specialize (PSemAction_inline_In _ _ H2 P1 P2 H1 HPAction) as HIn_PSemAction. *)
(*       admit. *)
(*     + admit. *)
(*   - admit. *)
(* Admitted. *)
(*       (* econstructor 2; simpl; auto. *) *)
(*       (* * apply HInRules_inline. *) *)
(*       (* * simpl; apply HIn_PSemAction. *) *)
(*       (* * rewrite map_app, SubList_app_l_iff; auto. *) *)
(*       (* * rewrite map_app, SubList_app_l_iff; auto. *) *)
(*       (* * rewrite H3, HUpds, app_assoc; reflexivity. *) *)
(*       (* *  *) *)
    
(* Lemma PPlusSubsteps_inline f m o upds execs calls: *)
(*   PPlusSubsteps m o upds execs calls -> *)
(*   PPlusSubsteps (inlinesingle_BaseModule m f) o upds *)
(*                 (filter (remove_execs (filter (keep_calls f) calls)) execs) *)
(*                 (filter (remove_calls f) calls). *)
(* Proof. *)
(*   induction 1; simpl in *. *)
(*   - econstructor 1; eauto. *)
(*   - econstructor 2; auto. *)
(*     + apply (in_map (inlinesingle_Rule f)) in HInRules; simpl in *. *)
(*       apply HInRules. *)
(*     + admit. *)
(*     + admit. *)
(*     + admit. *)
(*     + admit. *)
(*     + admit. *)
(*     + admit. *)
(*     + admit. *)
(*     + admit. *)
(*     + admit. *)
(*     + admit. *)
(*   - admit. *)
(* Admitted. *)