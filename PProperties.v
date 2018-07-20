Require Import Kami.Syntax.
Require Import Kami.Properties.
Import ListNotations.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.PermutEq.
Require Import RelationClasses Setoid Morphisms.

Lemma PSemAction_SemAction o k:
  forall (a : ActionT type k) (readRegs newRegs : RegsT) (calls : MethsT) (fret : type k),
    PSemAction o a readRegs newRegs calls fret ->
    (exists (readRegs' newRegs' : RegsT) (calls' : MethsT),
        readRegs [=] readRegs' /\
        newRegs [=] newRegs' /\
        calls [=] calls' /\
        SemAction o a readRegs' newRegs' calls' fret).
Proof.
  induction 1; dest.
  - exists x, x0, ((meth, existT SignT s (evalExpr marg, mret))::x1).
    repeat split; eauto.
    + rewrite <- H2; assumption.
    + econstructor 1; auto.
      * unfold key_not_In in HDisjCalls.
        intro; specialize (HDisjCalls v); rewrite H2 in HDisjCalls; eauto.
  - exists x, x0, x1.
    repeat split; eauto.
    econstructor 2; assumption.
  - exists (x2++x), (x3++x0), (x4++x1).
    rewrite H1, H5 in HUReadRegs; rewrite H2, H6 in HUNewRegs; rewrite H3, H7 in HUCalls.
    repeat split; auto.
    + econstructor 3; eauto.
      * intro; specialize (HDisjRegs k0); rewrite <- H6, <- H2; assumption.
      * intro; specialize (HDisjCalls k0); rewrite <- H7, <- H3; assumption.
  - exists x, x0, x1.
    repeat split; auto.
    econstructor 4; eauto.
  - exists ((r, existT (fullType type) regT regV)::x), x0, x1.
    repeat split; eauto.
    + rewrite <- H0; assumption.
    + econstructor 5; eauto.
  - exists x, ((r, existT (fullType type) k (evalExpr e))::x0), x1.
    repeat split; eauto.
    + rewrite <- H1; assumption.
    + econstructor 6; auto.
      intro; specialize (HDisjRegs v); rewrite H1 in HDisjRegs; apply HDisjRegs.
  - exists (x2++x), (x3++x0), (x4++x1).
    rewrite H1, H5 in HUReadRegs; rewrite H2, H6 in HUNewRegs; rewrite H3, H7 in HUCalls.
    repeat split; auto.
    econstructor 7; auto.
    + intro; specialize (HDisjRegs k); rewrite H2, H6 in HDisjRegs; apply HDisjRegs.
    + intro; specialize (HDisjCalls k); rewrite H3, H7 in HDisjCalls; apply HDisjCalls.
    + apply H8.
    + assumption.
  - exists (x2++x), (x3++x0), (x4++x1).
    rewrite H1, H5 in HUReadRegs; rewrite H2, H6 in HUNewRegs; rewrite H3, H7 in HUCalls.
    repeat split; auto.
    econstructor 8; auto.
    + intro; specialize (HDisjRegs k); rewrite H2, H6 in HDisjRegs; apply HDisjRegs.
    + intro; specialize (HDisjCalls k); rewrite H3, H7 in HDisjCalls; apply HDisjCalls.
    + apply H8.
    + assumption.
  - exists x, x0, x1.
    repeat split; auto.
    econstructor; eauto.
  - exists x, x0, x1.
    repeat split; auto.
    econstructor; eauto.
  - exists nil, nil, nil.
    repeat split; subst; auto.
    econstructor; eauto.
Qed.

Lemma SemAction_PSemAction o k:
  forall (a : ActionT type k) (readRegs newRegs : RegsT) (calls : MethsT) (fret : type k),
    SemAction o a readRegs newRegs calls fret ->
    PSemAction o a readRegs newRegs calls fret.
Proof.
  induction 1; subst.
  - econstructor 1; eauto.
  - econstructor 2; eauto.
  - econstructor 3; eauto.
  - econstructor 4; eauto.
  - econstructor 5; eauto.
  - econstructor 6; eauto.
  - econstructor 7; eauto.
  - econstructor 8; eauto.
  - econstructor 9; eauto.
  - econstructor 10; eauto.
  - econstructor 11; eauto.
Qed.

Lemma key_in_split' : forall (A B C : Type)(l : list (A*B))(x : (A*C)),
    In (fst x) (map fst l) ->
    (exists (l1 l2 : list (A*B))(y : B), l = l1++(((fst x), y)::l2)).
Proof.
  induction l; simpl; intros; auto.
  - contradiction.
  - destruct H.
    + exists nil, l; simpl.
      destruct a, x; simpl in *; subst.
      exists b; reflexivity.
    + specialize (IHl _ H).
      dest.
      exists (a::x0), x1.
      simpl. exists x2.
      rewrite H0; reflexivity.
Qed.

Lemma map_in_split A B (f : A -> B):
  forall (l : list A)(x : A),
    In (f x) (map f l) -> (exists (l1 l2 : list A), (map f l) = (map f l1)++((f x)::(map f l2))).
Proof.
  induction l; simpl; intros; auto.
  - contradiction.
  - destruct H.
    + exists nil, l; simpl.
      rewrite H; reflexivity.
    + specialize (IHl _ H).
      dest.
      exists (a::x0), x1.
      simpl.
      rewrite H0; reflexivity.
Qed.

Lemma getKindAttr_perm_eq (A B : Type)(P : B -> Type)(Q : B -> Type) :
  forall (l1 : list (A * {x : B & P x}))(l2 : list (A * {x : B & Q x})),
  getKindAttr l1 [=] getKindAttr l2 ->
  (exists l2', l2 [=] l2' /\
               getKindAttr l2' = getKindAttr l1).
Proof.
  induction l1.
  - intros.
    exists nil.
    repeat split; auto.
    destruct l2;[reflexivity|specialize (Permutation_nil H);discriminate].
  - simpl; intros.
    assert (In (fst a, projT1 (snd a)) (getKindAttr l2));[rewrite <- H; left; reflexivity|].
    rewrite in_map_iff in H0; dest.
    specialize (in_split _ _ H1) as TMP; dest; subst.
    rewrite map_app in H; simpl in H; rewrite H0 in H.
    specialize (Permutation_cons_app_inv _ _ H) as TMP.
    rewrite <- map_app in TMP.
    specialize (IHl1 _ TMP); dest.
    exists (x::x2); split.
    rewrite <- H2; symmetry; apply Permutation_cons_app; reflexivity.
    simpl; rewrite H3, H0; reflexivity.
Qed.

Lemma fst_produce_snd A B:
  forall (l : list (A * B)) (a : A),
    In a (map fst l) -> (exists (b : B), In (a, b) l).
Proof.
  induction l; simpl; intros.
  - inversion H.
  - destruct a.
    destruct H.
    + exists b.
      inversion H; subst.
      left; reflexivity.
    + specialize (IHl _ H); dest.
      exists x.
      right; assumption.
Qed.

Lemma key_perm_eq (A B C : Type):
  forall (l : list (A*C))(l' : list (A*B)),
    (map fst l) [=] (map fst l') ->
    (exists l'',
        l' [=] l'' /\
        map fst l = map fst l'').
Proof.
  induction l.
  - intros.
    apply Permutation_nil,map_eq_nil in H; subst;exists nil; split; auto.
  - intros.
    specialize (key_in_split' _ _ (Permutation_in _ H (in_eq _ _))) as TMP; dest.
    rewrite H0 in H; simpl in H; rewrite map_app in H;simpl in H;apply Permutation_cons_app_inv in H.
    rewrite <- map_app in H.
    specialize (IHl _ H); dest.
    exists ((fst a, x1)::x2); split.
    + rewrite H0, <- H1; symmetry; apply Permutation_middle.
    + simpl; rewrite H2; reflexivity.
Qed.
      

Section PSemAction_rewrites.
  Variable (k : Kind) (a : ActionT type k) (fret : type k).
  Lemma PSemAction_rewrite_state  readRegs newRegs calls o1 o2:
      (o1 [=] o2) ->
      PSemAction o1 a readRegs newRegs calls fret ->
      PSemAction o2 a readRegs newRegs calls fret.
  Proof.
    induction 2.
    - econstructor 1; eauto.
    - econstructor 2; eauto.
    - econstructor 3; eauto.
    - econstructor 4; eauto.
    - econstructor 5; eauto.
      rewrite <- H.
      assumption.
    - econstructor 6; eauto.
      rewrite <- H.
      assumption.
    - econstructor 7; eauto.
    - econstructor 8; eauto.
    - econstructor 9; eauto.
    - econstructor 10; eauto.
    - econstructor 11; eauto.
  Qed.

  Lemma PSemAction_rewrite_calls readRegs newRegs calls1 calls2 o:
    (calls1 [=] calls2) ->
    PSemAction o a readRegs newRegs calls1 fret ->
    PSemAction o a readRegs newRegs calls2 fret.
  Proof.
    induction 2.
    - econstructor 1; eauto.
      rewrite <- H; assumption.
    - econstructor 2; eauto.
    - econstructor 3; eauto.
      rewrite <- H; assumption.
    - econstructor 4; eauto.
    - econstructor 5; eauto.
    - econstructor 6; eauto.
    - econstructor 7; eauto.
      rewrite <- H; assumption.
    - econstructor 8; eauto.
      rewrite <- H; assumption.
    - econstructor 9; eauto.
    - econstructor 10; eauto.
    - econstructor 11; eauto.
      rewrite HCalls in H; apply (Permutation_nil H).
  Qed.

  Lemma SubList_refl A (l : list A) :
    SubList l l.
  Proof.
    firstorder.
  Qed.

  Global Instance SubList_PreOrder A : PreOrder (@SubList A) | 10 := {
  PreOrder_Reflexive := (@SubList_refl A);
  PreOrder_Transitive := (@SubList_transitive A)}.

  Lemma PSemAction_rewrite_readRegs readRegs1 readRegs2 newRegs calls o:
    readRegs1 [=] readRegs2 ->
    PSemAction o a readRegs1 newRegs calls fret ->
    PSemAction o a readRegs2 newRegs calls fret.
  Proof.
    induction 2.
    - econstructor 1; eauto.
    - econstructor 2; eauto.
    - econstructor 3; eauto.
      rewrite <- H; assumption.
    - econstructor 4; eauto.
    - econstructor 5; eauto.
      rewrite <- H; assumption.
    - econstructor 6; eauto.
    - econstructor 7; eauto.
      rewrite <- H; assumption.
    - econstructor 8; eauto.
      rewrite <- H; assumption.
    - econstructor 9; eauto.
    - econstructor 10; eauto.
    - econstructor 11; eauto.
      rewrite HReadRegs in H; apply (Permutation_nil H).
  Qed.

  Lemma PSemAction_rewrite_newRegs readRegs newRegs1 newRegs2 calls o:
    newRegs1 [=] newRegs2 ->
    PSemAction o a readRegs newRegs1 calls fret ->
    PSemAction o a readRegs newRegs2 calls fret.
  Proof.
    induction 2.
    - econstructor 1; eauto.
    - econstructor 2; eauto.
    - econstructor 3; eauto.
      rewrite <- H; assumption.
    - econstructor 4; eauto.
    - econstructor 5; eauto.
    - econstructor 6; eauto.
      rewrite <- H; assumption.
    - econstructor 7; eauto.
      rewrite <- H; assumption.
    - econstructor 8; eauto.
      rewrite <- H; assumption.
    - econstructor 9; eauto.
    - econstructor 10; eauto.
    - econstructor 11; eauto.
      rewrite HNewRegs in H; apply (Permutation_nil H).
  Qed.
  
  Global Instance PSemAction_rewrite' :
    Proper (@Permutation (string * {x : FullKind & fullType type x}) ==>
                         @Permutation (string * {x : FullKind & fullType type x}) ==>
                         @Permutation (string * {x : FullKind & fullType type x}) ==>
                         @Permutation MethT ==>
                         iff) (fun w x y z => @PSemAction w k a x y z fret) |10.
  Proof.
    repeat red; subst; split; intros; eauto using PSemAction_rewrite_state, PSemAction_rewrite_calls, PSemAction_rewrite_readRegs, PSemAction_rewrite_newRegs.
    apply Permutation_sym in H; apply Permutation_sym in H0;apply Permutation_sym in H1;apply Permutation_sym in H2.   
    eauto using PSemAction_rewrite_state, PSemAction_rewrite_calls, PSemAction_rewrite_readRegs, PSemAction_rewrite_newRegs.
  Qed.
End PSemAction_rewrites. 

Inductive FullLabel_perm : FullLabel -> FullLabel -> Prop :=
| FL_eq (u u' : RegsT) (cs cs' : MethsT) (rm rm' : RuleOrMeth): u [=] u' -> rm = rm' -> cs [=] cs' -> FullLabel_perm (u, (rm, cs)) (u', (rm', cs')).

Inductive List_FullLabel_perm : list FullLabel -> list FullLabel -> Prop :=
| LFL_eq_nil : List_FullLabel_perm nil nil
| LFL_eq_cons_1 (fl1 fl2 : FullLabel)(ls1 ls2 : list FullLabel): FullLabel_perm fl1 fl2 -> List_FullLabel_perm ls1 ls2 -> List_FullLabel_perm (fl1::ls1) (fl2::ls2)
| LFL_eq_cons_2 (fl1 fl2 fl3 fl4 : FullLabel)(ls1 ls2 : list FullLabel) : FullLabel_perm fl1 fl2 -> FullLabel_perm fl3 fl4 -> List_FullLabel_perm ls1 ls2 -> List_FullLabel_perm (fl1::fl3::ls1) (fl4::fl2::ls2)
| LFL_eq_trans ls1 ls2 ls3 : List_FullLabel_perm ls1 ls2 -> List_FullLabel_perm ls2 ls3 -> List_FullLabel_perm ls1 ls3.

Lemma FullLabel_perm_refl fl :
  FullLabel_perm fl fl.
Proof.
  destruct fl, p; constructor; auto.
Qed.

Lemma FullLabel_perm_sym fl fl' :
  FullLabel_perm fl fl' -> FullLabel_perm fl' fl.
Proof.
  induction 1; econstructor; eauto using Permutation_sym.
Qed.

Lemma FullLabel_perm_trans fl fl' fl'' :
  FullLabel_perm fl fl' -> FullLabel_perm fl' fl'' -> FullLabel_perm fl fl''.
Proof.
  induction 1; intro; inv H2; econstructor;eauto using Permutation_trans.
Qed.

Global Instance FullLabel_perm_Equivalence : Equivalence (@FullLabel_perm) | 10 :={
   Equivalence_Reflexive := @FullLabel_perm_refl;
   Equivalence_Symmetric := @FullLabel_perm_sym;
   Equivalence_Transitive := @FullLabel_perm_trans}.

Lemma List_FullLabel_perm_refl ls :
  List_FullLabel_perm ls ls.
Proof.
  induction ls; econstructor; eauto using FullLabel_perm_refl.
Qed.

Lemma List_FullLabel_perm_sym ls ls':
  List_FullLabel_perm ls ls' -> List_FullLabel_perm ls' ls.
Proof.
  induction 1.
  - econstructor.
  - econstructor 2; eauto using FullLabel_perm_sym.
  - econstructor 3; eauto using FullLabel_perm_sym.
  - econstructor 4; eauto.
Qed.

Lemma List_FullLabel_perm_trans :
  forall (ls ls' ls'' : list FullLabel),
  List_FullLabel_perm ls ls' -> List_FullLabel_perm ls' ls'' -> List_FullLabel_perm ls ls''.
Proof.
  exact LFL_eq_trans.
Qed.

Global Instance List_FullLabel_perm_Equivalence : Equivalence (@List_FullLabel_perm) | 10 :={
   Equivalence_Reflexive := @List_FullLabel_perm_refl;
   Equivalence_Symmetric := @List_FullLabel_perm_sym;
   Equivalence_Transitive := @List_FullLabel_perm_trans}.  

Lemma List_FullLabel_perm_in:
  forall l l', List_FullLabel_perm l l' ->
               forall a,
                 In a l ->
                 (exists x,
                     FullLabel_perm a x /\
                     In x l').
Proof.
  induction 1.
  - contradiction.
  - intros; destruct H1.
    + subst.
      exists fl2; repeat split;[|left]; auto.
    + specialize (IHList_FullLabel_perm _ H1); dest.
      exists x; split;[|right]; auto.
  - intros; destruct H2;[|destruct H2]; subst.
    + exists fl2; repeat split;[|right;left];auto.
    + exists fl4; repeat split;[|left];auto.
    + specialize (IHList_FullLabel_perm _ H2); dest.
      exists x; split; [|right; right]; auto.
  - intros; specialize (IHList_FullLabel_perm1 _ H1); dest.
    specialize (IHList_FullLabel_perm2 _ H3); dest.
    exists x0; repeat split; eauto using FullLabel_perm_trans.
Qed.

Lemma List_FullLabel_perm_getRleOrMeth l1 l2:
  List_FullLabel_perm l1 l2 ->
  (map getRleOrMeth l1) [=] (map getRleOrMeth l2).
Proof.
  induction 1; eauto using Permutation_trans.
  - inv H; simpl.
    econstructor 2; eauto.
  - inv H; inv H0; simpl.
    rewrite perm_swap; repeat econstructor 2; eauto.
Qed.

Corollary List_FullLabel_perm_InExec_rewrite f l1 l2:
  List_FullLabel_perm l1 l2 ->
  InExec f l1 ->
  InExec f l2.
Proof.
  intros; apply List_FullLabel_perm_getRleOrMeth in H.
  unfold InExec.
  rewrite <- H; assumption.
Qed.

Global Instance List_FullLabel_perm_InExec_rewrite' f:
  Proper (List_FullLabel_perm ==> iff) (@InExec f) |10.
Proof.
  repeat red; intros; split; intros; eauto using List_FullLabel_perm_InExec_rewrite, List_FullLabel_perm_sym.
Qed.

Lemma Perm_rewrite_List_FullLabel_perm_l l1 l2:
  l1 [=] l2 ->
  forall l,
    List_FullLabel_perm l1 l ->
    List_FullLabel_perm l2 l.
Proof.
  induction 1.
  - intros; assumption.
  - intros.
    rewrite <- H0.
    econstructor 2.
    + reflexivity.
    + eapply IHPermutation.
      reflexivity.
  - intros.
    rewrite <- H.
    econstructor 3; reflexivity.
  - intros.
    rewrite <- H1.
    eapply IHPermutation2.
    eapply IHPermutation1.
    reflexivity.
Qed.  

Corollary Perm_rewrite_List_FullLabel_perm l1 l2 l3 l4 :
  l1 [=] l2 ->
  l3 [=] l4 ->
  List_FullLabel_perm l1 l3 ->
  List_FullLabel_perm l2 l4.
Proof.
  intros.
  eauto using Perm_rewrite_List_FullLabel_perm_l, List_FullLabel_perm_sym.
Qed.

Global Instance Perm_rewrite_List_FullLabel_perm' :
  Proper (@Permutation FullLabel ==> @Permutation FullLabel ==> iff) (@List_FullLabel_perm) |10.
Proof.
  repeat red; split; intros; eauto using Perm_rewrite_List_FullLabel_perm, Permutation_sym.
Qed.
  
Section Permutation_filter.
  Variable A : Type.
  Variable f : A -> bool.
  
  Lemma Permutation_filter l l':
    l [=] l' -> filter f l [=] filter f l'.
  Proof.
    induction 1; auto.
    - rewrite (filter_app _ (x::nil) l); rewrite (filter_app _ (x::nil) l').
      rewrite IHPermutation; reflexivity.
    - rewrite (filter_app _ (y::x::nil) l); rewrite (filter_app _ (x::y::nil) l).
      apply Permutation_app_tail.
      rewrite (filter_app _ (y::nil) (x::nil)); rewrite (filter_app _ (x::nil) (y::nil)).
      rewrite (Permutation_app_comm); reflexivity.
    - rewrite IHPermutation1; rewrite IHPermutation2; reflexivity.
  Qed.

  Global Instance Permutation_filter' :
    Proper (@Permutation A ==> @Permutation A) (@filter A f) | 10.
  Proof.
    intro; eauto using Permutation_filter.
  Qed.

End Permutation_filter.
Section SubList_rewrites.
  Variable A : Type.

  Lemma SubList_rewrite (l1 l2 l3 l4 : list A):
    l1 [=] l3 -> l2 [=] l4 -> SubList l1 l2 -> SubList l3 l4.
  Proof.
    unfold SubList; intros.
    rewrite <- H0.
    apply (H1 x).
    rewrite H.
    assumption.
  Qed.

  Global Instance SubList_rewrite' :
    Proper (@Permutation A ==> @Permutation A ==> iff) (@SubList A) | 10.
  repeat red; intros; split; eauto using SubList_rewrite, Permutation_sym.
  Qed.
End SubList_rewrites.

Lemma PSubsteps_Substeps m:
  forall (o : RegsT)(l : list FullLabel),
    PSubsteps m o l ->
    (exists (o' : RegsT)(l' : list FullLabel),
        o [=] o' /\
        List_FullLabel_perm l l' /\
        getKindAttr o' = getKindAttr (getRegisters m) /\
        Substeps m o' l').
Proof.
  induction 1.
  - specialize (getKindAttr_perm_eq _ _ _ _ (Permutation_sym HRegs)) as TMP
    ; dest;exists x, nil; repeat split; auto; econstructor 1; eauto.
  - dest; apply (PSemAction_rewrite_state H0) in HPAction; apply PSemAction_SemAction in HPAction; dest.
    exists x, ((x2, (Rle rn, x3))::x0); repeat split; auto;[destruct l|].
    + apply Permutation_nil in HLabel; discriminate.
    + rewrite HLabel.
      econstructor; eauto.
      econstructor; eauto.
    + econstructor 2; eauto.
      * rewrite H4 in HReadsGood; assumption.
      * rewrite H5 in HUpdGood; assumption.
      * intros;specialize (List_FullLabel_perm_in (List_FullLabel_perm_sym H1) _ H8) as TMP; dest;specialize (HDisjRegs _ H10);
          intro; inversion H9; simpl; destruct (HDisjRegs k);[left|right];intro; apply H16.
        -- rewrite <- H15; simpl.
           rewrite <- H11; assumption.
        -- rewrite H5; assumption.
      * intros.
        specialize (List_FullLabel_perm_in (List_FullLabel_perm_sym H1) _ H8) as TMP; dest;specialize (HNoRle _ H10);
          inversion H9;rewrite <- H15 in HNoRle; simpl in *;rewrite H12;assumption.
      * intros;rewrite <- H6 in H8;unfold InCall in H9; dest; specialize (List_FullLabel_perm_in (List_FullLabel_perm_sym H1) _ H9) as TMP;
          dest;inv H11;eapply HNoCall.
        -- apply H8.
        -- unfold InCall;exists (u', (rm', cs'));split; auto; simpl in *;rewrite <- H15; assumption.
  -  dest; apply (PSemAction_rewrite_state H0) in HPAction; apply PSemAction_SemAction in HPAction; dest.
    exists x, ((x2, (Meth (fn, existT SignT (projT1 fb) (argV, retV)), x3))::x0); repeat split; auto;[destruct l|].
    + apply Permutation_nil in HLabel; discriminate.
    + rewrite HLabel.
      econstructor; eauto.
      econstructor; eauto.
    + econstructor 3; eauto.
      * rewrite H4 in HReadsGood; assumption.
      * rewrite H5 in HUpdGood; assumption.
      * intros;specialize (List_FullLabel_perm_in (List_FullLabel_perm_sym H1) _ H8) as TMP; dest;specialize (HDisjRegs _ H10);
          intro; inversion H9; simpl; destruct (HDisjRegs k);[left|right];intro; apply H16.
        -- rewrite <- H15; simpl.
           rewrite <- H11; assumption.
        -- rewrite H5; assumption.
      * intros;rewrite <- H6 in H8;unfold InCall in H9; dest; specialize (List_FullLabel_perm_in (List_FullLabel_perm_sym H1) _ H9) as TMP;
          dest;inv H11;eapply HNoCall.
        -- apply H8.
        -- unfold InCall;exists (u', (rm', cs'));split; auto; simpl in *;rewrite <- H15; assumption.
      * rewrite <- H1; assumption.
Qed.

Lemma Substeps_PSubsteps m:
  forall (o : RegsT) (l : list FullLabel),
    Substeps m o l -> PSubsteps m o l.
  induction 1; subst.
  - econstructor 1; rewrite HRegs; reflexivity.
  - econstructor 2;[rewrite HRegs|apply HInRules| apply (SemAction_PSemAction HAction)| | | | | | | ]; eauto.
  - econstructor 3;[rewrite HRegs|apply HInMeths| apply (SemAction_PSemAction HAction)| | | | | | | ]; eauto.
Qed.

Lemma List_FullLabel_perm_nil l :
  List_FullLabel_perm nil l ->
  l = nil.
Proof.
  intros; remember (@nil FullLabel) as m in H.
  induction H; [eauto| | | eauto];discriminate.
Qed.  

Lemma List_FullLabel_perm_len l1 l2 :
  List_FullLabel_perm l1 l2 ->
  length l1 = length l2.
Proof.
  induction 1; simpl; eauto using eq_trans.
Qed.

Lemma List_FullLabel_perm_ind_bis :
  forall (P : list FullLabel -> list FullLabel -> Prop),
       P [] [] ->
       (forall (x x' : FullLabel) (l l' : list FullLabel),FullLabel_perm x x' -> List_FullLabel_perm l l' -> P l l' -> P (x :: l) (x' :: l')) ->
       (forall (x y x' y' : FullLabel) (l l' : list FullLabel), FullLabel_perm x x' -> FullLabel_perm y y' ->
                                                                List_FullLabel_perm l l' -> P l l' -> P (y :: x :: l) (x' :: y' :: l')) ->
       (forall l l' l'' : list FullLabel, List_FullLabel_perm l l' -> P l l' -> List_FullLabel_perm l' l'' -> P l' l'' -> P l l'')
       -> forall l l' : list FullLabel, List_FullLabel_perm l l' -> P l l'.
Proof.
  intros P Hnil Hskip Hswap Htrans.
  induction 1; auto.
  eapply Htrans with ls2; auto.
Qed.

Lemma List_FullLabel_perm_Add a b l l' : FullLabel_perm a b -> List.Add a l l' -> List_FullLabel_perm (b::l) l'.
Proof.
  induction 2; simpl.
  - econstructor 2; eauto using FullLabel_perm_sym, List_FullLabel_perm_refl.
  - eapply LFL_eq_trans with (x::b::l).
    + econstructor 3; eauto using FullLabel_perm_refl, List_FullLabel_perm_refl.
    + econstructor 2; eauto using FullLabel_perm_refl.
Qed.

Ltac FLInvAdd := repeat (match goal with
 | H: List.Add ?x _ (_ :: _) |- _ => inversion H; clear H; subst
                       end).

Lemma List_FullLabel_perm_Add_inv l1 l2:
  List_FullLabel_perm l1 l2 -> forall l1' l2' a b, FullLabel_perm a b -> List.Add a l1' l1 -> List.Add b l2' l2 ->
                                                                     List_FullLabel_perm l1' l2'.
Proof.
 revert l1 l2. refine (List_FullLabel_perm_ind_bis _ _ _ _ _).
 - (* nil *)
   inversion_clear 2.
 - (* skip *)
   intros x x' l1 l2 FL_E LFLE IH. intros. FLInvAdd; auto.
   + rewrite <- LFLE.
     eapply List_FullLabel_perm_Add; rewrite <- FL_E in H; eauto using FullLabel_perm_trans, FullLabel_perm_sym.
   + rewrite LFLE.
     symmetry; eapply List_FullLabel_perm_Add; rewrite H in FL_E; eauto using FullLabel_perm_trans, FullLabel_perm_sym.
   + econstructor 2; eauto.
 - (* swap *)
   intros x y x' y' l1 l2 FL_E1 FL_E2 PFLE IH. intros. FLInvAdd.
   + try econstructor; eauto using FullLabel_perm_trans, FullLabel_perm_sym.
   + try econstructor; eauto using FullLabel_perm_trans, FullLabel_perm_sym.
   + try econstructor; eauto using FullLabel_perm_trans, FullLabel_perm_sym.
     rewrite <- PFLE.
     eapply List_FullLabel_perm_Add; rewrite <- FL_E1 in H; eauto.
   + try econstructor; eauto using FullLabel_perm_trans, FullLabel_perm_sym.
   + try econstructor; eauto using FullLabel_perm_trans, FullLabel_perm_sym.
   + assert (y::x::l0 [=] x::y::l0);[constructor| rewrite H0].
     econstructor 2; eauto.
     rewrite <- PFLE.
     eapply List_FullLabel_perm_Add;[rewrite FL_E2;apply H|];eauto.
   + try econstructor; eauto using FullLabel_perm_trans, FullLabel_perm_sym.
     rewrite PFLE; symmetry; eapply List_FullLabel_perm_Add;[rewrite <-FL_E2; symmetry; apply H| assumption].
   + assert (x'::y'::l0 [=] y'::x'::l0);[constructor| rewrite H0].
     econstructor 2; eauto.
     symmetry; rewrite PFLE; eapply List_FullLabel_perm_Add;[symmetry; rewrite <- FL_E1; apply H| assumption].
   + econstructor 3; eauto.
 - (* trans *)
   intros l1 l l2 PE IH PE' IH' l1' l2' a b FL_E AD1 AD2.
   assert (In a l1). rewrite (List.Add_in AD1); left; reflexivity.
   specialize (List_FullLabel_perm_in PE _ H) as TMP; dest.
   destruct (Add_inv _ _ H1) as (l', AD).
   transitivity l'.
   + eapply IH;[apply H0| |];auto.
   + rewrite H0 in FL_E. eapply IH';[apply FL_E| |];auto.
Qed.

Lemma List_FullLabel_perm_cons_inv fl1 fl2 l1 l2:
  FullLabel_perm fl1 fl2 ->
    List_FullLabel_perm (fl1::l1) (fl2::l2) ->
    List_FullLabel_perm l1 l2.
Proof.
  intros; eapply List_FullLabel_perm_Add_inv; eauto using List.Add_head.
Qed.

Lemma List_FullLabel_perm_app l1 l2:
  List_FullLabel_perm l1 l2 ->
  forall l3 l4,
  List_FullLabel_perm l3 l4 ->
  List_FullLabel_perm (l1++l3) (l2++l4).
Proof.
  induction 1; intros.
  - repeat rewrite app_nil_r; assumption.
  - repeat rewrite <- Permutation_middle; econstructor 2; eauto.
  - repeat rewrite <- Permutation_middle; econstructor 3; eauto.
  - eapply List_FullLabel_perm_trans; eauto.
    apply IHList_FullLabel_perm2; reflexivity.
Qed.

Lemma PSubsteps_List_FullLabel_perm_rewrite m o l :
  PSubsteps m o l ->
  forall l',
  List_FullLabel_perm l l' ->
  PSubsteps m o l'.
Proof.
  induction 1.
  - intros; apply List_FullLabel_perm_nil in H; subst.
    econstructor 1; eauto.
  - intros; rewrite HLabel in *.
    specialize (List_FullLabel_perm_in H0 (u, (Rle rn, cs)) (in_eq _ _)) as TMP; dest.
      inversion H1; subst; apply (PSemAction_rewrite_newRegs H6) in HPAction;
        apply (PSemAction_rewrite_calls H9) in HPAction; rewrite H6 in HUpdGood.
      apply in_split in H2; dest.
      assert (l' [=] (u', (Rle rn, cs'))::(x++x0)); subst.
    + symmetry; apply Permutation_cons_app; reflexivity.
    + econstructor 2; eauto;rewrite H3 in H0; apply List_FullLabel_perm_cons_inv in H0; auto; intros.
      * specialize (List_FullLabel_perm_in (List_FullLabel_perm_sym H0) _ H2) as TMP; dest.
        specialize (HDisjRegs _ H5).
        intro; destruct (HDisjRegs k);[left|right];intro; apply H7; inv H4; simpl in *;[rewrite <- H10| rewrite H6]; assumption.
      * specialize (List_FullLabel_perm_in (List_FullLabel_perm_sym H0) _ H2) as TMP; dest.
        specialize (HNoRle _ H5).
        inv H4; simpl in *; assumption.
      * rewrite <- H9 in H2.
        unfold InCall in H4; dest.
        eapply HNoCall; eauto; unfold InCall.
        specialize (List_FullLabel_perm_in (List_FullLabel_perm_sym H0) _ H4) as TMP; dest.
        exists x2; split; auto.
        inv H7; simpl in *; rewrite <- H12; assumption.
  - intros; rewrite HLabel in *.
    specialize (List_FullLabel_perm_in H0 (u, (Meth (fn, existT SignT (projT1 fb) (argV, retV)), cs)) (in_eq _ _)) as TMP; dest.
      inversion H1; subst; apply (PSemAction_rewrite_newRegs H6) in HPAction;
        apply (PSemAction_rewrite_calls H9) in HPAction; rewrite H6 in HUpdGood.
      apply in_split in H2; dest.
      assert (l' [=] (u', (Meth (fn, existT SignT (projT1 fb) (argV, retV)), cs'))::(x++x0)); subst.
    + symmetry; apply Permutation_cons_app; reflexivity.
    + econstructor 3; eauto;rewrite H3 in H0; apply List_FullLabel_perm_cons_inv in H0; auto; intros.
      * specialize (List_FullLabel_perm_in (List_FullLabel_perm_sym H0) _ H2) as TMP; dest.
        specialize (HDisjRegs _ H5).
        intro; destruct (HDisjRegs k);[left|right];intro; apply H7; inv H4; simpl in *;[rewrite <- H10| rewrite H6]; assumption.
      * rewrite <- H9 in H2.
        unfold InCall in H4; dest.
        eapply HNoCall; eauto; unfold InCall.
        specialize (List_FullLabel_perm_in (List_FullLabel_perm_sym H0) _ H4) as TMP; dest.
        exists x2; split; auto.
        inv H7; simpl in *; rewrite <- H12; assumption.
      * apply HNoExec; rewrite H0; assumption.
Qed.

Global Instance PSubsteps_List_FullLabel_perm_rewrite' :
  Proper (Logic.eq ==> Logic.eq ==> List_FullLabel_perm ==> iff) (@PSubsteps) | 10.
repeat red; intros; split; intros; subst; eauto using List_FullLabel_perm_sym, PSubsteps_List_FullLabel_perm_rewrite.
Qed.

Lemma List_FullLabel_perm_InCall_rewrite f l l' :
  List_FullLabel_perm l l' ->
  InCall f l ->
  InCall f l'.
Proof.
  unfold InCall; induction 1; simpl; auto; intros; dest.
  - destruct H1; subst.
    + inv H.
      exists (u', (rm', cs')).
      split; auto; simpl in *.
      rewrite <- H4; assumption.
    + apply (List_FullLabel_perm_in H0) in H1; dest.
      exists x0.
      inv H1.
      split; auto; simpl in *; rewrite <- H6; assumption.
  - repeat destruct H2; subst; auto.
    + exists fl2; split; auto.
      inv H; simpl in *; rewrite <- H5; assumption.
    + exists fl4; split; auto.
      inv H0; simpl in *; rewrite <- H5; assumption.
    + assert (exists x, In x ls1 /\ In f (snd (snd x)));[exists x; split; auto|].
      specialize (IHList_FullLabel_perm H4) as TMP; dest.
      exists x0; split;auto.
Qed.

Lemma List_FullLabel_perm_WeakInclusion l l' :
  List_FullLabel_perm l l' ->
  WeakInclusion l l'.
Proof.
  unfold WeakInclusion.
  intros; repeat split; dest;
    eauto using List_FullLabel_perm_InExec_rewrite, List_FullLabel_perm_InCall_rewrite, List_FullLabel_perm_sym;[intro; destruct H0;[left|right]|intro; destruct H0;[left|right]|];
      try destruct H0; try split; eauto using List_FullLabel_perm_InExec_rewrite, List_FullLabel_perm_InCall_rewrite, List_FullLabel_perm_sym.
  intros; dest.
  exists x.
  induction H; eauto.
  - inv H; destruct H0.
    + rewrite <- H.
      left; reflexivity.
    + specialize (IHList_FullLabel_perm H); right; assumption.
  - repeat destruct H0.
    + inv H1.
      right; left; reflexivity.
    + inv H.
      left; reflexivity.
    + specialize (IHList_FullLabel_perm H0); right; right; assumption.
Qed.

Lemma MatchingExecCalls_List_FullLabel_perm_rewrite_1 m l l' l'':
  List_FullLabel_perm l' l'' ->
  MatchingExecCalls l l' m ->
  MatchingExecCalls l l'' m.
Proof.
  induction m;unfold MatchingExecCalls;simpl;intros;split;
    eauto; try intro; try eapply H0; eauto;
      try apply (List_FullLabel_perm_InExec_rewrite _ H);
      try eapply H0; eauto.
Qed.

Lemma MatchingExecCalls_List_FullLabel_perm_rewrite_2 m l l' l'':
  List_FullLabel_perm l' l'' ->
  MatchingExecCalls l' l m ->
  MatchingExecCalls l'' l m.
Proof.
  induction m;unfold MatchingExecCalls;simpl;intros;split;eauto; eapply H0;
    eauto using List_FullLabel_perm_InCall_rewrite, List_FullLabel_perm_sym.
Qed.

Global Instance MatchingExecCalls_List_FullLabel_perm_rewrite' :
  Proper (List_FullLabel_perm ==> List_FullLabel_perm ==> Logic.eq ==> iff) (@MatchingExecCalls) | 10.
Proof.
  repeat red; intros; split; intros; subst;
    eauto using  MatchingExecCalls_List_FullLabel_perm_rewrite_1,
    MatchingExecCalls_List_FullLabel_perm_rewrite_2,
    List_FullLabel_perm_sym.
Qed.
  
Lemma PStep_Step m o l:
  PStep m o l ->
  (exists o' l',
      o [=] o' /\
      getKindAttr o' = getKindAttr (getAllRegisters m) /\
      List_FullLabel_perm l l' /\
      Step m o' l').
Proof.
  induction 1.
  - apply PSubsteps_Substeps in HPSubsteps; dest.
    exists x, x0.
    repeat split; auto.
    econstructor 1; auto.
    rewrite <- H0; assumption.
  - dest.
    exists x, x0; repeat split; eauto.
    econstructor 2; auto.
    intros.
    apply (List_FullLabel_perm_InCall_rewrite H2).
    eapply HHidden; eauto.
    apply (List_FullLabel_perm_InExec_rewrite _ (List_FullLabel_perm_sym H2)); assumption.
  - dest.
    exists (x1++x), (x2++x0).
    repeat split.
    + rewrite HRegs, H5, H1; reflexivity.
    + simpl; repeat rewrite map_app; rewrite H2, H6; reflexivity.
    + rewrite HLabels.
      eapply List_FullLabel_perm_app; eauto.
    + econstructor 3; eauto.
      * rewrite <- H7; rewrite <- H3; assumption.
      * rewrite <- H7; rewrite <- H3; assumption.
      * intros.
        apply (List_FullLabel_perm_in (List_FullLabel_perm_sym H7)) in H9;
          apply (List_FullLabel_perm_in (List_FullLabel_perm_sym H3)) in H10; dest.
        specialize (HNoRle _ _ H12 H11).
        inv H9; inv H10; subst; simpl in *; assumption.
      * intros.
        eapply HNoCall.
        -- apply (List_FullLabel_perm_InCall_rewrite (List_FullLabel_perm_sym H7)) in H9;
             apply H9.
        -- apply (List_FullLabel_perm_InCall_rewrite (List_FullLabel_perm_sym H3));
           assumption.
Qed.

Lemma Step_PStep m o l:
  Step m o l ->
  PStep m o l.
Proof.
  induction 1; econstructor; subst;eauto.
  - apply Substeps_PSubsteps; assumption.
Qed.

Inductive List_FullLabel_perm_Lists : (list (list FullLabel)) -> (list (list FullLabel)) -> Prop :=
|PermutationEquiv_nil : List_FullLabel_perm_Lists nil nil
|PermutationEquiv_cons ls ls' l l' : List_FullLabel_perm_Lists ls ls'
                                     -> List_FullLabel_perm l l'
                                     -> List_FullLabel_perm_Lists (l::ls) (l'::ls').

Lemma List_FullLabel_perm_Lists_refl l :
  List_FullLabel_perm_Lists l l.
Proof.
  induction l; econstructor; eauto.
  reflexivity.
Qed.

Lemma List_FullLabel_perm_Lists_sym l l' :
  List_FullLabel_perm_Lists l l' -> List_FullLabel_perm_Lists l' l.
Proof.
  induction 1; econstructor; eauto using List_FullLabel_perm_sym.
Qed.

Lemma List_FullLabel_perm_Lists_trans l:
  forall l' l'',
    List_FullLabel_perm_Lists l l' ->
    List_FullLabel_perm_Lists l' l'' ->
    List_FullLabel_perm_Lists l l''.
Proof.
  induction l; eauto; intros; inv H; inv H0.
  - constructor.
  - constructor.
    + eapply IHl; eauto.
    + rewrite H5; assumption.
Qed.

Lemma List_FullLabel_perm_Lists_len l l' :
  List_FullLabel_perm_Lists l l' ->
  length l = length l'.
Proof.
  induction 1;[|simpl; rewrite IHList_FullLabel_perm_Lists]; reflexivity.
Qed.

Lemma List_FullLabel_perm_Lists_WeakInclusions l l' :
  List_FullLabel_perm_Lists l l' ->
  WeakInclusions l l'.
Proof.
  induction 1.
  - apply WeakInclusionsRefl.
  - econstructor; eauto.
    apply List_FullLabel_perm_WeakInclusion in H0; assumption.
Qed.

Lemma RegInit_generalized_list x:
  forall o' l,
  o' [=] x ->
  map fst l = map fst x ->
  (forall (o : string * {x : FullKind & fullType type x}) (r : string * {x : FullKind & option (ConstFullT x)}),
    In o o' ->
    In r l ->
    fst o = fst r ->
    exists pf : projT1 (snd o) = projT1 (snd r),
      match projT2 (snd r) with
      | Some x => match pf in (_ = Y) return (fullType type Y) with
                  | eq_refl => projT2 (snd o)
                  end = evalConstFullT x
      | None => True
      end) ->
  Forall2
    (fun (o'0 : string * {x : FullKind & fullType type x}) (r : string * {x0 : FullKind & option (ConstFullT x0)}) =>
       fst o'0 = fst r /\
       (exists pf : projT1 (snd o'0) = projT1 (snd r),
           match projT2 (snd r) with
           | Some x0 => match pf in (_ = Y) return (fullType type Y) with
                        | eq_refl => projT2 (snd o'0)
                        end = evalConstFullT x0
           | None => True
           end)) x l.
Proof.
  induction x; intros; inv H0.
  - apply map_eq_nil in H3; rewrite H3.
    constructor.
  - destruct l; inv H3.
    constructor.
    + split; [symmetry; assumption|].
      apply (H1 a p (Permutation_in _ (Permutation_sym H) (in_eq _ _)) (in_eq _ _) (eq_sym H2)).
    + eapply IHx; eauto.
      intros.
      eapply H1;[rewrite H | |]; try right; assumption.
Qed.

Lemma keys_establish_order (A B : Type):
  forall (l : list (A*B)),
    NoDup (map fst l) ->
    forall (l' : list (A*B)),
      l [=] l' ->
      (map fst l = map fst l') ->
      l = l'.
Proof.
  induction l; eauto; intros.
  - apply Permutation_nil in H0; rewrite H0; reflexivity.
  - destruct l';[ symmetry in H0; apply Permutation_nil in H0; inv H0|].
    simpl in *; inv H1; inv H.
    specialize (Permutation_in _ H0 (in_eq _ _)) as T; destruct T.
    + subst.
      apply Permutation_cons_inv in H0.
      rewrite (IHl H6 _ H0 H4); reflexivity.
    + apply False_ind.
      apply H5; rewrite H4.
      apply (in_map fst) in H; assumption.
Qed.

Lemma List_FullLabel_perm_fst l l':
  List_FullLabel_perm l l' ->
  forall a,
  In a (map fst l) ->
  (exists a',
      a [=] a' /\
      In a' (map fst l')).
Proof.
  induction 1; simpl; eauto; intros.
  - destruct H1; subst.
    + inv H; simpl in *.
      exists u'; split; eauto.
    + specialize (IHList_FullLabel_perm a H1); dest.
      exists x; split; eauto.
  - repeat destruct H2; subst.
    + inv H.
      exists u'; split; eauto.
    + inv H0.
      exists u'; split; eauto.
    + specialize (IHList_FullLabel_perm a H2); dest.
      exists x; split; eauto.
  - specialize (IHList_FullLabel_perm1 a H1); dest.
    specialize (IHList_FullLabel_perm2 x H3); dest.
    exists x0; split; eauto using Permutation_trans.
Qed.
    
Lemma Forall2_RegInit_keymatch x :
  forall l,
    Forall2
      (fun (o'0 : string * {x : FullKind & fullType type x}) (r : string * {x0 : FullKind & option (ConstFullT x0)}) =>
         fst o'0 = fst r /\
         (exists pf : projT1 (snd o'0) = projT1 (snd r),
             match projT2 (snd r) with
             | Some x0 => match pf in (_ = Y) return (fullType type Y) with
                          | eq_refl => projT2 (snd o'0)
                          end = evalConstFullT x0
             | None => True
             end)) x l ->
    map fst x = map fst l.
Proof.
  induction x; intros; inv H.
  - reflexivity.
  - simpl.
    destruct H2.
    rewrite H.
    rewrite (IHx _ H4); reflexivity.
Qed.

Lemma PTrace_Trace m o ls:
  WfMod m ->
  PTrace m o ls ->
  (exists o' ls',
      o' [=] o /\
      map fst o' = map fst (getAllRegisters m) /\
      List_FullLabel_perm_Lists ls ls' /\
      Trace m o' ls').
Proof.
  induction 2; subst.
  - exists o'', nil;
      repeat split; eauto using Permutation_sym; try econstructor; eauto.
    apply Forall2_RegInit_keymatch; assumption.
  - specialize (WfNoDups H) as TMP; dest.
    apply PStep_Step in HPStep; dest.
    unfold PUpdRegs in HPUpdRegs; dest.
    rewrite <- H4 in H12.
    specialize (getKindAttr_perm_eq _ _ _ _ (H12)) as TMP; dest.
    exists x3, (x2::x0).
    rewrite <- H5 in H1.
    rewrite <- H4 in H8.
    specialize (getKindAttr_map_fst _ _ H9); intros.
    rewrite <- H5 in H16.
    specialize (keys_establish_order H1 H8 (eq_sym H16)) as eq_x_x1.
    specialize (getKindAttr_map_fst _ _ H15); intros.
    setoid_rewrite <- H17 in H1.
    repeat split; eauto using Permutation_sym.
    + setoid_rewrite H17; setoid_rewrite H5; reflexivity.
    + econstructor; eauto.
    + econstructor 2; eauto.
      * rewrite eq_x_x1; assumption.
      * specialize (List_FullLabel_perm_fst H10).
        intros.
        split; eauto.
        intros.
        rewrite <- H14 in H19.
        specialize (H13 _ _ H19); dest.
        destruct H13;[left|right];dest.
        -- specialize (H18 _ H13); dest.
           exists x5; split; auto.
           rewrite <- H18; assumption.
        -- split;[|rewrite H4];auto.
           intro; dest.
           apply H13.
           specialize (List_FullLabel_perm_fst (List_FullLabel_perm_sym H10) _ H21) as TMP; dest.
           exists x5; split; eauto.
           rewrite <- H23; assumption.
Qed.

Lemma Trace_PTrace m o ls :
  Trace m o ls ->
  PTrace m o ls.
Proof.
  induction 1; subst.
  - econstructor; eauto.
  - econstructor 2; eauto.
    + apply Step_PStep in HStep.
      assumption.
    + unfold PUpdRegs; unfold UpdRegs in HUpdRegs; dest.
      split; eauto.
      rewrite H0; reflexivity.
Qed.

Definition PTraceList (m : Mod) (ls : list (list FullLabel)) :=
  (exists (o : RegsT), PTrace m o ls).

Definition PTraceInclusion (m m' : Mod) :=
  forall (o : RegsT)(ls : list (list FullLabel)), PTrace m o ls -> exists (ls' : list (list FullLabel)), PTraceList m' ls' /\ WeakInclusions ls ls'.

Lemma PTraceInclusion_TraceInclusion m1 m2 :
  WfMod m1 ->
  WfMod m2 ->
  PTraceInclusion m1 m2 -> TraceInclusion m1 m2.
Proof.
  intros.
  apply TraceInclusion'_TraceInclusion.
  repeat intro.
  apply Trace_PTrace in H2.
  specialize (H1 o ls H2); dest.
  unfold PTraceList in H1; dest.
  apply PTrace_Trace in H1; dest; eauto.
  exists x2; split.
  - exists x1; assumption.
  - specialize (List_FullLabel_perm_Lists_WeakInclusions H5) as trans.
    apply (WeakInclusionsTrans H3 trans).
Qed.

Section PSubsteps_rewrite.
  
  Lemma PSubsteps_rewrite_regs m o1 o2 l:
    (o1 [=] o2) ->
    PSubsteps m o1 l ->
    PSubsteps m o2 l.
  Proof.
    induction 2.
    - econstructor 1.
      rewrite <- H; assumption.
    - econstructor 2;[rewrite <- H|apply HInRules|apply (PSemAction_rewrite_state H) in HPAction; apply HPAction| | |apply HLabel| | | | ];assumption.
    - econstructor 3;[rewrite <- H|apply HInMeths|apply (PSemAction_rewrite_state H) in HPAction; apply HPAction| | |apply HLabel| | | | ];assumption.
  Qed.

  Lemma PSubsteps_rewrite_lists m o l1 l2:
    (l1 [=] l2) ->
    PSubsteps m o l1 ->
    PSubsteps m o l2.
  Proof.
    induction 2.
    - apply Permutation_nil in H; rewrite H.
      econstructor 1; assumption.
    - econstructor 2; eauto.
      rewrite H in HLabel.
      assumption.
    - econstructor 3; eauto.
      rewrite H in HLabel.
      assumption.
  Qed.

  Lemma PSubsteps_rewrite_both m o1 o2 l1 l2 :
    o1 [=] o2 ->
    l1 [=] l2 ->
    PSubsteps m o1 l1 ->
    PSubsteps m o2 l2.
  Proof.
    intros; apply (PSubsteps_rewrite_regs H) in H1; apply (PSubsteps_rewrite_lists H0) in H1; assumption.
  Qed.

  Inductive BaseModule_perm : BaseModule -> BaseModule -> Prop :=
  | perm_equiv m m' (HRegsPerm : getRegisters m [=] getRegisters m')
               (HMethsPerm : getMethods m [=] getMethods m')
               (HRulesPerm : getRules m [=] getRules m') :
      BaseModule_perm m m'.
  
  Lemma BaseModule_perm_refl m :
    BaseModule_perm m m.
  Proof.
    constructor; auto.
  Qed.

  Lemma BaseModule_perm_sym m m' :
    BaseModule_perm m m' -> BaseModule_perm m' m.
  Proof.
    intro; induction H; constructor; eauto using Permutation_sym.
  Qed.

  Lemma BaseModule_perm_trans m m' m'':
    BaseModule_perm m m' -> BaseModule_perm m' m'' -> BaseModule_perm m m''.
  Proof.
    intros.
    induction H, H0; constructor; eauto using Permutation_trans.
  Qed.

  Global Instance BaseModule_perm_Equivalence : Equivalence (@BaseModule_perm) | 10 := {
    Equivalence_Reflexive := @BaseModule_perm_refl;
    Equivalence_Symmetric := @BaseModule_perm_sym;
    Equivalence_Transitive:= @BaseModule_perm_trans}.

  Lemma PSubsteps_BaseModule_rewrite m m' o l :
    BaseModule_perm m m' -> PSubsteps m o l -> PSubsteps m' o l.
  Proof.
    intro; inv H; induction 1.
    - econstructor 1; rewrite <- HRegsPerm; assumption.
    - econstructor 2; try rewrite <- HRegsPerm; try rewrite <- HRulesPerm; eauto.
    - econstructor 3; try rewrite <- HRegsPerm; try rewrite <- HMethsPerm; eauto.
  Qed.

  Lemma PSubsteps_rewrite_all m m' o o' l l' :
    BaseModule_perm m m' -> o [=] o' -> l [=] l' -> PSubsteps m o l -> PSubsteps m' o' l'.
  Proof.
    intros.
    apply (PSubsteps_BaseModule_rewrite H) in H2.
    apply (PSubsteps_rewrite_both H0 H1) in H2.
    assumption.
  Qed.
    
  Global Instance PSubsteps_rewrite' :
    Proper (@BaseModule_perm ==>
        @Permutation (string * {x : FullKind & fullType type x}) ==>
                         @Permutation (FullLabel) ==> iff) (@PSubsteps)| 10.
  Proof.
    repeat red; intros; split; intros; eauto using Permutation_sym, BaseModule_perm_sym, PSubsteps_rewrite_all.
  Qed.
End PSubsteps_rewrite.
Section InExec_InCall_perm.
  Variable f : MethT.
  
  Lemma InCall_perm l l' :
    l [=] l' -> InCall f l  -> InCall f l'.
    induction 1; intros.
    - assumption.
    - apply (InCall_app_iff f (x::nil) l').
      apply (InCall_app_iff f (x::nil) l) in H0.
      destruct H0;[left|right; apply IHPermutation];assumption.
    - apply (InCall_app_iff f (x::y::nil) l).
      apply (InCall_app_iff f (y::x::nil) l) in H.
      destruct H;[left;apply (InCall_app_iff f (x::nil) (y::nil)) | right];
        [apply (InCall_app_iff f (y::nil) (x::nil)) in H; destruct H;[right|left]|];assumption.
    - apply (IHPermutation2 (IHPermutation1 H1)).
  Qed.

  Lemma InExec_perm l l' :
    l [=] l' -> InExec f l -> InExec f l'.
    induction 1; intros.
    - assumption.
    - apply (InExec_app_iff f (x::nil) l').
      apply (InExec_app_iff f (x::nil) l) in H0.
      destruct H0;[left|right; apply IHPermutation];assumption.
    - apply (InExec_app_iff f (x::y::nil) l).
      apply (InExec_app_iff f (y::x::nil) l) in H.
      destruct H;[left;apply (InExec_app_iff f (x::nil) (y::nil)) | right];
        [apply (InExec_app_iff f (y::nil) (x::nil)) in H; destruct H;[right|left]|];assumption.
    - apply (IHPermutation2 (IHPermutation1 H1)).
  Qed.

  Global Instance InCall_perm' :
    Proper (@Permutation (FullLabel) ==> iff) (@InCall f) | 10.
  Proof.
    repeat red; intros; specialize (Permutation_sym H) as TMP; eauto using InCall_perm.
  Qed.

  Global Instance InExec_perm' :
    Proper (@Permutation (FullLabel) ==> iff) (@InExec f) | 10.
  Proof.
    repeat red; intros; specialize (Permutation_sym H) as TMP; eauto using InExec_perm.
  Qed.
End InExec_InCall_perm.

Section PStep_rewrite.
  
  Lemma MatchingExecCalls_perm1 l1 l2 l3 m:
    l1 [=] l3 -> MatchingExecCalls l1 l2 m -> MatchingExecCalls l3 l2 m.
  Proof.
    repeat intro.
    specialize (H0 f).
    apply H0; auto.
    rewrite H; assumption.
  Qed.

  Lemma MatchingExecCalls_perm2 l1 l2 l3 m:
    l2 [=] l3 -> MatchingExecCalls l1 l2 m -> MatchingExecCalls l1 l3 m.
  Proof.
    repeat intro.
    specialize (H0 f).
    rewrite <- H.
    apply H0; auto.
  Qed.

  Lemma MatchingExecCalls_perm l1 l2 l3 l4 m:
    l1 [=] l3 ->
    l2 [=] l4 ->
    MatchingExecCalls l1 l2 m ->
    MatchingExecCalls l3 l4 m.
  Proof.
    intros; eauto using MatchingExecCalls_perm1, MatchingExecCalls_perm2.
  Qed.
    
  Global Instance MatchingExecCalls_perm' :
    Proper (@Permutation (FullLabel) ==>
                         @Permutation (FullLabel) ==>
                         Logic.eq ==>
                         iff) (@MatchingExecCalls) | 10.
  Proof.
    repeat red; split; intros; subst;
      specialize (Permutation_sym H) as TMP; specialize (Permutation_sym H0) as TMP1;
        eauto using MatchingExecCalls_perm.
  Qed.
  
  Lemma PStep_rewrite m o1 o2 l1 l2 :
    (o1 [=] o2) ->
    (l1 [=] l2) ->
    PStep m o1 l1 ->
    PStep m o2 l2.
  Proof.
    induction 3.
    - econstructor 1.
      apply (PSubsteps_rewrite_regs H).
      apply (PSubsteps_rewrite_lists H0).
      assumption.
      rewrite <- H0.
      assumption.
    - econstructor 2; eauto.
      intros.
      rewrite <- H0.
      eapply HHidden; eauto.
      rewrite H0; assumption.
    - econstructor 3; eauto.
      + rewrite <- H; assumption.
      + rewrite <- H0; assumption.
  Qed.

  Global Instance Step_perm_rewrite' :
    Proper (Logic.eq ==> @Permutation (string * {x : FullKind & fullType type x})
                     ==> @Permutation FullLabel
                     ==> iff) (@PStep) | 10.
  repeat red; split; intros; subst;
    specialize (Permutation_sym H0) as TMP; specialize (Permutation_sym H1) as TMP1;
      eauto using PStep_rewrite.
  Qed.
End PStep_rewrite.

Lemma PSemActionUpdSub o k a reads upds calls ret:
  @PSemAction o k a reads upds calls ret ->
  SubList (getKindAttr upds) (getKindAttr o).
Proof.
  induction 1; auto;
    unfold SubList in *; intros;
      rewrite ?in_app_iff in *.
  - rewrite HUNewRegs in *.
    rewrite map_app, in_app_iff in *.
    destruct H1; firstorder fail.
  - subst; rewrite HANewRegs in *;firstorder; simpl in *.
    subst.
    assumption.
  - rewrite HUNewRegs in *.
    rewrite map_app, in_app_iff in *.
    destruct H1; intuition.
  - rewrite HUNewRegs in *.
    rewrite map_app, in_app_iff in *.
    destruct H1; intuition.
  - subst; simpl in *; intuition.
Qed.

Lemma PSemActionExpandRegs o k a reads upds calls ret:
  @PSemAction o k a reads upds calls ret ->
  forall o', SubList reads o' ->
             SubList (getKindAttr upds) (getKindAttr o') ->
             @PSemAction o' k a reads upds calls ret.
Proof.
  intros.
  induction H; try solve [econstructor; auto].
  - subst.
    specialize (IHPSemAction H0).
    econstructor; eauto.
  - rewrite HUReadRegs in *; rewrite HUNewRegs in *.
    apply SubList_app_l in H0; dest.
    rewrite map_app in *.
    apply SubList_app_l in H1; dest.
    specialize (IHPSemAction1 H0 H1).
    specialize (IHPSemAction2 H3 H4).
    econstructor; eauto.
  - rewrite HNewReads in *.
    apply SubList_cons in H0; dest.
    specialize (IHPSemAction H2 H1).
    econstructor; eauto.
  - rewrite HANewRegs in *.
    simpl in *.
    apply SubList_cons in H1; dest.
    specialize (IHPSemAction H0 H2).
    econstructor; eauto.
  - rewrite HUReadRegs in *; rewrite HUNewRegs in *.
    apply SubList_app_l in H0; dest.
    rewrite map_app in *.
    apply SubList_app_l in H1; dest.
    specialize (IHPSemAction1 H0 H1).
    specialize (IHPSemAction2 H3 H4).
    econstructor; eauto.
  - rewrite HUReadRegs in *; rewrite HUNewRegs in *.
    apply SubList_app_l in H0; dest.
    rewrite map_app in *.
    apply SubList_app_l in H1; dest.
    specialize (IHPSemAction1 H0 H1).
    specialize (IHPSemAction2 H3 H4).
    econstructor 8; eauto.
Qed.

Lemma PSubsteps_upd_SubList_key m o l:
  PSubsteps m o l ->
  forall x s v, In x (map fst l) ->
                In (s, v) x ->
                In s (map fst (getRegisters m)).
Proof.
  induction 1; intros.
  - simpl in *; tauto.
  - subst; rewrite HLabel in H0.
    destruct H0; subst; simpl in *.
    + apply (in_map (fun x => (fst x, projT1 (snd x)))) in H1; simpl in *.
      specialize (HUpdGood _ H1).
      apply (in_map fst) in HUpdGood.
      rewrite map_map in HUpdGood.
      simpl in *.
      setoid_rewrite (functional_extensionality (fun x => fst x) fst) in HUpdGood; auto.
    + eapply IHPSubsteps; eauto.
  - subst; rewrite HLabel in H0.
    destruct H0; subst; simpl in *.
    + apply (in_map (fun x => (fst x, projT1 (snd x)))) in H1; simpl in *.
      specialize (HUpdGood _ H1).
      apply (in_map fst) in HUpdGood.
      rewrite map_map in HUpdGood.
      simpl in *.
      setoid_rewrite (functional_extensionality (fun x => fst x) fst) in HUpdGood; auto.
    + eapply IHPSubsteps; eauto.
Qed.

Lemma PSubsteps_upd_In m o l:
  PSubsteps m o l ->
  forall x, In x (map fst l) ->
            forall s: string, In s (map fst x) ->
                              In s (map fst (getRegisters m)).
Proof.
  intros.
  rewrite in_map_iff in H1; dest; subst.
  destruct x0; simpl.
  eapply PSubsteps_upd_SubList_key; eauto.
Qed.

Lemma PSubsteps_meth_In m o l :
  PSubsteps m o l ->
  forall u f cs, In (u, (Meth f, cs)) l ->
                 In (fst f) (map fst (getMethods m)).
Proof.
  intros.
  apply (PSubsteps_Substeps) in H; dest.
  specialize (List_FullLabel_perm_in H1 _ H0) as TMP; dest.
  inv H4.
  apply (Substeps_meth_In H3 _ _ _ H5).
Qed.

Lemma PSubsteps_combine m1 o1 l1:
  PSubsteps m1 o1 l1 ->
  forall m2 o2 l2  (DisjRegs: DisjKey (getRegisters m1) (getRegisters m2)) (DisjMeths: DisjKey (getMethods m1) (getMethods m2))
         (HOneRle: forall x1 x2, In x1 l1 -> In x2 l2 -> match fst (snd x1), fst (snd x2) with
                                                         | Rle _, Rle _ => False
                                                         | _, _ => True
                                                         end)
         (HNoCall: forall x, InCall x l1 -> InCall x l2 -> False),
    PSubsteps m2 o2 l2 ->
    PSubsteps (BaseMod (getRegisters m1 ++ getRegisters m2) (getRules m1 ++ getRules m2) (getMethods m1 ++ getMethods m2)) (o1 ++ o2) (l1 ++ l2).
Proof.
  induction 1; intros.
  - induction H; simpl in *.
    + constructor 1; auto; simpl.
      rewrite ?map_app; rewrite HRegs0; rewrite HRegs. reflexivity.
    + econstructor 2; eauto; simpl; rewrite ?map_app; try congruence.
      * rewrite HRegs; rewrite HRegs0; reflexivity.
      * rewrite in_app_iff; right; eassumption.
      * specialize (PSemAction_SemAction HPAction) as TMP; dest.
        pose proof (SemActionReadsSub (BaseMod (getRegisters m1 ++ getRegisters m2) (getRules m1 ++ getRules m2) (getMethods m1 ++ getMethods m2)) H3).
        pose proof (SemActionUpdSub H3).
        eapply PSemActionExpandRegs; eauto; unfold SubList in *; intros; rewrite ?map_app, ?in_app_iff; right.
        -- eapply H4; rewrite <- H0; eauto.
        -- eapply H5; rewrite <- H1; eauto.
      * unfold SubList in *; intros.
        rewrite in_app_iff; right; eapply HReadsGood; eauto.
      * unfold SubList in *; intros.
        rewrite in_app_iff; right; eapply HUpdGood; eauto.
      * eapply IHPSubsteps; intros;
          unfold InCall in *; simpl in *; dest; tauto.
    + econstructor 3; eauto; simpl; rewrite ?map_app; try congruence.
      * rewrite HRegs; rewrite HRegs0; reflexivity.
      * rewrite in_app_iff; right; eassumption.
      * specialize (PSemAction_SemAction HPAction) as TMP; dest.
        pose proof (SemActionReadsSub (BaseMod (getRegisters m1 ++ getRegisters m2) (getRules m1 ++ getRules m2) (getMethods m1 ++ getMethods m2)) H3).
        pose proof (SemActionUpdSub H3).
        eapply PSemActionExpandRegs; eauto; unfold SubList in *; intros; rewrite ?map_app, ?in_app_iff; right.
        -- eapply H4; rewrite <- H0; eauto.
        -- eapply H5; rewrite <- H1; eauto.
      * unfold SubList in *; intros.
        rewrite in_app_iff; right; eapply HReadsGood; eauto.
      * unfold SubList in *; intros.
        rewrite in_app_iff; right; eapply HUpdGood; eauto.
      * eapply IHPSubsteps; intros;
          unfold InCall in *; simpl in *; dest; tauto.
  - subst; simpl; rewrite HLabel.
    assert (sth_else: forall x1 x2, In x1 ls -> In x2 l2 -> match fst (snd x1), fst (snd x2) with
                                                            | Rle _, Rle _ => False
                                                            | _, _ => True
                                                            end);[intros x1 x2; specialize (HOneRle x1 x2); rewrite HLabel in *; clear - HOneRle; firstorder fail|].
    assert (sth2_else: forall x, InCall x ls -> InCall x l2 -> False);[intros x; specialize (HNoCall0 x); rewrite HLabel in *;clear - HNoCall0; firstorder fail|].
    specialize (IHPSubsteps _ _ _ DisjRegs DisjMeths sth_else sth2_else H0).
    simpl; econstructor 2; eauto; simpl; rewrite ?map_app; try congruence.
    + inv H0; rewrite HRegs; rewrite HRegs0; reflexivity.
    + rewrite in_app_iff; left; eassumption.
    + specialize (PSemAction_SemAction HPAction) as TMP;dest.
      pose proof (SemActionReadsSub (BaseMod (getRegisters m1 ++ getRegisters m2) (getRules m1 ++ getRules m2) (getMethods m1 ++ getMethods m2)) H4).
      pose proof (SemActionUpdSub H4).
      eapply PSemActionExpandRegs; eauto; unfold SubList in *; intros; rewrite ?map_app, ?in_app_iff; left.
      * eapply H5; rewrite <- H1; eauto.
      * eapply H6; rewrite <- H2; eauto.
    + unfold SubList in *; intros.
      rewrite in_app_iff; left; eapply HReadsGood; eauto.
    + unfold SubList in *; intros.
      rewrite in_app_iff; left; eapply HUpdGood; eauto.
    + intros.
      rewrite in_app_iff in *.
      destruct H1; [eapply HDisjRegs; eauto| ].
      rewrite DisjKeyWeak_same by apply string_dec; intro; intros.
      rewrite in_map_iff in H2; dest; subst.   
      pose proof (PSubsteps_upd_In H0 _ (in_map fst _ _ H1) _ (in_map fst _ _ H4)).
      apply (SubList_map fst) in HUpdGood.
      rewrite ?map_map in *; simpl in *.
      rewrite ?(functional_extensionality (fun x => fst x) fst) in HUpdGood by tauto.
      setoid_rewrite (functional_extensionality (fun x => fst x) fst) in HUpdGood; [|tauto].
      specialize (HUpdGood _ H3).
      clear - H2 DisjRegs HUpdGood; firstorder fail.
    + intros.
      rewrite in_app_iff in *.
      destruct H1; [eapply HNoRle; eauto| ].
      unfold SubList in *.
      specialize (HOneRle (u, (Rle rn, cs)) x); rewrite HLabel in HOneRle.
      specialize (HOneRle (or_introl eq_refl) H1); simpl in *; assumption.
    + intros.
      rewrite InCall_app_iff in *.
      destruct H2; [eapply HNoCall; eauto|].
      eapply HNoCall0; eauto.
      rewrite HLabel.
      unfold InCall.
      eexists; split; simpl; eauto.
  - subst; simpl.
    assert (sth_else: forall x1 x2, In x1 ls -> In x2 l2 -> match fst (snd x1), fst (snd x2) with
                                                            | Rle _, Rle _ => False
                                                            | _, _ => True
                                                            end);[intros;specialize (HOneRle x1 x2);rewrite HLabel in * ; firstorder fail|].
    assert (sth2_else: forall x, InCall x ls -> InCall x l2 -> False);[intros; specialize (HNoCall0 x); rewrite HLabel in *; firstorder fail|].
    specialize (IHPSubsteps _ _ _ DisjRegs DisjMeths sth_else sth2_else H0).
    rewrite HLabel;simpl; econstructor 3; eauto; simpl; rewrite ?map_app; try congruence.
    + inv H0;rewrite HRegs; rewrite HRegs0; reflexivity.
    + rewrite in_app_iff; left; eassumption.
    + specialize (PSemAction_SemAction HPAction) as TMP; dest.
      pose proof (SemActionReadsSub (BaseMod (getRegisters m1 ++ getRegisters m2) (getRules m1 ++ getRules m2) (getMethods m1 ++ getMethods m2)) H4).
      pose proof (SemActionUpdSub H4).
      eapply PSemActionExpandRegs; eauto; unfold SubList in *; intros; rewrite ?map_app, ?in_app_iff; left.
      * eapply H5; rewrite <- H1; eauto.
      * eapply H6; rewrite <- H2; eauto.
    + unfold SubList in *; intros.
      rewrite in_app_iff; left; eapply HReadsGood; eauto.
    + unfold SubList in *; intros.
      rewrite in_app_iff; left; eapply HUpdGood; eauto.
    + intros.
      rewrite in_app_iff in *.
      destruct H1; [eapply HDisjRegs; eauto| ].
      rewrite DisjKeyWeak_same by apply string_dec; intro; intros.
      rewrite in_map_iff in H2; dest; subst.
      pose proof (PSubsteps_upd_In H0 _ (in_map fst _ _ H1) _ (in_map fst _ _ H4)).
      apply (SubList_map fst) in HUpdGood.
      rewrite ?map_map in *; simpl in *.
      rewrite ?(functional_extensionality (fun x => fst x) fst) in HUpdGood by tauto.
      setoid_rewrite (functional_extensionality (fun x => fst x) fst) in HUpdGood; [|tauto].
      specialize (HUpdGood _ H3).
      clear - H2 DisjRegs HUpdGood; firstorder fail.
    + intros.
      rewrite InCall_app_iff in *.
      destruct H2; [eapply HNoCall; eauto|].
      eapply HNoCall0; eauto.
      unfold InCall.
      eexists; rewrite HLabel;split; simpl; eauto.
    + rewrite InExec_app_iff; intros; destruct H1; auto.
      unfold InExec in H1; rewrite in_map_iff in H1; dest.
      destruct x, p; simpl in *; subst.
      eapply PSubsteps_meth_In in H2; eauto.
      destruct (DisjMeths fn);auto.
      apply (in_map fst) in HInMeths; contradiction.
Qed.

Corollary PStep_meth_InExec m o l :
  PStep m o l ->
  forall f : MethT,
    InExec f l -> In (fst f) (map fst (getAllMethods m)).
Proof.
  intros.
  apply PStep_Step in H; dest.
  eapply (Step_meth_InExec H3 f).
  apply (List_FullLabel_perm_InExec_rewrite f H2); assumption.
Qed.

Lemma PStep_substitute' m o l:
  PStep m o l -> forall (HWfMod: WfMod m), PStepSubstitute m o l.
Proof.
  unfold StepSubstitute.
  induction 1; auto; simpl; intros; dest; unfold MatchingExecCalls in *; simpl in *.
  - repeat split.
    clear HMatching.
    induction HPSubsteps.
    + econstructor 1; eauto.
    + econstructor 2; eauto.
    + econstructor 3; eauto.
    + simpl; tauto.
    + specialize (HMatching f); tauto.
    + simpl in *; tauto.
  - inv HWfMod.
    specialize (IHPStep HWf); unfold PStepSubstitute in IHPStep; dest.
    repeat split; auto.
    + specialize (H1 f); tauto.
    + intros.
      destruct H4; simpl in *; subst.
      -- apply HHidden; auto.
      -- apply H2; auto.
  - inv HWfMod.
    specialize (IHPStep1 HWf1).
    specialize (IHPStep2 HWf2).
    unfold PStepSubstitute in *; dest.
    subst; repeat split; auto.
    + pose proof (PSubsteps_combine H4  HDisjRegs HDisjMeths HNoRle HNoCall H1 (m2 := BaseMod (getAllRegisters m2) _ _)).
      simpl in *.
      rewrite HLabels; rewrite HRegs.
      assumption.
    + rewrite HLabels in *.
      unfold MatchingExecCalls in *; simpl in *.
      rewrite ?InExec_app_iff, ?InCall_app_iff, ?map_app, ?in_app_iff in *.
      repeat match goal with
             | H: forall x: MethT, _ |- _ => specialize (H f)
             end; tauto.
    + intros.
      rewrite HLabels in *.
      unfold MatchingExecCalls in *; simpl in *.
      rewrite ?InExec_app_iff, ?InCall_app_iff, ?map_app, ?in_app_iff in *.
      repeat match goal with
             | H: forall x: string, _ |- _ => specialize (H s)
             | H: forall x: MethT, _ |- _ => specialize (H (s, v))
             end.
      specialize (H6 v); specialize (H3 v).
      destruct H7, H8, H9; try tauto.
      * pose proof (PStep_meth_InExec H0 _ H9); simpl in *.
        clear - HDisjMeths H7 H10; firstorder fail.
      * pose proof (WfMod_Hidden HWf2 s H8).
        clear - HDisjMeths H7 H10; firstorder fail.
      * pose proof (WfMod_Hidden HWf2 s H8).
        clear - HDisjMeths H7 H10; firstorder fail.
      * pose proof (WfMod_Hidden HWf1 s H8).
        clear - HDisjMeths H7 H10; firstorder fail.
      * pose proof (WfMod_Hidden HWf1 s H8).
        clear - HDisjMeths H7 H10; firstorder fail.
      * pose proof (PStep_meth_InExec H _ H9); simpl in *.
        clear - HDisjMeths H7 H10; firstorder fail.
Qed.

Lemma PStepSubstitute_flatten m o l (HWfMod: WfMod m):
  PStep (flatten m) o l <-> PStepSubstitute m o l.
Proof.
  unfold flatten, getFlat, PStepSubstitute.
  split; intros.
  - induction (getHidden m).
    + simpl in *.
      inv H.
      split; [auto| split; [auto| intros; tauto]].
    + simpl in *.
      inv H.
      specialize (IHl0 HPStep); dest.
      split; [auto| split; [auto| intros]].
      rewrite createHide_Meths in *; simpl in *.
      destruct H3; [subst |clear - H1 H2 H3 H4; firstorder fail].
      firstorder fail.
  - induction (getHidden m); simpl; auto; dest.
    + constructor; auto.
    + assert (sth: PStep (createHide (BaseMod (getAllRegisters m) (getAllRules m) (getAllMethods m)) l0) o l) by firstorder fail.
      assert (sth2: forall v, In a (map fst (getAllMethods m)) -> InExec (a, v) l -> InCall (a, v) l) by firstorder fail.
      constructor; auto.
      rewrite createHide_Meths.
      auto.
Qed.

Lemma PStep_substitute m o l (HWfMod: WfMod m):
  PStep m o l -> PStep (flatten m) o l.
Proof.
  intros Stp.
  apply PStep_substitute' in Stp; auto.
  rewrite PStepSubstitute_flatten in *; auto.
Qed.

Lemma splitRegs o m1 m2 (DisjRegisters: DisjKey (getRegisters m1) (getRegisters m2)):
  getKindAttr o [=] getKindAttr (getRegisters m1 ++ getRegisters m2) ->
  getKindAttr (filter (fun x : string * {x : FullKind & fullType type x} => getBool (in_dec string_dec (fst x) (map fst (getRegisters m1)))) o) [=] getKindAttr (getRegisters m1).
Proof.
  intros HRegs.
  rewrite map_app in *.
  pose proof (filter_map_simple (fun x: string * {x: FullKind & fullType type x} => (fst x, projT1 (snd x)))
                                (fun x => getBool (in_dec string_dec (fst x) (map fst (getRegisters m1)))) o) as sth.
  simpl in sth.
  setoid_rewrite <- sth.
  setoid_rewrite HRegs.
  rewrite filter_app.
  setoid_rewrite filter_false_list at 2.
  - rewrite filter_true_list at 1.
    + rewrite app_nil_r; auto.
    + intros.
      apply (in_map fst) in H.
      rewrite map_map in H.
      simpl in *.
      setoid_rewrite (functional_extensionality (fun x => fst x) fst) in H; try tauto.
      destruct (in_dec string_dec (fst a) (map fst (getRegisters m1))); auto.
  - intros.
    apply (in_map fst) in H.
    rewrite map_map in H.
    simpl in *.
    setoid_rewrite (functional_extensionality (fun x => fst x) fst) in H; try tauto.
    destruct (in_dec string_dec (fst a) (map fst (getRegisters m1))); auto.
    specialize (DisjRegisters (fst a)).
    tauto.
Qed.

Global Instance BaseModuleFilter_rewrite' :
  Proper (Logic.eq ==> @Permutation (FullLabel) ==> @Permutation (FullLabel)) (@ModuleFilterLabels) | 10.
Proof.
  unfold ModuleFilterLabels; repeat red; intros; rewrite H, H0; reflexivity.
Qed.

Lemma WfActionT_ReadsWellDefined_perm : forall (k : Kind)(a : ActionT type k)(retl : type k)
                                          (m1 : BaseModule)(o readRegs newRegs : RegsT)(calls : MethsT),
    WfActionT m1 a ->
    PSemAction o a readRegs newRegs calls retl ->
    SubList (getKindAttr readRegs) (getKindAttr (getRegisters m1)).
Proof.
  intros.
  apply (PSemAction_SemAction) in H0; dest.
  rewrite H0.
  eapply (WfActionT_ReadsWellDefined H H3); eauto.
Qed.

Lemma WfActionT_WritesWellDefined_perm : forall (k : Kind)(a : ActionT type k)(retl : type k)
                                           (m1 : BaseModule)(o readRegs newRegs : RegsT)(calls : MethsT),
    WfActionT m1 a ->
    PSemAction o a readRegs newRegs calls retl ->
    SubList (getKindAttr newRegs) (getKindAttr (getRegisters m1)).
Proof.
  intros.
  apply (PSemAction_SemAction) in H0; dest.
  rewrite H1.
  eapply (WfActionT_WritesWellDefined); eauto.
Qed.

Lemma WfActionT_PSemAction : forall (k : Kind)(a : ActionT type k)(retl : type k)
                                   (m1 : BaseModule)(o readRegs newRegs : RegsT)(calls : MethsT),
    WfActionT m1 a ->
    NoDup (map fst o) ->
    PSemAction o a readRegs newRegs calls retl ->
    (forall (o1 : RegsT),
        SubList o1 o ->
        getKindAttr o1 [=] getKindAttr (getRegisters m1) ->
        PSemAction o1 a readRegs newRegs calls retl).
  induction 3; intro; subst; inversion H; EqDep_subst.
  - intros TMP1 TMP2; specialize (IHPSemAction (H4 mret) o1 TMP1 TMP2).
    econstructor 1; eauto.
  - intros TMP1 TMP2; specialize (IHPSemAction (H4) o1 TMP1 TMP2).
    econstructor 2; eauto.
  - intros TMP1 TMP2; specialize (IHPSemAction1 (H4) o1 TMP1 TMP2); specialize (IHPSemAction2 (H6 v) o1 TMP1 TMP2).
    econstructor 3; eauto.
  - intros TMP1 TMP2; specialize (IHPSemAction (H4 valueV) o1 TMP1 TMP2).
    econstructor 4; eauto.
  - intros TMP1 TMP2; specialize (IHPSemAction (H5 regV) o1 TMP1 TMP2).
    econstructor 5; eauto.
    apply (KeyRefinement (r, existT (fullType type) regT regV) H0 TMP1 HRegVal).
    rewrite <- TMP2 in H7; apply (in_map fst) in H7; specialize (GKA_fst (A:=string)(fullType type) o1); intro.
    simpl in *.
    setoid_rewrite H2; assumption.
  - intros TMP1 TMP2; specialize (IHPSemAction H5 o1 TMP1 TMP2).
    econstructor 6; eauto.
    rewrite TMP2; assumption.
  - intros TMP1 TMP2; specialize (IHPSemAction1 H8 o1 TMP1 TMP2); specialize (IHPSemAction2 (H5 r1) o1 TMP1 TMP2).
    econstructor 7; eauto.
  - intros TMP1 TMP2; specialize (IHPSemAction1 H9 o1 TMP1 TMP2); specialize (IHPSemAction2 (H5 r1) o1 TMP1 TMP2).
    econstructor 8; eauto.
  - intros TMP1 TMP2; specialize (IHPSemAction H4 o1 TMP1 TMP2).
    econstructor 9; eauto.
  - intros TMP1 TMP2; specialize (IHPSemAction H4 o1 TMP1 TMP2).
    econstructor 10; eauto.
  - intros; econstructor 11; eauto.
Qed.

Lemma papp_sublist_l : forall {A : Type} (l1 l2 l : list A),
    l [=] l1++l2 -> SubList l1 l.
Proof.
  repeat intro.
  rewrite H.
  apply (in_app_iff l1 l2 x); left; assumption.
Qed.

Lemma papp_sublist_r : forall {A : Type} (l1 l2 l : list A),
    l [=] l1++l2 -> SubList l2 l.
Proof.
  repeat intro.
  rewrite H.
  apply (in_app_iff l1 l2 x); right; assumption.
Qed.

Section SplitSubsteps.
  Variable m1 m2: BaseModule.
  Variable DisjRegs: DisjKey (getRegisters m1) (getRegisters m2).
  Variable DisjRules: DisjKey (getRules m1) (getRules m2).
  Variable DisjMeths: DisjKey (getMethods m1) (getMethods m2).

  Variable WfMod1: WfBaseMod m1.
  Variable WfMod2: WfBaseMod m2.
  
  Lemma pfilter_perm o l :
    PSubsteps (concatFlat m1 m2) o l ->
    l [=] ((ModuleFilterLabels m1 l)++(ModuleFilterLabels m2 l)).
  Proof.   
    induction 1; subst.
    - simpl; apply Permutation_refl.
    - unfold ModuleFilterLabels; setoid_rewrite HLabel; fold (ModuleFilterLabels m1 ((u, (Rle rn, cs))::ls));
      fold (ModuleFilterLabels m2 ((u, (Rle rn, cs))::ls)). apply in_app_iff in HInRules.
      destruct HInRules as [HInRules | HInRules]; rewrite (InRules_Filter _ _ _ _ _ _ HInRules).
      + destruct (DisjRules rn).
        * generalize (in_map_iff fst (getRules m1) rn). intro TMP; destruct TMP as [L R];clear L.
          assert (exists x, fst x = rn /\ In x (getRules m1));[exists (rn, rb); auto| specialize (R H1); contradiction].
        * rewrite (NotInRules_Filter _ _ _ _ _ H0).
          constructor. assumption.
      + destruct (DisjRules rn).
        * rewrite (NotInRules_Filter _ _ _ _ _ H0).
          apply (Permutation_cons_app _ _ _ IHPSubsteps).
        * generalize (in_map_iff fst (getRules m2) rn). intro TMP; destruct TMP as [L R];clear L.
          assert (exists x, fst x = rn /\ In x (getRules m2));[exists (rn, rb); auto | specialize (R H1); contradiction].
    - apply in_app_iff in HInMeths.
      unfold ModuleFilterLabels; rewrite HLabel; fold (ModuleFilterLabels m1 ( (u, (Meth (fn, existT SignT (projT1 fb) (argV, retV)), cs))::ls));
        fold (ModuleFilterLabels m2 ((u, (Meth (fn, existT SignT (projT1 fb) (argV, retV)), cs))::ls));
      destruct HInMeths as [HInMeths | HInMeths]; rewrite (InMethods_Filter _ _ _ _ _ _ _ _ HInMeths).
      + destruct (DisjMeths fn).
        * generalize (in_map_iff fst (getMethods m1) fn). intro TMP; destruct TMP as [L R]; clear L.
          assert (exists x, fst x = fn /\ In x (getMethods m1)); [exists (fn, fb); auto| specialize (R H1); contradiction].
        * rewrite (NotInMethods_Filter _ _ _ _ _ _ _ _ H0).
          constructor. assumption.
      + destruct (DisjMeths fn).
        * rewrite (NotInMethods_Filter _ _ _ _ _ _ _ _ H0).
          apply (Permutation_cons_app _ _ _ IHPSubsteps).
        * generalize (in_map_iff fst (getMethods m2) fn). intro TMP; destruct TMP as [L R]; clear L.
          assert (exists x, fst x = fn /\ In x (getMethods m2)); [exists (fn, fb); auto| specialize (R H1); contradiction].
  Qed.

  Lemma split_f A B (f : A -> B) :
    forall (ls : list A) (l1 l2 : list B),
      map f ls [=] l1 ++ l2 ->
      (exists (ls1 ls2 : list A),
          (ls [=] ls1++ls2) /\
          (map f ls1 [=] l1) /\
          (map f ls2 [=] l2)).
  Proof.
    induction ls; intros.
    - exists nil, nil.
      apply (Permutation_nil) in H; destruct (app_eq_nil _ _ H).
      repeat split.
      + reflexivity.
      + rewrite H0; reflexivity.
      + rewrite H1; reflexivity.
    - assert (In (f a) (map f (a::ls)));[left; reflexivity|].
      rewrite H in H0.
      destruct (in_app_or _ _ _ H0).
      + specialize (in_split _ _ H1) as TMP; dest.
        rewrite H2 in H; simpl in H.
        rewrite <- app_assoc in H.
        specialize (Permutation_cons_app_inv (l:=(map f ls)) x (x0++l2) H) as TMP.
        rewrite app_assoc in TMP.
        specialize (IHls (x ++ x0) (l2) TMP) as TMP2; dest.
        exists (a::x1), x2.
        repeat split.
        * simpl; constructor; auto.
        * simpl; rewrite H2.
          apply Permutation_cons_app.
          assumption.
        * assumption.
      + specialize (in_split _ _ H1) as TMP; dest.
        rewrite H2 in H; simpl in H.
        rewrite app_assoc in H.
        specialize (Permutation_cons_app_inv (l:=(map f ls)) (l1++x) x0 H) as TMP.
        rewrite <- app_assoc in TMP.
        specialize (IHls (l1) (x++x0) TMP) as TMP2; dest.
        exists (x1), (a::x2).
        repeat split.
        * apply Permutation_cons_app; assumption.
        * assumption.
        * simpl; rewrite H2.
          apply Permutation_cons_app.
          assumption.
  Qed.
  
  Lemma split_PSubsteps1 o l:
    NoDup (map fst (getRegisters m1)) ->
    NoDup (map fst (getRegisters m2)) ->
    PSubsteps (concatFlat m1 m2) o l ->
    (exists o1 o2, getKindAttr o1 [=] getKindAttr (getRegisters m1) /\
                   getKindAttr o2 [=] getKindAttr (getRegisters m2) /\
                   o [=] o1++o2 /\
                   PSubsteps m1 o1 (ModuleFilterLabels m1 l) /\
                   PSubsteps m2 o2 (ModuleFilterLabels m2 l)).
  Proof.
    unfold concatFlat; induction 3; simpl in *.
    - rewrite map_app in *; apply split_f in HRegs; dest.
      exists x, x0;split;[|split;[|split;[|split;[constructor|constructor]]]];assumption.
    - rewrite map_app in *;apply in_app_iff in HInRules; specialize (DisjRules rn).
      assert (NoDup (map fst o));[setoid_rewrite GKA_fst;setoid_rewrite HRegs; rewrite <- map_app; rewrite <- GKA_fst; apply (NoDupKey_Expand H H0 DisjRegs)|].
      destruct HInRules as [HInRules|HInRules];generalize (in_map fst _ _ HInRules);destruct DisjRules;try contradiction.
      + subst; dest; exists x, x0;split;[|split;[|split;[|split]]];auto.
        rewrite HLabel in *.
        rewrite (InRules_Filter _ _ _ _ _ _ HInRules).
        destruct WfMod1 as [WfMod_Rle1 WfMod_Meth1];destruct WfMod2 as [WfMod_Rle2 WfMod_Meth2];
          specialize (WfActionT_ReadsWellDefined_perm (WfMod_Rle1 _ HInRules) HPAction) as Reads_sublist; specialize (WfActionT_WritesWellDefined_perm (WfMod_Rle1 _ HInRules) HPAction) as Writes_sublist.
        constructor 2 with (rn:= rn)(rb:=rb)(reads:=reads)(u:=u)(cs:=cs)(ls:=(ModuleFilterLabels m1 ls)); auto.
        * specialize (papp_sublist_l _ _ H6) as SL_o_x.
          specialize (WfMod_Rle1 (rn, rb) HInRules); specialize (WfActionT_PSemAction WfMod_Rle1 H2 HPAction SL_o_x H4).
          simpl; auto.
        * unfold ModuleFilterLabels;intros;apply HDisjRegs;
            destruct (filter_In (BaseModuleFilter m1) x1 ls) as [L R];
            destruct (L H10);assumption.
        * intros; apply HNoRle;
            destruct (filter_In (BaseModuleFilter m1) x1 ls) as [L R];
            destruct (L H10);assumption.
        * intros; apply (HNoCall c H10). destruct H11 as [x1 [L R]];exists x1;split;[|assumption].
          destruct (filter_In (BaseModuleFilter m1) x1 ls) as [L1 R1]; destruct (L1 L); assumption.
        * rewrite HLabel,(NotInRules_Filter _ _ _ _ _ H3); assumption.
      + subst; dest; exists x, x0; split;[|split;[|split;[|split]]];auto.
        rewrite HLabel,(NotInRules_Filter _ _ _ _ _ H3); assumption.
        rewrite HLabel,(InRules_Filter _ _ _ _ _ _ HInRules).
        destruct WfMod1 as [WfMod_Rle1 WfMod_Meth1];destruct WfMod2 as [WfMod_Rle2 WfMod_Meth2];
          specialize (WfActionT_ReadsWellDefined_perm (WfMod_Rle2 _ HInRules) HPAction) as Reads_sublist; specialize (WfActionT_WritesWellDefined_perm (WfMod_Rle2 _ HInRules) HPAction) as Writes_sublist.
        constructor 2 with (rn:= rn)(rb:=rb)(reads:=reads)(u:=u)(cs:=cs)(ls:=(ModuleFilterLabels m2 ls)); auto.
        * specialize (papp_sublist_r _ _ H6) as SL_o_x.
          specialize (WfMod_Rle2 (rn, rb) HInRules); specialize (WfActionT_PSemAction WfMod_Rle2 H2 HPAction SL_o_x H5).
          simpl; auto.
        * unfold ModuleFilterLabels;intros;apply HDisjRegs;
            destruct (filter_In (BaseModuleFilter m2) x1 ls) as [L R];
            destruct (L H10);assumption.
        * intros; apply HNoRle;
            destruct (filter_In (BaseModuleFilter m2) x1 ls) as [L R];
            destruct (L H10);assumption.
        * intros; apply (HNoCall c H10). destruct H11 as [x1 [L R]];exists x1;split;[|assumption].
          destruct (filter_In (BaseModuleFilter m2) x1 ls) as [L1 R1]; destruct (L1 L); assumption.
    - rewrite map_app in *;apply in_app_iff in HInMeths; specialize (DisjMeths fn).
      assert (NoDup (map fst o));[setoid_rewrite GKA_fst;setoid_rewrite HRegs; rewrite <- map_app; rewrite <- GKA_fst; apply (NoDupKey_Expand H H0 DisjRegs)|].
      destruct HInMeths as [HInMeths|HInMeths];generalize (in_map fst _ _ HInMeths);destruct DisjMeths;try contradiction;intros.
      + subst; dest; exists x, x0;split;[|split;[|split;[|split]]];auto.
        * rewrite HLabel,(InMethods_Filter _ _ _ _ _ _ _ _ HInMeths).
          destruct WfMod1 as [WfMod_Rle1 WfMod_Meth1];destruct WfMod2 as [WfMod_Rle2 WfMod_Meth2]; specialize (WfActionT_ReadsWellDefined_perm (WfMod_Meth1 (fn, fb) HInMeths argV) HPAction) as Reads_sublist; specialize (WfActionT_WritesWellDefined_perm (WfMod_Meth1 (fn, fb) HInMeths argV) HPAction) as Writes_sublist.
          constructor 3 with (fn:=fn)(fb:=fb)(reads:=reads)(u:=u)(cs:=cs)(argV:=argV)(retV:=retV)(ls:=(ModuleFilterLabels m1 ls)); auto.
          -- specialize (papp_sublist_l _ _ H7) as SL_o_x.
             specialize (WfMod_Meth1 (fn, fb) HInMeths argV); specialize (WfActionT_PSemAction WfMod_Meth1 H2 HPAction SL_o_x H5).
             simpl; auto.
          -- intros; apply HDisjRegs;
               destruct (filter_In (BaseModuleFilter m1) x1 ls) as [L R];
               destruct (L H10); assumption.
          -- intros; apply (HNoCall c H10). destruct H11 as [x1 [L R]];exists x1;split;[|assumption].
             destruct (filter_In (BaseModuleFilter m1) x1 ls) as [L1 R1]; destruct (L1 L); assumption.
          -- intros; apply HNoExec; unfold InExec in *.
             rewrite in_map_iff in H10; dest; destruct x1, p; simpl in *; subst.
             unfold ModuleFilterLabels in H11; rewrite filter_In in H11; dest.
             apply (in_map getRleOrMeth) in H10; assumption.
        * rewrite HLabel,(NotInMethods_Filter _ _ _ _ _ _ _ _ H3); assumption.
      + subst; dest; exists x, x0;split;[|split;[|split;[|split]]]; auto.
        * rewrite HLabel,(NotInMethods_Filter _ _ _ _ _ _ _ _ H3); assumption.
        * rewrite HLabel,(InMethods_Filter _ _ _ _ _ _ _ _ HInMeths).
          destruct WfMod1 as [WfMod_Rle1 WfMod_Meth1];destruct WfMod2 as [WfMod_Rle2 WfMod_Meth2];
            specialize (WfActionT_ReadsWellDefined_perm (WfMod_Meth2 (fn, fb) HInMeths argV) HPAction) as Reads_sublist;
            specialize (WfActionT_WritesWellDefined_perm (WfMod_Meth2 (fn, fb) HInMeths argV) HPAction) as Writes_sublist.
          constructor 3 with (fn:=fn)(fb:=fb)(reads:=reads)(u:=u)(cs:=cs)(argV:=argV)(retV:=retV)(ls:=(ModuleFilterLabels m2 ls)); auto.
          -- specialize (papp_sublist_r _ _ H7) as SL_o_x.
             specialize (WfMod_Meth2 (fn, fb) HInMeths argV); specialize (WfActionT_PSemAction WfMod_Meth2 H2 HPAction SL_o_x H6).
             simpl; auto.
          -- intros; apply HDisjRegs;
               destruct (filter_In (BaseModuleFilter m2) x1 ls) as [L R];
               destruct (L H10); assumption.
          -- intros; apply (HNoCall c H10). destruct H11 as [x1 [L R]];exists x1;split;[|assumption].
             destruct (filter_In (BaseModuleFilter m2) x1 ls) as [L1 R1]; destruct (L1 L); assumption.
          -- intros; apply HNoExec; unfold InExec in *.
             rewrite in_map_iff in H10; dest; destruct x1, p; simpl in *; subst.
             unfold ModuleFilterLabels in H11; rewrite filter_In in H11; dest.
             apply (in_map getRleOrMeth) in H10; assumption.
  Qed.
  
  Lemma split_Substeps2 o l:
    PSubsteps (concatFlat m1 m2) o l ->
      (forall x y : FullLabel,
          In x (ModuleFilterLabels m1 l) ->
          In y (ModuleFilterLabels m2 l) ->
          match fst (snd x) with
          | Rle _ => match fst (snd y) with
                     | Rle _ => False
                     | Meth _ => True
                     end
          | Meth _ => True
          end) /\
      (forall x : MethT, InCall x (ModuleFilterLabels m1 l) -> InCall x (ModuleFilterLabels m2 l)
                         -> False).
  Proof.
    induction 1; intros; split; auto; subst.
    - intros; contradiction.
    - unfold InCall; intros; dest; contradiction.
    - simpl in HInRules.
      destruct (in_app_or _ _ _ HInRules) as [Rle_in | Rle_in]; specialize (in_map fst _ _ Rle_in) as map_Rle_in; destruct (DisjRules rn); try contradiction;
        intros x y; rewrite HLabel,(InRules_Filter u _ _ ls cs _ Rle_in);rewrite (NotInRules_Filter u _ ls cs _ H0); intros.
        * destruct H1.
          -- rewrite <- H1; simpl.
             apply HNoRle.
             unfold ModuleFilterLabels in H2; apply filter_In in H2; destruct H2; assumption.
          -- eapply IHPSubsteps; eauto.
        * destruct H2.
          -- rewrite <- H2; simpl.
             apply HNoRle.
             unfold ModuleFilterLabels in H1; apply filter_In in H1; destruct H1; assumption.
          -- eapply IHPSubsteps; eauto.
    - destruct (in_app_or _ _ _ HInRules) as [Rle_in | Rle_in]; specialize (in_map fst _ _ Rle_in) as map_Rle_in; destruct (DisjRules rn); try contradiction;
        intros x; rewrite HLabel,(InRules_Filter u _ _ ls cs _ Rle_in);rewrite (NotInRules_Filter u _ ls cs _ H0); intros.
      + destruct (InCall_app_iff x (((u, (Rle rn, cs)))::nil) (ModuleFilterLabels m1 ls)) as [L R]; clear R.
        destruct (L H1); clear L.
        * unfold InCall in H3. dest.
          destruct H3;[subst|contradiction].
          apply InCall_split_InCall in H2.
          apply (HNoCall x); auto.
        * eapply IHPSubsteps; eauto.
      + destruct (InCall_app_iff x (((u, (Rle rn, cs)))::nil) (ModuleFilterLabels m2 ls)) as [L R]; clear R.
        destruct (L H2); clear L.
        * unfold InCall in H3. dest.
          destruct H3;[subst|contradiction].
          apply InCall_split_InCall in H1.
          apply (HNoCall x); auto.
        * eapply IHPSubsteps; eauto.
    - intros.
      unfold ModuleFilterLabels in *.
      rewrite HLabel in *.
      specialize (filter_app (BaseModuleFilter m1) ((u, (Meth (fn, existT SignT (projT1 fb) (argV, retV)), cs))::nil) ls) as TMP; setoid_rewrite TMP in H0; clear TMP.
      specialize (filter_app (BaseModuleFilter m2) ((u, (Meth (fn, existT SignT (projT1 fb) (argV, retV)), cs))::nil) ls) as TMP; setoid_rewrite TMP in H1; clear TMP.
      destruct (in_app_or _ _ _ H0); destruct (in_app_or _ _ _ H1).
      + apply filter_In in H3; apply filter_In in H2. dest.
        destruct H2, H3; try contradiction.
        subst; simpl; auto.
      + apply filter_In in H2; destruct H2.
        destruct H2;[|contradiction].
        subst; simpl; auto.
      + apply filter_In in H3; destruct H3.
        destruct H3;[|contradiction].
        subst; simpl; auto.
        destruct (fst (snd x)); auto.
      + eapply IHPSubsteps; eauto.
    - intros.
      destruct (DisjMeths fn).
      + rewrite HLabel in *; setoid_rewrite (NotInMethods_Filter u _ fb argV retV ls cs _ H2) in H0.
        unfold ModuleFilterLabels in *.
        specialize (filter_app (BaseModuleFilter m2) ((u, (Meth (fn, existT SignT (projT1 fb) (argV, retV)), cs))::nil) ls) as TMP; setoid_rewrite TMP in H1; clear TMP.
        destruct (InCall_app_iff x (filter (BaseModuleFilter m2) [(u, (Meth (fn, existT SignT (projT1 fb) (argV, retV)), cs))]) (filter (BaseModuleFilter m2) ls)) as [L R]; clear R; destruct (L H1); clear L.
        * unfold InCall in H3; dest; apply filter_In in H3; destruct H3.
          destruct H3;[subst|contradiction].
          simpl in H6.
          apply InCall_split_InCall in H0.
          eapply HNoCall; eauto.
        * eapply IHPSubsteps; eauto.
      + rewrite HLabel in *; setoid_rewrite (NotInMethods_Filter u _ fb argV retV ls cs _ H2) in H1.
        unfold ModuleFilterLabels in *.
        specialize (filter_app (BaseModuleFilter m1) ((u, (Meth (fn, existT SignT (projT1 fb) (argV, retV)), cs))::nil) ls) as TMP; setoid_rewrite TMP in H0; clear TMP.
        destruct (InCall_app_iff x (filter (BaseModuleFilter m1) [(u, (Meth (fn, existT SignT (projT1 fb) (argV, retV)), cs))]) (filter (BaseModuleFilter m1) ls)) as [L R]; clear R; destruct (L H0); clear L.
        * unfold InCall in H3; dest; apply filter_In in H3; destruct H3.
          destruct H3;[subst|contradiction].
          simpl in H6.
          apply InCall_split_InCall in H1.
          eapply HNoCall; eauto.
        * eapply IHPSubsteps; eauto.
  Qed.

End SplitSubsteps.

Lemma PSubsteps_flatten m o l:
  PSubsteps (BaseMod (getRegisters m) (getRules m) (getMethods m)) o l ->
  PSubsteps m o l.
Proof.
  induction 1; simpl; auto.
  - constructor 1; auto.
  - econstructor 2; eauto.
  - econstructor 3; eauto.
Qed.

Lemma flatten_PSubsteps m o l:
  PSubsteps m o l ->
  PSubsteps (BaseMod (getRegisters m) (getRules m) (getMethods m)) o l.
  induction 1; simpl; auto.
  - constructor 1; auto.
  - econstructor 2; eauto.
  - econstructor 3; eauto.
Qed.

Lemma PWfConcats m1 m2 o l:
  WfConcat m2 m1 -> PSubsteps (getFlat m2) o l ->
  forall s v,
    In s (getHidden m1) -> ~InCall (s, v) l.
Proof.
  intros.
  specialize (PSubsteps_Substeps H0) as TMP; dest.
  specialize (WfConcats H H5 H1 (v:=v)).
  repeat intro.
  apply H6.
  apply (List_FullLabel_perm_InCall_rewrite H3); assumption.
Qed.

Lemma substitute_PStep' m (HWfMod: WfMod m):
  forall o l,
    PStepSubstitute m o l ->
    PStep m o l.
Proof.
  unfold PStepSubstitute.
  induction m; simpl in *; intros; dest.
  - constructor 1; auto; eapply PSubsteps_flatten; eauto.
  - constructor; auto.
    inv HWfMod;eapply IHm; eauto.
  - inv HWfMod.
    specialize (IHm1 HWf1).
    specialize (IHm2 HWf2).
    destruct (WfNoDups HWf1) as [ND_Regs1 [ND_Meths1 ND_Rules1]].
    destruct (WfNoDups HWf2) as [ND_Regs2 [ND_Meths2 ND_Rules2]].
    specialize (WfMod_WfBaseMod_flat HWf1) as WfBaseMod1.
    specialize (WfMod_WfBaseMod_flat HWf2) as WfBaseMod2.
    pose proof (@split_PSubsteps1 (getFlat m1) (getFlat m2) HDisjRegs HDisjRules HDisjMeths WfBaseMod1 WfBaseMod2 _ _  ND_Regs1 ND_Regs2 H);dest.
    rewrite H4 in *.
    assert (DisjKey (getRules (getFlat m1)) (getRules (getFlat m2)));[repeat intro; apply HDisjRules|].
    assert (DisjKey (getMethods (getFlat m1))(getMethods (getFlat m2)));[repeat intro;apply HDisjMeths|].
    specialize (pfilter_perm H7 H8 H) as P1.
    rewrite P1. rewrite P1 in H.
    econstructor 3.
    + eapply IHm1; eauto.
      Opaque MatchingExecCalls.
      repeat split; eauto.
      * unfold getFlat in H0; simpl in *.
        assert (MatchingExecCalls l l (Base (concatFlat (getFlat m1) (getFlat m2))));[unfold concatFlat, getFlat;simpl; assumption|].
        eapply MatchingExecCalls_Split; eauto.
      * intros; specialize (H1 s v).
        intros; specialize (PWfConcats WfConcat2 H6 H10 (v:=v));intro.
        rewrite map_app in H1.
        specialize (H1 (in_or_app _ _ s (or_introl H9)) (in_or_app _ _ s (or_introl H10)) (InExec_split_InExec _ _ _ H11)).
        assert (DisjKey (getRules (getFlat m1)) (getRules (getFlat m2)));[repeat intro; apply HDisjRules|].
        assert (DisjKey (getMethods (getFlat m1))(getMethods (getFlat m2)));[repeat intro;apply HDisjMeths|].
        rewrite P1 in H1; apply InCall_app_iff in H1; destruct H1;[assumption|contradiction].
    + eapply IHm2; eauto.
      repeat split; eauto.
      * unfold getFlat in H0; simpl in *.
        assert (MatchingExecCalls l l (Base (concatFlat (getFlat m1) (getFlat m2))));[unfold concatFlat, getFlat;simpl; assumption|].
        apply MatchingExecCalls_Concat_comm in H9.
        eapply MatchingExecCalls_Split; eauto.
      * intros; specialize (H1 s v).
        intros; specialize (PWfConcats WfConcat1 H5 H10 (v:=v));intro.
        rewrite map_app in H1.
        specialize (H1 (in_or_app _ _ s (or_intror H9)) (in_or_app _ _ s (or_intror H10)) (InExec_split_InExec _ _ _ H11)).
        assert (DisjKey (getRules (getFlat m1)) (getRules (getFlat m2)));[repeat intro; apply HDisjRules|].
        assert (DisjKey (getMethods (getFlat m1))(getMethods (getFlat m2)));[repeat intro;apply HDisjMeths|].
        rewrite P1 in H1; apply InCall_app_iff in H1; destruct H1;[contradiction|assumption].
    + assert (MatchingExecCalls l l (Base (concatFlat (getFlat m1) (getFlat m2)))); auto.
      specialize (MatchingExecCalls_Mix H9); intros.
      Transparent MatchingExecCalls.
      repeat intro.
      destruct (H10 f H11 H12).
      split; auto.
      intro; apply (PWfConcats WfConcat1 H5 H15 (v:=(snd f))); destruct f ;assumption.
    + assert (MatchingExecCalls l l (Base (concatFlat (getFlat m1) (getFlat m2)))); auto.
      specialize (MatchingExecCalls_Mix (MatchingExecCalls_Concat_comm H9)); intros.
      repeat intro.
      destruct (H10 f H11 H12).
      split; auto.
      intro; apply (PWfConcats WfConcat2 H6 H15 (v:=(snd f))); destruct f ;assumption.
    + intros.
      eapply split_Substeps2; eauto; rewrite <- P1; assumption.
    + eapply split_Substeps2; eauto; rewrite P1; apply H.
    + reflexivity.
    + reflexivity.
Qed.


Lemma substitute_PStep m o l (HWfMod: WfMod m):
  PStep (flatten m) o l ->
  PStep m o l.
Proof.
  rewrite PStepSubstitute_flatten in *; auto.
  apply substitute_PStep'; auto.
Qed.

Section PTraceSubstitute.
  Variable m: Mod.
  Variable WfMod_m: WfMod m.

  Lemma PTrace_flatten_same1: forall o l,  PTrace m o l -> PTrace (flatten m) o l.
  Proof.
    induction 1; subst.
    - (constructor 1 with (o'':= o'')); unfold flatten; auto.
      rewrite createHide_Regs.
      auto.
    - apply PStep_substitute in HPStep; auto.
      econstructor 2; eauto.
  Qed.

  Lemma PTrace_flatten_same2: forall o l, PTrace (flatten m) o l -> PTrace m o l.
  Proof.
    induction 1; subst.
    - rewrite getAllRegisters_flatten in *;constructor 1 with (o'' := o''); auto.
    - apply substitute_PStep in HPStep;auto; dest.
      + econstructor 2; eauto.
  Qed.

  Lemma PTraceInclusion_flatten_r: PTraceInclusion m (flatten m).
  Proof.
    unfold PTraceInclusion; intros.
    exists ls.
    split;[|apply WeakInclusionsRefl].
    unfold PTraceList.
    exists o.
    apply PTrace_flatten_same1; assumption.
  Qed.

  Corollary TraceInclusion_flatten_r' : TraceInclusion m (flatten m).
  Proof.
    apply PTraceInclusion_TraceInclusion; eauto using flatten_WfMod.
    apply PTraceInclusion_flatten_r.
  Qed.
  
  Lemma PTraceInclusion_flatten_l: PTraceInclusion (flatten m) m.
  Proof.
    unfold PTraceInclusion; intros.
    apply PTrace_flatten_same2 in H.
    exists ls.
    split.
    - unfold PTraceList; exists o; auto.
    - apply WeakInclusionsRefl.
  Qed.

  Corollary TraceInclusion_flatten_l' : TraceInclusion (flatten m) m.
  Proof.
    apply PTraceInclusion_TraceInclusion; eauto using flatten_WfMod.
    apply PTraceInclusion_flatten_l.
  Qed.
  
End PTraceSubstitute.


Record WfModule : Type := mkWfMod {module :> Mod; Wf_cond : WfMod module}.

Section WfModule_rewrite.

  Inductive WfModule_perm : WfModule ->WfModule -> Prop :=
  |Wf_perm_equiv (m m': WfModule) (HAllRegsPerm : getAllRegisters m [=] getAllRegisters m')
              (HAllMethsPerm : getAllMethods m [=] getAllMethods m')
              (HAllRulesPerm : getAllRules m [=] getAllRules m')
              (HHiddenPerm : getHidden m [=] getHidden m') :
     WfModule_perm m m'.

  Lemma WfModule_perm_refl m :
    WfModule_perm m m.
  Proof.
    constructor; auto.
  Qed.

  Lemma WfModule_perm_sym m m':
    WfModule_perm m m' -> WfModule_perm m' m.
  Proof.
    constructor; inv H; eauto using Permutation_sym.
  Qed.

  Lemma WfModule_perm_trans m m' m'' :
    WfModule_perm m m' -> WfModule_perm m' m'' -> WfModule_perm m m''.
  Proof.
    constructor; inv H; inv H0; eauto using Permutation_trans.
  Qed.

  Global Instance WfModule_perm_Equivalence : Equivalence (@WfModule_perm) | 10 := {
     Equivalence_Reflexive := @WfModule_perm_refl;
     Equivalence_Symmetric := @WfModule_perm_sym;             
     Equivalence_Transitive:= @WfModule_perm_trans}.

  
  Lemma PStep_rewrite_base m1' m2' o l hl:
    BaseModule_perm m1' m2' ->
    PStep (createHide m1' hl) o l->
    PStep (createHide m2' hl) o l.
  Proof.
    induction hl; simpl.
    - intros.
      inv H0; econstructor 1.
      + rewrite <- H; assumption.
      + repeat intro.
        apply (HMatching f H0); simpl in *.
        inversion H; subst.
        rewrite HMethsPerm; assumption.
    - intros.
      inv H0; econstructor 2; auto; intros.
      eapply HHidden; auto.
      rewrite createHide_Meths in *.
      inversion H; subst.
      rewrite HMethsPerm; assumption.
  Qed.

Lemma PStep_rewrite_hides m o l:
  forall hl' hl,
    hl [=] hl' ->
    PStep (createHide m hl) o l->
    PStep (createHide m hl') o l.
Proof.
  induction 1; auto; intros.
  - simpl in *; inv H0; econstructor 2;  auto.
    intros.
    rewrite createHide_Meths in *.
    eapply HHidden; eauto.
  - simpl in *.
    inv H; inv HPStep.
    econstructor 2;[econstructor 2|]; auto.
Qed.
  
  Lemma PStep_WfModule_rewrite m1 m2 o l :
    WfModule_perm m1 m2 ->
    PStep m1 o l ->
    PStep m2 o l.
  Proof.
    intros.
    apply (substitute_PStep); eauto using (Wf_cond m2).
    apply (PStep_substitute) in H0; eauto using (Wf_cond m1).
    unfold flatten in *.
    assert (BaseModule_perm (getFlat m1) (getFlat m2));[inv H;unfold getFlat;constructor;auto|].
    apply (PStep_rewrite_base (getHidden m1) H1) in H0.
    inv H.
    apply (PStep_rewrite_hides _ HHiddenPerm H0).
  Qed.

  Lemma Forall2_perm (A B : Type) (* (l1 : list A) *)
        (l2 l3 : list B)(P : A -> B -> Prop):
    l2 [=] l3 ->
    forall l1,
    Forall2 P l1 l2 ->
    (exists l4,
        l1 [=] l4 /\
        Forall2 P l4 l3).
    induction 1.
    - intros; inv H.
      exists nil; split; eauto.
    - intros.
      destruct l1; inv H0.
      specialize (IHPermutation _ H6);dest.
      exists (a::x0).
      split; auto.
    - intros.
      destruct l1; inv H.
      destruct l1; inv H5.
      exists (a0::a::l1); split; auto.
      econstructor 3.
    - intros.
      specialize (IHPermutation1 _ H1);dest.
      specialize (IHPermutation2 _ H3);dest.
      exists x0; split; eauto using Permutation_trans.
  Qed.
  
  Lemma PTrace_WfModule_rewrite m1 m2 o ls:
    WfModule_perm m1 m2 ->
    PTrace m1 o ls ->
    PTrace m2 o ls.
  Proof.
    induction 2; subst; inv H.
    - specialize (Forall2_perm  HAllRegsPerm HUpdRegs) as TMP; dest.
      econstructor 1 with (o'':=x);eauto.
      rewrite <- H; assumption.
    - econstructor 2; eauto.
      eapply (PStep_WfModule_rewrite) in HPStep; eauto.
      econstructor; eauto.
  Qed.

  Lemma PTrace_RegsT_rewrite m o1 o2 ls :
    o1 [=] o2 ->
    PTrace m o1 ls ->
    PTrace m o2 ls.
  Proof.
    intros; inv H0.
    - econstructor 1 with (o'':=o''); eauto using Permutation_sym, Permutation_trans.
    - econstructor 2; eauto.
      unfold PUpdRegs in *; dest.
      repeat split; auto.
      + rewrite <- H; assumption.
      + intros.
        rewrite <- H in H2.
        specialize (H1 s v H2).
        assumption.
  Qed.

  Lemma PTrace_rewrite m1 m2 o1 o2 ls:
    o1 [=] o2 ->
    WfModule_perm m1 m2 ->
    PTrace m1 o1 ls ->
    PTrace m2 o2 ls.
  Proof.
    intros; eauto using PTrace_WfModule_rewrite, PTrace_RegsT_rewrite.
  Qed.

  Global Instance PStep_WfModule_rewrite' :
    Proper (@WfModule_perm ==> Logic.eq ==> Logic.eq ==> iff) (@PStep) |10.
  Proof.
    repeat red; split; intros; subst; eauto using WfModule_perm_sym,PStep_WfModule_rewrite.
  Qed.

  Global Instance Trace_rewrite' :
    Proper (@WfModule_perm ==> @Permutation (string * {x : FullKind & fullType type x}) ==> Logic.eq ==> iff) (@PTrace) | 10.
  Proof.
    repeat red; split; intros; subst; eauto using WfModule_perm_sym, Permutation_sym, PTrace_rewrite.
  Qed.
End WfModule_rewrite.

Lemma WfNilMod :
  WfMod (Base (BaseMod nil nil nil)).
Proof.
  constructor; simpl; constructor; intros; contradiction.
Qed.

Lemma WfConcatActionTNil (k : Kind) (a : ActionT type k):
  WfConcatActionT a (Base (BaseMod nil nil nil)).
Proof.
  induction a; econstructor; eauto.
Qed.

Lemma WfConcatNil m :
  WfMod m ->
  WfMod (ConcatMod m (Base (BaseMod nil nil nil))).
Proof.
  constructor; unfold DisjKey; simpl; intros; auto.
  - apply WfNilMod.
  - split; intros; eauto using WfConcatActionTNil.
  - split; intros; contradiction.
Qed.

Lemma WfNilConcat m :
  WfMod (ConcatMod m (Base (BaseMod nil nil nil))) ->
  WfMod m.
Proof.
  intros; inv H; assumption.
Qed.

Lemma WfConcatComm m1 m2 :
  WfMod (ConcatMod m1 m2) ->
  WfMod (ConcatMod m2 m1).
Proof.
  intros; inv H.
  econstructor; eauto using DisjKey_Commutative.
Qed.

Lemma DeM1 (A : Type):
  forall (l1 l2 : list A) (a : A),
    ~(In a l1 \/ In a l2) <-> ~In a l1 /\ ~In a l2.
Proof.
  split;intros.
  - split; intro; apply H; auto.
  - destruct H.
    intro; destruct H1; auto.
Qed.

Lemma WfConcatSplits m1 m2 (k : Kind) (a : ActionT type k):
    WfConcatActionT a (ConcatMod m1 m2) ->
    WfConcatActionT a m1 /\
    WfConcatActionT a m2.
Proof.
  induction a.
  - intros; split; econstructor 1; eauto; inv H0; EqDep_subst; intro; try eapply H; eauto;
      apply H8; simpl; rewrite in_app_iff; eauto.
  - intros; split; econstructor 2; eauto; inv H0; EqDep_subst; destruct (H (evalExpr e) H6); auto.
  - intros; split; econstructor 3; eauto; inv H0; EqDep_subst; try intro; try eapply IHa; eauto;
    eapply H; eauto.
  - intros; split; econstructor 4; eauto; inv H0; EqDep_subst; intros; eapply H; eauto.
  - intros; split; econstructor 5; eauto; inv H0; EqDep_subst; intros; eapply H; eauto.
  - intros; split; econstructor 6; eauto; inv H; EqDep_subst; eapply IHa; eauto.
  - intros; split; econstructor 7; eauto; inv H0; EqDep_subst; try intros; try eapply H; eauto;
      try eapply IHa1; eauto; eapply IHa2; eauto.
  - intros; split; econstructor 8; eauto; inv H; EqDep_subst; eapply IHa; eauto.
  - intros; split; econstructor 9; eauto; inv H; EqDep_subst; eapply IHa; eauto.
  - intros; split; econstructor 10.
Qed.

Lemma WfConcatMerge m1 m2 (k : Kind) (a : ActionT type k) :
  WfConcatActionT a m1 ->
  WfConcatActionT a m2 ->
  WfConcatActionT a (ConcatMod m1 m2).
Proof.
  induction a; intros.
  - econstructor 1; inv H0; inv H1; EqDep_subst; intros; try eapply H; eauto; simpl; rewrite in_app_iff; intro;
      destruct H0;auto.
  - econstructor 2; inv H0; inv H1; EqDep_subst; eapply H; eauto.
  - econstructor 3; inv H0; inv H1; EqDep_subst; try eapply H; eauto.
  - econstructor 4; inv H0; inv H1; EqDep_subst; intros; eapply H; eauto.
  - econstructor 5; inv H0; inv H1; EqDep_subst; intros; eapply H; eauto.
  - econstructor 6; inv H; inv H0; EqDep_subst; eapply IHa; eauto.
  - econstructor 7; inv H0; inv H1; EqDep_subst; intros; try eapply H, IHa1, IHa2; eauto.
  - econstructor 8; inv H; inv H0; EqDep_subst; eapply IHa; eauto.
  - econstructor 9; inv H; inv H0; EqDep_subst; eapply IHa; eauto.
  - econstructor 10.
Qed.
    

Lemma WfConcatAssoc1 m1 m2 m3 :
  WfMod (ConcatMod m1 (ConcatMod m2 m3)) ->
  WfMod (ConcatMod (ConcatMod m1 m2) m3).
Proof.
  intros; inv H; inv HWf2; inv WfConcat1; inv WfConcat2.
  econstructor; simpl in *; eauto.
  - intro.
    destruct (HDisjRegs k), (HDisjRegs0 k); simpl in *; rewrite map_app in *; rewrite in_app_iff in *; rewrite DeM1 in *; auto.
    destruct H3; right; assumption.
  - intro.
    destruct (HDisjRules k), (HDisjRules0 k); simpl in *; rewrite map_app in *; rewrite in_app_iff in *; rewrite DeM1 in *; auto.
    destruct H3; right; assumption.
  - intro.
    destruct (HDisjMeths k), (HDisjMeths0 k); simpl in *; rewrite map_app in *; rewrite in_app_iff in *; rewrite DeM1 in *; auto.
    destruct H3; right; assumption.
  - econstructor; eauto; simpl in *.
    + intro.
      destruct (HDisjRegs k), (HDisjRegs0 k); simpl in *; auto; rewrite map_app in *; rewrite in_app_iff in *; rewrite DeM1 in *; auto.
      destruct H3; right; assumption.
    + intro.
      destruct (HDisjRules k), (HDisjRules0 k); simpl in *; auto; rewrite map_app in *; rewrite in_app_iff in *; rewrite DeM1 in *.
      destruct H3; right; assumption.
    + intro.
      destruct (HDisjMeths k), (HDisjMeths0 k); simpl in *; auto; rewrite map_app in *; rewrite in_app_iff in *; rewrite DeM1 in *.
      destruct H3; right; assumption.
    + econstructor; intros.
      * specialize (H _ H3).
        apply (WfConcatSplits H).
      * specialize (H0 _ H3 v).
        apply (WfConcatSplits H0).
    + econstructor; intros.
      * apply (H1 rule (in_or_app _ _ _ (or_introl _ H3))).
      * apply (H2 meth (in_or_app _ _ _ (or_introl _ H3)) v).
  - split; intros; simpl in *; rewrite in_app_iff in *; destruct H3.
    + specialize (H _ H3); apply (WfConcatSplits H).
    + inv WfConcat0; eauto.
    + specialize (H0 _ H3 v); apply (WfConcatSplits H0).
    + inv WfConcat0; eauto.
  - split; intros; simpl in *;inv WfConcat3.
    + eapply WfConcatMerge; eauto.
      apply (H1 rule (in_or_app _ _ _ (or_intror _ H3))).
    + eapply WfConcatMerge; eauto.
      apply (H2 meth (in_or_app _ _ _ (or_intror _ H3)) v).
Qed.


Lemma WfConcatAssoc2 m1 m2 m3 :
  WfMod (ConcatMod (ConcatMod m1 m2) m3) ->
  WfMod (ConcatMod m1 (ConcatMod m2 m3)).
Proof.
  intros.
  inv H; inv HWf1; inv WfConcat1; inv WfConcat2.
  econstructor; try intro; simpl in *; eauto.
  - destruct (HDisjRegs k), (HDisjRegs0 k); simpl in *; rewrite map_app in *; rewrite in_app_iff in *; rewrite DeM1 in *; auto.
    destruct H3; left; assumption.
  - destruct (HDisjRules k), (HDisjRules0 k); simpl in *; rewrite map_app in *; rewrite in_app_iff in *; rewrite DeM1 in *; auto.
    destruct H3; left; assumption.
  - destruct (HDisjMeths k), (HDisjMeths0 k); simpl in *; rewrite map_app in *; rewrite in_app_iff in *; rewrite DeM1 in *; auto.
    destruct H3; left; assumption.
  - econstructor; try intro; simpl in *; eauto.
    + destruct (HDisjRegs k), (HDisjRegs0 k); simpl in *; auto; rewrite map_app in *; rewrite in_app_iff in *; rewrite DeM1 in *.
      destruct H3; left; assumption.
    + destruct (HDisjRules k), (HDisjRules0 k); simpl in *; auto; rewrite map_app in *; rewrite in_app_iff in *; rewrite DeM1 in *.
      destruct H3; left; assumption.
    + destruct (HDisjMeths k), (HDisjMeths0 k); simpl in *; auto; rewrite map_app in *; rewrite in_app_iff in *; rewrite DeM1 in *.
      destruct H3; left; assumption.
    + split; intros.
      * apply (H rule (in_or_app _ _ _ (or_intror _ H3))).
      * apply (H0 meth (in_or_app _ _ _ (or_intror _ H3)) v).
    + split; intros.
      * eapply WfConcatSplits; eauto.
      * eapply WfConcatSplits; eauto.
  -  split; intros; inv WfConcat0; inv WfConcat3.
     + eapply WfConcatMerge; eauto.
       apply (H rule (in_or_app _ _ _ (or_introl _ H3))).
     + eapply WfConcatMerge; eauto.
       apply (H0 meth (in_or_app _ _ _ (or_introl _ H3)) v).
  - econstructor; intros; simpl in *; rewrite in_app_iff in *; destruct H3; inv WfConcat0; inv WfConcat3;
      eauto; eapply (WfConcatSplits (m1 :=m1) (m2 := m2)); eauto.
Qed.

Lemma WfMod_createHide' l : forall m, WfMod (createHide' m l) <-> (SubList l (map fst (getAllMethods m)) /\ WfMod m).
Proof.
  split.
  - induction l; simpl; intros; split; auto.
    + repeat intro; contradiction.
    + inv H.
      specialize (IHl HWf); dest.
      repeat intro.
      destruct H1; subst; rewrite getAllMethods_createHide' in HHideWf; auto.
    + inv H.
      specialize (IHl HWf); dest; auto.
  - induction l; intros; dest; simpl; eauto.
    destruct (SubList_cons H).
    econstructor; eauto.
    rewrite getAllMethods_createHide'; auto.
Qed.

Lemma SeparatedBaseMod_concat l1 l2:
  getAllRegisters (mergeSeparatedBaseMod (l1++l2)) [=] getAllRegisters (mergeSeparatedBaseMod l1) ++ getAllRegisters (mergeSeparatedBaseMod l2).
Proof.
  induction l1.
  - simpl; reflexivity.
  - simpl.
    rewrite <- app_assoc.
    apply Permutation_app_head.
    rewrite IHl1.
    reflexivity.
Qed.

Lemma SeparatedBaseMod_concat_Rules l1 l2:
  getAllRules (mergeSeparatedBaseMod (l1++l2)) [=] getAllRules (mergeSeparatedBaseMod l1) ++ getAllRules (mergeSeparatedBaseMod l2).
Proof.
  induction l1.
  - simpl; reflexivity.
  - simpl.
    rewrite <- app_assoc.
    apply Permutation_app_head.
    rewrite IHl1.
    reflexivity.
Qed.

Lemma SeparatedBaseMod_concat_Meths l1 l2:
  getAllMethods (mergeSeparatedBaseMod (l1++l2)) [=] getAllMethods (mergeSeparatedBaseMod l1) ++ getAllMethods (mergeSeparatedBaseMod l2).
Proof.
  induction l1.
  - simpl; reflexivity.
  - simpl.
    rewrite <- app_assoc.
    apply Permutation_app_head.
    rewrite IHl1.
    reflexivity.
Qed.

Lemma SeparatedBaseFile_concat l1 l2:
  getAllRegisters (mergeSeparatedBaseFile (l1++l2)) [=] getAllRegisters (mergeSeparatedBaseFile l1) ++ getAllRegisters (mergeSeparatedBaseFile l2).
Proof.
  induction l1.
  - simpl; reflexivity.
  - simpl.
    rewrite <- app_assoc.
    apply Permutation_app_head.
    rewrite IHl1.
    reflexivity.
Qed.

Lemma SeparatedBaseFile_concat_Rules l1 l2:
  getAllRules (mergeSeparatedBaseFile (l1++l2)) [=] getAllRules (mergeSeparatedBaseFile l1) ++ getAllRules (mergeSeparatedBaseFile l2).
Proof.
  induction l1.
  - simpl; reflexivity.
  - simpl; assumption.
Qed.

Lemma SeparatedBaseFile_concat_Meths l1 l2:
  getAllMethods (mergeSeparatedBaseFile (l1++l2)) [=] getAllMethods (mergeSeparatedBaseFile l1) ++ getAllMethods (mergeSeparatedBaseFile l2).
Proof.
  induction l1.
  - simpl; reflexivity.
  - simpl.
    rewrite <- app_assoc.
    apply Permutation_app_head.
    rewrite IHl1.
    reflexivity.
Qed.

Lemma DisjKey_perm_rewrite (A B : Type) (l1 l2 l3 l4 : list (A*B)) :
  l1 [=] l2 ->
  l3 [=] l4 ->
  DisjKey l1 l3 ->
  DisjKey l2 l4.
Proof.
  repeat intro; destruct (H1 k); [left; rewrite <- H|right; rewrite <- H0]; auto.
Qed.

Global Instance DisjKey_perm_rewrite' A B :
  Proper (@Permutation (A*B) ==> @Permutation (A*B) ==> iff) (@DisjKey A B) | 10.
Proof.
  repeat red; intros; split; intros; eauto using DisjKey_perm_rewrite, Permutation_sym.
Qed.

Lemma WfActionTConcatAssoc1 m1 m2 m3 (k : Kind) (a : ActionT type k) :
  WfConcatActionT a (ConcatMod (ConcatMod m1 m2) m3) ->
  WfConcatActionT a (ConcatMod m1 (ConcatMod m2 m3)).
Proof.
  intros.
  induction a; inv H; econstructor; EqDep_subst; intros; simpl in *; eauto.
    rewrite app_assoc; assumption.
Qed.


Lemma WfActionTConcatAssoc2 m1 m2 m3 (k : Kind) (a : ActionT type k) :
  WfConcatActionT a (ConcatMod m1 (ConcatMod m2 m3)) ->
  WfConcatActionT a (ConcatMod (ConcatMod m1 m2) m3).
Proof.
  intros.
  induction a; inv H; econstructor; EqDep_subst; intros; simpl in *; eauto.
    rewrite <- app_assoc; assumption.
Qed.

Lemma WfConcatBaseFiles l1 l2 (k : Kind) (a : ActionT type k):
  WfConcatActionT a (ConcatMod (mergeSeparatedBaseFile l1) (mergeSeparatedBaseFile l2)) ->
  WfConcatActionT a (mergeSeparatedBaseFile (l1 ++ l2)).
Proof.
  induction l1.
  - intros.
    apply WfConcatSplits in H; dest; assumption.
  - simpl.
    intros.
    apply WfActionTConcatAssoc1  in H.
    apply WfConcatSplits in H; dest.
    apply WfConcatMerge; eauto.
Qed.

Lemma WfConcatBaseModules l1 l2 (k : Kind) (a : ActionT type k):
  WfConcatActionT a (ConcatMod (mergeSeparatedBaseMod l1) (mergeSeparatedBaseMod l2)) ->
  WfConcatActionT a (mergeSeparatedBaseMod (l1 ++ l2)).
Proof.
  induction l1.
  - intros.
    apply WfConcatSplits in H; dest; assumption.
  - simpl.
    intros.
    apply WfActionTConcatAssoc1  in H.
    apply WfConcatSplits in H; dest.
    apply WfConcatMerge; eauto.
Qed.

Lemma WfAppBaseFiles l1 l2:
  WfMod (mergeSeparatedBaseFile l1) ->
  WfMod (mergeSeparatedBaseFile l2) ->
  WfMod (ConcatMod (mergeSeparatedBaseFile l1) (mergeSeparatedBaseFile l2)) ->
  WfMod (mergeSeparatedBaseFile (l1 ++ l2)).
Proof.
  induction l1; intros; simpl in *; auto.
  apply WfConcatAssoc2 in H1.
  econstructor; inv H1; simpl in *; auto.
  - rewrite <- SeparatedBaseFile_concat in HDisjRegs; assumption.
  - intro; left; intro; contradiction.
  - rewrite <- SeparatedBaseFile_concat_Meths in HDisjMeths; assumption.
  - pose proof (HWf2) as HWf2'.
    inv HWf2; eapply IHl1; eauto.
  - split; intros; destruct WfConcat1.
    + simpl in *; contradiction.
    + specialize (H3 _ H1 v).
      apply WfConcatBaseFiles in H3; assumption.
  - split; intros; destruct WfConcat2.
    rewrite getAllRules_mergeBaseFile in H1; contradiction.
    simpl in H3; repeat rewrite getAllMethods_mergeBaseFile in *.
    rewrite map_app, concat_app in *.
    specialize (H3 _ H1 v); assumption.
Qed.

Lemma WfAppBaseMods l1 l2:
  WfMod (mergeSeparatedBaseMod l1) ->
  WfMod (mergeSeparatedBaseMod l2) ->
  WfMod (ConcatMod (mergeSeparatedBaseMod l1) (mergeSeparatedBaseMod l2)) ->
  WfMod (mergeSeparatedBaseMod (l1 ++ l2)).
Proof.
  induction l1; intros; simpl in *; auto.
  apply WfConcatAssoc2 in H1.
  econstructor; inv H1; simpl in *; auto.
  - rewrite <- SeparatedBaseMod_concat in HDisjRegs; assumption.
  - rewrite <- SeparatedBaseMod_concat_Rules in HDisjRules; assumption.
  - rewrite <- SeparatedBaseMod_concat_Meths in HDisjMeths; assumption.
  - pose proof (HWf2) as HWf2'.
    inv HWf2; eapply IHl1; eauto.
  - split; intros; destruct WfConcat1.
    +  specialize (H2 _ H1).
       apply WfConcatBaseModules in H2; assumption.
    + specialize (H3 _ H1 v).
      apply WfConcatBaseModules in H3; assumption.
  - split; intros; destruct WfConcat2.
    + simpl in *.
      repeat rewrite getAllRules_mergeBaseMod in *.
      rewrite map_app, concat_app in *.
      specialize (H2 _ H1); assumption.
    + simpl in H3; repeat rewrite getAllMethods_mergeBaseMod in *.
      rewrite map_app, concat_app in *.
      specialize (H3 _ H1 v); assumption.
Qed.


Lemma Base_File_Disjoint_Registers m :
  WfMod m ->
  DisjKey (getAllRegisters (mergeSeparatedBaseFile (fst (separateBaseMod m)))) (getAllRegisters (mergeSeparatedBaseMod (snd (separateBaseMod m)))).
Proof.
  intros; induction m; inv H.
  - destruct m; simpl; rewrite app_nil_r; repeat intro;[right|left];intro; contradiction.
  - specialize (IHm HWf).
    simpl; assumption.
  - specialize (IHm1 HWf1); specialize (IHm2 HWf2).
    intro.
    destruct (HDisjRegs k).
    + rewrite separateBaseMod_flatten in H; simpl in H.
      unfold mergeSeparatedMod in H.
      rewrite getAllRegisters_createHide' in H; simpl in *; rewrite map_app,in_app_iff, DeM1 in H; dest.
      destruct (separateBaseMod m1), (separateBaseMod m2); simpl.
      rewrite SeparatedBaseMod_concat, SeparatedBaseFile_concat; repeat rewrite map_app, in_app_iff; repeat rewrite DeM1.
      destruct (IHm1 k), (IHm2 k); simpl in *.
      * left; split; auto.
      * right; split; auto.
      * left; split; auto.
      * right; split; auto.
    + rewrite separateBaseMod_flatten in H; simpl in H.
      unfold mergeSeparatedMod in H.
      rewrite getAllRegisters_createHide' in H; simpl in *; rewrite map_app,in_app_iff, DeM1 in H; dest.
      destruct (separateBaseMod m1), (separateBaseMod m2); simpl.
      rewrite SeparatedBaseMod_concat, SeparatedBaseFile_concat; repeat rewrite map_app, in_app_iff; repeat rewrite DeM1.
      destruct (IHm1 k), (IHm2 k); simpl in *.
      * left; split; auto.
      * left; split; auto.
      * right; split; auto.
      * right; split; auto.
Qed.

Lemma WfActionBreakDownFile m (k : Kind) (a : ActionT type k): 
  WfConcatActionT a m -> WfConcatActionT a (mergeSeparatedBaseFile (fst (snd (separateMod m)))).
Proof.
  induction a; simpl; intros; econstructor; intros; try inv H0; try inv H; EqDep_subst; eauto.
  - rewrite mergeSeparatedBaseFile_noHides; intro; contradiction.
Qed.

Lemma WfActionBreakDownMod m (k : Kind) (a : ActionT type k): 
  WfConcatActionT a m -> WfConcatActionT a (mergeSeparatedBaseMod (snd (snd (separateMod m)))).
Proof.
  induction a; simpl; intros; econstructor; intros; try inv H0; try inv H; EqDep_subst; eauto.
  - rewrite mergeSeparatedBaseMod_noHides; intro; contradiction.
Qed.

Lemma WfModBreakDownFile m :
  WfMod m ->
  WfMod (mergeSeparatedBaseFile (fst (snd (separateMod m)))).
Proof.
  induction m.
  - destruct m; simpl; intros; eauto using WfConcatNil, WfNilMod.
  - intro; inv H; simpl; eapply IHm; eauto.
  - intro; inv H.
    rewrite (separateBaseMod_flatten m1), (separateBaseMod_flatten m2) in HDisjRegs.
    rewrite (separateBaseModule_flatten_Rules m1), (separateBaseModule_flatten_Rules m2) in HDisjRules.
    rewrite (separateBaseModule_flatten_Methods m1), (separateBaseModule_flatten_Methods m2) in HDisjMeths.
    inv WfConcat1; inv WfConcat2.
    setoid_rewrite (separateBaseModule_flatten_Rules m1) in H; setoid_rewrite  (separateBaseModule_flatten_Rules m2) in H1.
    setoid_rewrite  (separateBaseModule_flatten_Methods m1) in H0; setoid_rewrite  (separateBaseModule_flatten_Methods m2) in H2.
    simpl in *.
    unfold mergeSeparatedMod in *; repeat rewrite getAllRegisters_createHide' in *; repeat rewrite getAllMethods_createHide' in *; repeat rewrite getAllRules_createHide' in *; simpl in *.
    remember (separateBaseMod m1) as sbm1; remember (separateBaseMod m2) as sbm2.
    destruct sbm1, sbm2; simpl in *.
    apply WfAppBaseFiles; eauto.
    econstructor; eauto.
    + intro; specialize (HDisjRegs k); repeat rewrite map_app, in_app_iff, DeM1 in *.
      destruct HDisjRegs; dest; eauto.
    + intro; specialize (HDisjRules k); repeat rewrite map_app, in_app_iff, DeM1 in *.
      destruct HDisjRules; dest; eauto.
    + intro; specialize (HDisjMeths k); repeat rewrite map_app, in_app_iff, DeM1 in *.
      destruct HDisjMeths; dest; eauto.
    + split; intros.
      * setoid_rewrite in_app_iff in H.
        specialize (H _ (or_introl _ H3)).
        apply WfActionBreakDownFile in H.
        unfold separateMod in H; simpl in *; rewrite <- Heqsbm2 in H; simpl in *; assumption.
      * setoid_rewrite in_app_iff in H0.
        specialize (H0 _ (or_introl _ H3) v).
        apply WfActionBreakDownFile in H0.
        unfold separateMod in H0; simpl in *; rewrite <- Heqsbm2 in H0; simpl in *; assumption.
    + split; intros.
      * setoid_rewrite in_app_iff in H1.
        specialize (H1 _ (or_introl _ H3)).
        apply WfActionBreakDownFile in H1.
        unfold separateMod in H1; simpl in *; rewrite <- Heqsbm1 in H1; simpl in *; assumption.
      * setoid_rewrite in_app_iff in H2.
        specialize (H2 _ (or_introl _ H3) v).
        apply WfActionBreakDownFile in H2.
        unfold separateMod in H2; simpl in *; rewrite <- Heqsbm1 in H2; simpl in *; assumption.
Qed.

Lemma WfModBreakDownMod m :
  WfMod m ->
  WfMod (mergeSeparatedBaseMod (snd (snd (separateMod m)))).
Proof.
  induction m.
  - destruct m; simpl; intros; eauto using WfConcatNil, WfNilMod.
  - intro; inv H; simpl; eapply IHm; eauto.
  - intro; inv H.
    rewrite (separateBaseMod_flatten m1), (separateBaseMod_flatten m2) in HDisjRegs.
    rewrite (separateBaseModule_flatten_Rules m1), (separateBaseModule_flatten_Rules m2) in HDisjRules.
    rewrite (separateBaseModule_flatten_Methods m1), (separateBaseModule_flatten_Methods m2) in HDisjMeths.
    inv WfConcat1; inv WfConcat2.
    setoid_rewrite (separateBaseModule_flatten_Rules m1) in H; setoid_rewrite  (separateBaseModule_flatten_Rules m2) in H1.
    setoid_rewrite  (separateBaseModule_flatten_Methods m1) in H0; setoid_rewrite  (separateBaseModule_flatten_Methods m2) in H2.
    simpl in *.
    unfold mergeSeparatedMod in *; repeat rewrite getAllRegisters_createHide' in *; repeat rewrite getAllMethods_createHide' in *; repeat rewrite getAllRules_createHide' in *; simpl in *.
    remember (separateBaseMod m1) as sbm1; remember (separateBaseMod m2) as sbm2.
    destruct sbm1, sbm2; simpl in *.
    apply WfAppBaseMods; eauto.
    econstructor; eauto.
    + intro; specialize (HDisjRegs k); repeat rewrite map_app, in_app_iff, DeM1 in *.
      destruct HDisjRegs; dest; eauto.
    + intro; specialize (HDisjRules k); repeat rewrite map_app, in_app_iff, DeM1 in *.
      destruct HDisjRules; dest; eauto.
    + intro; specialize (HDisjMeths k); repeat rewrite map_app, in_app_iff, DeM1 in *.
      destruct HDisjMeths; dest; eauto.
    + split; intros.
      * setoid_rewrite in_app_iff in H.
        specialize (H _ (or_intror _ H3)).
        apply WfActionBreakDownMod in H.
        unfold separateMod in H; simpl in *; rewrite <- Heqsbm2 in H; simpl in *; assumption.
      * setoid_rewrite in_app_iff in H0.
        specialize (H0 _ (or_intror _ H3) v).
        apply WfActionBreakDownMod in H0.
        unfold separateMod in H0; simpl in *; rewrite <- Heqsbm2 in H0; simpl in *; assumption.
    + split; intros.
      * setoid_rewrite in_app_iff in H1.
        specialize (H1 _ (or_intror _ H3)).
        apply WfActionBreakDownMod in H1.
        unfold separateMod in H1; simpl in *; rewrite <- Heqsbm1 in H1; simpl in *; assumption.
      * setoid_rewrite in_app_iff in H2.
        specialize (H2 _ (or_intror _ H3) v).
        apply WfActionBreakDownMod in H2.
        unfold separateMod in H2; simpl in *; rewrite <- Heqsbm1 in H2; simpl in *; assumption.
Qed.

Lemma WfConcat_noHide m1 m2 :
  getHidden m2 = nil ->
  WfConcat m1 m2.
Proof.
  intros.
  split; intros.
  - induction (snd rule type); econstructor; eauto.
    rewrite H; intro; contradiction.
  - induction (projT2 (snd meth) type v); econstructor; eauto.
    rewrite H; intro; contradiction.
Qed.

Lemma merged_WellFormed m:
  WfMod m ->
  WfMod (mergeSeparatedMod (fst (separateMod m)) (fst (snd (separateMod m))) (snd (snd (separateMod m)))).
Proof.
  induction 1.
  - destruct m; simpl in *.
    + unfold mergeSeparatedMod; simpl.
      repeat apply WfConcatNil.
      econstructor; eauto.
    + unfold mergeSeparatedMod; simpl.
      apply WfConcatAssoc2,WfConcatNil,WfConcatComm,WfConcatNil.
      econstructor; eauto.
  - unfold mergeSeparatedMod in *.
    rewrite WfMod_createHide' in *; dest; simpl in *; split; eauto.
    + unfold SubList; intros.
      destruct H2; subst.
      * rewrite (separateBaseModule_flatten_Methods m) in HHideWf.
        unfold mergeSeparatedMod in HHideWf. rewrite getAllMethods_createHide' in HHideWf; simpl in *; assumption.
      * eapply H0; eauto.
  - unfold mergeSeparatedMod in *.
    rewrite WfMod_createHide' in *; dest; split.
    + unfold separateMod in *.
      repeat intro.
      specialize (separateBaseModule_flatten_Methods (ConcatMod m1 m2)) as TMP1.
      specialize (separateBaseModule_flatten_Methods m1) as TMP2.
      specialize (separateBaseModule_flatten_Methods m2) as TMP3.
      unfold mergeSeparatedMod in *; rewrite getAllMethods_createHide' in *.
      rewrite <- TMP1.
      rewrite <- TMP2 in H3.
      rewrite <- TMP3 in H1.
      simpl in *; rewrite map_app in *; rewrite in_app_iff in *.
      destruct H5.
      * left; eapply H3; eauto.
      * right; eapply H1; eauto.
    + inv H4; inv H2.
      econstructor.
      * specialize (separateBaseMod_flatten (ConcatMod m1 m2)) as TMP1;
        specialize (separateBaseMod_flatten m1) as TMP2; specialize (separateBaseMod_flatten m2) as TMP3.
        unfold mergeSeparatedMod in *; rewrite getAllRegisters_createHide' in *; simpl in *; intro.
        specialize (HDisjRegs k); rewrite TMP2, TMP3 in HDisjRegs.
        repeat rewrite map_app,in_app_iff,DeM1 in *.
        destruct (separateBaseMod m1), (separateBaseMod m2); simpl in *.
        rewrite SeparatedBaseMod_concat, SeparatedBaseFile_concat; repeat rewrite map_app, in_app_iff, DeM1.
        destruct HDisjRegs,(HDisjRegs0 k),(HDisjRegs1 k); dest;[left|right|left|right|left|left|right|right];split; auto.
      * specialize (separateBaseModule_flatten_Rules (ConcatMod m1 m2)) as TMP1;
        specialize (separateBaseModule_flatten_Rules m1) as TMP2; specialize (separateBaseModule_flatten_Rules m2) as TMP3.
        unfold mergeSeparatedMod in *; rewrite getAllRules_createHide' in *; simpl in *; intro.
        specialize (HDisjRules k); rewrite TMP2, TMP3 in HDisjRules.
        repeat rewrite map_app,in_app_iff,DeM1 in *.
        destruct (separateBaseMod m1), (separateBaseMod m2); simpl in *.
        rewrite SeparatedBaseMod_concat_Rules, SeparatedBaseFile_concat_Rules; repeat rewrite map_app, in_app_iff, DeM1.
        destruct HDisjRules,(HDisjRules0 k),(HDisjRules1 k); dest;[left|right|left|right|left|left|right|right];split; auto.
      * specialize (separateBaseModule_flatten_Methods (ConcatMod m1 m2)) as TMP1;
        specialize (separateBaseModule_flatten_Methods m1) as TMP2; specialize (separateBaseModule_flatten_Methods m2) as TMP3.
        unfold mergeSeparatedMod in *; rewrite getAllMethods_createHide' in *; simpl in *; intro.
        specialize (HDisjMeths k); rewrite TMP2, TMP3 in HDisjMeths.
        repeat rewrite map_app,in_app_iff,DeM1 in *.
        destruct (separateBaseMod m1), (separateBaseMod m2); simpl in *.
        rewrite SeparatedBaseMod_concat_Meths, SeparatedBaseFile_concat_Meths; repeat rewrite map_app, in_app_iff, DeM1.
        destruct HDisjMeths,(HDisjMeths0 k),(HDisjMeths1 k); dest;[left|right|left|right|left|left|right|right];split; auto.
      * apply WfModBreakDownFile; econstructor; eauto.
      * apply WfModBreakDownMod; econstructor; eauto.
      * apply WfConcat_noHide.
        apply mergeSeparatedBaseMod_noHides.
      * apply WfConcat_noHide.
        apply mergeSeparatedBaseFile_noHides.
Qed.

Definition WfMergedMod (m : WfModule) :  WfModule :=
  (mkWfMod (merged_WellFormed (Wf_cond m))).

Lemma merged_perm_equality m :
  WfModule_perm m (WfMergedMod m).
Proof.
  constructor; simpl.
  - apply separateBaseMod_flatten.
  - apply separateBaseModule_flatten_Methods.
  - apply separateBaseModule_flatten_Rules.
  - apply separateBaseModule_flatten_Hides.
Qed.

Lemma TraceInclusion_Merge_l (m : WfModule) :
  TraceInclusion m (WfMergedMod m).
Proof.
  apply PTraceInclusion_TraceInclusion.
  - apply (Wf_cond m).
  - apply (Wf_cond (WfMergedMod m)).
  - repeat intro.
    apply (PTrace_WfModule_rewrite (merged_perm_equality m)) in H.
    exists ls.
    split.
    + unfold PTraceList; exists o; eauto.
    + apply WeakInclusionsRefl.
Qed.

Lemma TraceInclusion_Merge_r (m : WfModule) :
  TraceInclusion (WfMergedMod m) m.
Proof.
  apply PTraceInclusion_TraceInclusion.
  - apply (Wf_cond (WfMergedMod m)).
  - apply (Wf_cond m).
  - repeat intro.
    apply (PTrace_WfModule_rewrite (WfModule_perm_sym (merged_perm_equality m))) in H.
    exists ls.
    split.
    + unfold PTraceList; exists o; eauto.
    + apply WeakInclusionsRefl.
Qed.