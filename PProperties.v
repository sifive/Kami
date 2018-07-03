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
Qed.

Lemma Substeps_PSubsteps m:
  forall (o : RegsT) (l : list FullLabel),
    Substeps m o l -> PSubsteps m o l.
  induction 1; subst.
  - econstructor 1; rewrite HRegs; reflexivity.
  - econstructor 2.
    + rewrite HRegs; reflexivity.
    + apply HInRules.
    + apply (SemAction_PSemAction HAction).
    + assumption.
    + assumption.
    + reflexivity.
    + assumption.
    + assumption.
    + assumption.
    + assumption.
  - econstructor 3.
    + rewrite HRegs; reflexivity.
    + apply HInMeths.
    + apply (SemAction_PSemAction HAction).
    + assumption.
    + assumption.
    + reflexivity.
    + assumption.
    + assumption.
    + assumption.
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
Qed.

Global Instance PSubsteps_List_FullLabel_perm_rewrite' :
  Proper (Logic.eq ==> Logic.eq ==> List_FullLabel_perm ==> iff) (@PSubsteps) | 10.
repeat red; intros; split; intros; subst; eauto using List_FullLabel_perm_sym, PSubsteps_List_FullLabel_perm_rewrite.
Qed.

Lemma List_FullLabel_perm_InExec_rewrite f l l' :
  List_FullLabel_perm l l' ->
  InExec f l ->
  InExec f l'.
Proof.
  unfold InExec; induction 1; simpl; auto; intros.
  - destruct H1.
    + inversion H; subst; simpl in *; auto.
    + right; auto.
  - destruct H2; subst.
    + destruct H, H0; subst; simpl in *; auto.
    + destruct H, H0; subst; simpl in *; auto.
      destruct H2; auto.
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
  (* - unfold UpdRegs in HPUpdRegs; apply PStep_Step in HPStep; dest. *)
  (* - specialize (key_perm_eq _ _ (Permutation_sym HUpdRegs1)) as TMP;dest. *)
  (*   exists x, nil. *)
  (*   repeat split; eauto using Permutation_sym; econstructor; auto. *)
  (*   eapply RegInit_generalized_list; eauto. *)
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

