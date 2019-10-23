(*
 * Notations_rewrites.v
 *
 * Rewriting rules useful for Notation definitions
 *)
Require Import Kami.AllNotations.
Require Import List.
Require Import Vector.
Import VectorNotations.
Import ListNotations.
Require Import Kami.Notations.
Require Import Coq.Logic.ClassicalFacts.
Require Import Coq.Logic.Classical.

Lemma app_rewrite1: forall T (a:T) b c, (a::b)++c=a::(b++c).
Proof.
  simpl.
  intros.
  reflexivity.
Qed.

Lemma Registers1: forall a b, Registers (a::b) = (MERegister a)::(Registers b).
Proof.
  intros.
  simpl Registers.
  reflexivity.
Qed.

Lemma Registers2: Registers []=[].
Proof.
  simpl.
  reflexivity.
Qed.

Lemma Registers_dist_append : forall l1 l2, Registers (l1++l2)=(Registers l1)++(Registers l2).
Proof.
  intros.
  induction l1.
  + simpl.
    reflexivity.
  + simpl.
    rewrite IHl1.
    reflexivity.
Qed.

Lemma app_rewrite2: forall A (f:A) (r:list A), [f]++r=f::r.
  Proof. reflexivity. Qed.

Hint Rewrite app_rewrite1 app_rewrite2 app_nil_l app_nil_r Registers1 Registers2 : kami_rewrite_db.
Hint Rewrite Registers1 Registers2 : kami_rewrite_db.

Lemma makeModule_rules_Registers: forall l, makeModule_rules (Registers l)=[].
Proof.
  intros.
  induction l.
  + simpl.
    reflexivity.
  + simpl.
    rewrite IHl.
    simpl.
    reflexivity.
Qed.
 
Lemma makeModule_rules_append: forall l1 l2, (makeModule_rules (l1++l2))=(makeModule_rules l1)++(makeModule_rules l2).
Proof.
  intros.
  induction l1.
  + simpl.
    reflexivity.
  + simpl.
    rewrite IHl1.
    destruct a; reflexivity.
Qed.

Lemma makeModule_rules_MERegister: forall a b, makeModule_rules ((MERegister a)::b)=makeModule_rules b.
Proof.
  simpl.
  reflexivity.
Qed.

Lemma makeModule_rules_MERule: forall a b, makeModule_rules ((MERule a)::b)=a::(makeModule_rules b).
Proof.
  simpl.
  reflexivity.
Qed.

Lemma makeModule_rules_nil: makeModule_rules []=[].
Proof.
  simpl.
  reflexivity.
Qed.

Hint Rewrite makeModule_rules_Registers makeModule_rules_append makeModule_rules_MERegister makeModule_rules_MERule makeModule_rules_nil : kami_rewrite_db.
 
Lemma makeModule_meths_Registers: forall l, makeModule_meths (Registers l)=[].
Proof.
  intros.
  induction l.
  simpl.
  reflexivity.
  simpl.
  rewrite IHl.
  simpl.
  reflexivity.
Qed.
 
Lemma makeModule_meths_append: forall l1 l2, makeModule_meths (l1++l2)=(makeModule_meths l1)++(makeModule_meths l2).
Proof.
  intros.
  induction l1.
  + simpl.
    reflexivity.
  + simpl.
    rewrite IHl1.
    destruct a; reflexivity.
Qed.

Lemma makeModule_meths_MERegister: forall a b, makeModule_meths ((MERegister a)::b)=makeModule_meths b.
Proof.
  simpl.
  reflexivity.
Qed.

Lemma makeModule_meths_MERule: forall a b, makeModule_meths ((MERule a)::b)=(makeModule_meths b).
Proof.
  simpl.
  reflexivity.
Qed.

Lemma makeModule_meths_nil: makeModule_meths []=[].
Proof.
  simpl.
  reflexivity.
Qed.

Hint Rewrite makeModule_meths_Registers makeModule_meths_append makeModule_meths_MERegister makeModule_meths_MERule makeModule_meths_nil : kami_rewrite_db.

 
Lemma makeModule_regs_Registers: forall l, makeModule_regs (Registers l)=l.
Proof.
  intros.
  induction l.
  + simpl.
    reflexivity.
  + simpl.
    rewrite IHl.
    simpl.
    reflexivity.
Qed.
 
Lemma makeModule_regs_append: forall l1 l2, makeModule_regs (l1++l2)=(makeModule_regs l1)++(makeModule_regs l2).
Proof.
  intros.
  induction l1.
  + simpl.
    reflexivity.
  + simpl.
    rewrite IHl1.
    destruct a; reflexivity.
Qed.


Lemma makeModule_regs_MERegister: forall a b, makeModule_regs ((MERegister a)::b)=a::(makeModule_regs b).
Proof.
  simpl.
  reflexivity.
Qed.

Lemma makeModule_regs_MERule: forall a b, makeModule_regs ((MERule a)::b)=makeModule_regs b.
Proof.
  simpl.
  reflexivity.
Qed.

Lemma makeModule_regs_nil: makeModule_regs []=[].
Proof.
  simpl.
  reflexivity.
Qed.

Hint Rewrite makeModule_regs_Registers makeModule_regs_append makeModule_regs_MERegister makeModule_regs_MERule makeModule_regs_nil : kami_rewrite_db.

Lemma map1: forall T R (f: T -> R) (h:T) t, List.map f (h::t)=(f h)::(List.map f t).
Proof.
  simpl.
  reflexivity.
Qed.

Lemma getAllRules_ConcatMod : forall a b, getAllRules (ConcatMod a b)=getAllRules a++getAllRules b.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma getAllMethods_ConcatMod : forall a b, getAllMethods (ConcatMod a b)=getAllMethods a++getAllMethods b.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

(*
Lemma getCallsWithSignPerRule_append: forall T a b, getCallsWithSignPerRule (a++b)=getCallsWithSignPerRule a++getCallsWithSignPerRule b.
Proof.*)

Lemma getCallsPerMod_ConcatMod : forall a b, getCallsPerMod (ConcatMod a b)=(getCallsPerMod a)++(getCallsPerMod b).
Proof.
  unfold getCallsPerMod.
  simpl.
  intros.
  rewrite map_app.
  reflexivity.
Qed.

Lemma getCallsPerMod_BaseRegFile: forall m,
  getCallsPerMod (Base (BaseRegFile m)) = [].
Proof.
  intros.
  unfold getCallsPerMod.
  unfold getCallsWithSignPerMod.
  simpl.
  unfold getRegFileMethods.
  destruct m.
  destruct rfRead.
  + simpl.
    unfold getCallsWithSignPerMeth.
    destruct rfIsWrMask.
    - simpl.
      unfold readRegFile.
      induction reads.
      * reflexivity.
      * simpl.
        rewrite IHreads.
        reflexivity.
    - simpl.
      unfold readRegFile.
      induction reads.
      * reflexivity.
      * simpl.
        rewrite IHreads.
        reflexivity.
  + simpl.
    unfold getCallsWithSignPerMeth.
    simpl.
    unfold readSyncRegFile.
    destruct rfIsWrMask.
    simpl.
    destruct isAddr.
    * simpl.
      induction reads.
      -- reflexivity.
      -- simpl.
         rewrite map_app in IHreads.
         rewrite map_app.
         rewrite map_cons.
         simpl.
         rewrite concat_app in IHreads.
         rewrite concat_app.
         rewrite concat_cons.
         rewrite app_nil_l.
         rewrite IHreads.
         reflexivity.
    * simpl.
      induction reads.
      -- reflexivity.
      -- simpl.
         rewrite map_app in IHreads.
         rewrite map_app.
         rewrite map_cons.
         simpl.
         rewrite concat_app in IHreads.
         rewrite concat_app.
         rewrite concat_cons.
         rewrite app_nil_l.
         rewrite IHreads.
         reflexivity.
    * simpl.
      destruct isAddr.
      -- simpl.
         induction reads.
         ++ reflexivity.
         ++ simpl.
            rewrite map_app in IHreads.
            rewrite map_app.
            rewrite map_cons.
            simpl.
            rewrite concat_app in IHreads.
            rewrite concat_app.
            rewrite concat_cons.
            rewrite app_nil_l.
            rewrite IHreads.
            reflexivity.
      -- simpl.
         induction reads.
         ++ reflexivity.
         ++ simpl.
            rewrite map_app in IHreads.
            rewrite map_app.
            rewrite map_cons.
            simpl.
            rewrite concat_app in IHreads.
            rewrite concat_app.
            rewrite concat_cons.
            rewrite app_nil_l.
            rewrite IHreads.
            reflexivity.
Qed.

  Lemma getCallsPerMod_Base: forall (m : BaseModule), getCallsPerMod (Base m)=List.map fst (getCallsWithSignPerMod m).
  Proof.
    unfold getCallsPerMod.
    reflexivity.
  Qed.

Lemma map_getCallsPerMod_map_BaseRegFile: forall l,
  (concat (List.map getCallsPerMod
     (List.map (fun m : RegFileBase => (Base (BaseRegFile m))) l)))=[].
Proof.
  intros.
  induction l.
  + reflexivity.
  + simpl.
    rewrite IHl.
    rewrite app_nil_r.
    rewrite getCallsPerMod_BaseRegFile.
    reflexivity.
Qed.

  Lemma getCallsPerMod_fold_right_ConcatMod: forall (a:Mod) (l:list Mod), getCallsPerMod (List.fold_right ConcatMod a l)=concat (List.map getCallsPerMod l)++(getCallsPerMod a).
  Proof.
    intros.
    induction l.
    + reflexivity.
    + simpl.
      rewrite <- app_assoc.
      rewrite <- IHl.
      rewrite getCallsPerMod_ConcatMod.
      reflexivity. 
Qed.
 
  Hint Rewrite map1 getAllRules_ConcatMod getAllMethods_ConcatMod getCallsPerMod_ConcatMod map_getCallsPerMod_map_BaseRegFile : kami_rewrite_db.
  Hint Rewrite getCallsPerMod_fold_right_ConcatMod getCallsPerMod_BaseRegFile : kami_rewrite_db.

  Theorem getAllRegisters_ConcatMod: forall a b, getAllRegisters (ConcatMod a b)=getAllRegisters(a)++getAllRegisters(b).
  Proof.
     reflexivity.
  Qed.

  Axiom EquivThenEqual: prop_extensionality.

  Theorem equiv_rewrite: forall x y, (x=y)=(x<->y).
  Proof.
    intros.
    apply EquivThenEqual.
    split.
    + intros.
      subst.
      split.
      - intros.
        apply H.
      - intros.
        apply H.
    + intros.
      inversion H; subst; clear H.
      apply EquivThenEqual.
      split.
      - apply H0.
      - apply H1.
  Qed.

  Theorem DisjKey_Cons1:
    forall T Q (a:(T*Q)) x z, DisjKey (a::x) z = ((~(List.In (fst a) (List.map fst z))) /\ DisjKey x z).
  Proof.
    intros.
    unfold DisjKey.
    simpl.
    rewrite equiv_rewrite.
    split.
    + intros.
      split.
      - assert (~(fst a=fst a \/ List.In (fst a) (List.map fst x)) \/
                ~ List.In (fst a) (List.map fst z)).
        apply H.
        inversion H0; subst; clear H0.
        tauto.
        tauto.
      - simpl.
        intros.
        assert (~(fst a=k \/ List.In k (List.map fst x)) \/
                ~ List.In k (List.map fst z)).
        apply H.
        inversion H0; subst; clear H0.
        apply not_or_and in H1.
        inversion H1; subst; clear H1.
        left.
        apply H2.
        right.
        apply H1.
    + intros.
      inversion H; subst; clear H.
      classical_right.
      apply NNPP in H.
      inversion H; subst; clear H.
      - apply H0.
      - simpl.
      assert (~ List.In k (List.map fst x) \/ ~ List.In k (List.map fst z)).
      apply H1.
      inversion H; subst; clear H.
      apply H3 in H2.
      inversion H2.
      apply H3.
Qed.

Theorem DisjKey_Cons2:
    forall T Q (a:(T*Q)) x z, DisjKey x (a::z) = ((~(List.In (fst a) (List.map fst x))) /\ DisjKey x z).
Proof.
  intros.
  unfold DisjKey.
  simpl.
  rewrite equiv_rewrite.
  split.
  + intros.
    split.
    - assert (~ List.In (fst a) (List.map fst x) \/
              ~ (fst a = fst a \/ List.In (fst a) (List.map fst z))).
      apply H.
      inversion H0; subst; clear H0.
      tauto.
      tauto.
    - simpl.
      intros.
      assert (
              ~ List.In k (List.map fst x) \/
              ~(fst a=k \/ List.In k (List.map fst z))).
      apply H.
      inversion H0; subst; clear H0.
      left.
      apply H1.
      apply not_or_and in H1.
      inversion H1; subst; clear H1.
      right.
      apply H2.
  + intros.
    inversion H; subst; clear H.
    assert (~ List.In k (List.map fst x) \/ ~ List.In k (List.map fst z)).
    apply H1.
    classical_left.
    apply NNPP in H2.
    inversion H2; subst; clear H2.
    - apply H0.
    - simpl.
      inversion H; subst; clear H.
      apply H2.
      apply H2 in H3.
      inversion H3.
Qed.

Theorem DisjKey_Append1: forall T Q (x:list (T*Q)) (y:list (T*Q)) (z:list (T*Q)), DisjKey (x++y) z=(DisjKey x z /\ DisjKey y z).
  Proof.
    intros.
    induction x.
    + simpl.
      unfold DisjKey.
      simpl.
      rewrite equiv_rewrite.
      split.
      - intros.
        * split.
          tauto.
          apply H.
      - intros.
        inversion H. subst. clear H.
        apply H1.
    + simpl.
      rewrite ?DisjKey_Cons1.
      rewrite equiv_rewrite.
      split.
      intros.
      inversion H; subst; clear H.
      split.
      - split.
        apply H0.
        rewrite IHx in H1.
        inversion H1; subst; clear H1.
        apply H.
      - simpl.
        rewrite IHx in H1.
        inversion H1; subst; clear H1.
        apply H2.
      - simpl.
        intros.
        inversion H; subst; clear H.
        split.
        * inversion H0; subst; clear H0.
          apply H.
        * simpl.
          rewrite IHx.
          split.
          ++ inversion H0; subst; clear H0.
             apply H2.
          ++ simpl.
             apply H1.
  Qed.

  Theorem DisjKey_Append2: forall T Q (x:list (T*Q)) (y:list (T*Q)) (z:list (T*Q)), DisjKey x (y++z)=(DisjKey x y /\ DisjKey x z).
  Proof.
    intros.
    induction y.
    rewrite equiv_rewrite.
    + simpl.
      unfold DisjKey.
      split.
      - intros.
        tauto.
      - simpl.
        intros.
        inversion H; subst; clear H.
        apply H1.
    + simpl.
      rewrite ?DisjKey_Cons1.
      rewrite equiv_rewrite.
      split.
      - intros.
        rewrite DisjKey_Cons2.
        rewrite DisjKey_Cons2 in H.
        inversion H; subst; clear H.
        rewrite and_assoc.
        rewrite <- IHy.
        split.
        * apply H0.
        * apply H1.
      - rewrite ?DisjKey_Cons2.
        rewrite ?DisjKey_Cons2 in IHy.
        rewrite and_assoc.
        rewrite <- IHy.
        intros.
        apply H.
  Qed.

  Theorem DisjKey_In_map2: forall A B a (k:A) r l, @DisjKey A B a ((k,r)::l)=(~List.In k (List.map fst a) /\ (DisjKey a l)).
  Proof.
    intros.
    rewrite DisjKey_Cons2.
    simpl.
    reflexivity.
  Qed.
    
  Theorem DisjKey_In_map1: forall A B b (k:A) r l, @DisjKey A B ((k,r)::l) b=(~List.In k (List.map fst b) /\ (DisjKey l b)).
  Proof.
    intros.
    rewrite DisjKey_Cons1.
    simpl.
    reflexivity.
  Qed.

  Theorem DisjKey_In_map_fst2: forall A B a (f:(A*B)) l, @DisjKey A B a (f::l)=(~List.In (fst f) (List.map fst a) /\ (DisjKey a l)).
  Proof.
    intros.
    rewrite DisjKey_Cons2.
    reflexivity.
  Qed.

    
  Theorem DisjKey_In_map_fst1: forall A B b (f:(A*B)) l, @DisjKey A B (f::l) b=(~List.In (fst f) (List.map fst b) /\ (DisjKey l b)).
  Proof.
    intros.
    rewrite DisjKey_Cons1.
    reflexivity.
  Qed.

  Hint Rewrite getAllRegisters_ConcatMod DisjKey_Append1 DisjKey_Append2 DisjKey_In_map2 DisjKey_In_map1 : kami_rewrite_db.
  Hint Rewrite DisjKey_In_map_fst2 DisjKey_In_map_fst1: kami_rewrite_db.


