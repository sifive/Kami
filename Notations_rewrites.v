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
Require Import Kami.Lib.EclecticLib.

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

Hint Rewrite Registers_dist_append : kami_rewrite_db.

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

Lemma fold_right1: forall A B (f : B -> A -> A) (a0 : A) (h : B) (t : list B), List.fold_right f a0 (h::t)=f h (List.fold_right f a0 t).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma getAllRegisters_fold_right_ConcatMod : forall (b: Mod) (l:list Mod), getAllRegisters (List.fold_right ConcatMod b l)=(concat (List.map getAllRegisters l))++(getAllRegisters b).
Proof.
    induction l.
    + simpl.
      reflexivity.
    + simpl.
      rewrite IHl.
      rewrite app_assoc.
      reflexivity.
Qed.

Lemma getAllMethods_fold_right_ConcatMod : forall (b: Mod) (l:list Mod), getAllMethods (List.fold_right ConcatMod b l)=(concat (List.map getAllMethods l))++(getAllMethods b).
Proof.
    induction l.
    + simpl.
      reflexivity.
    + simpl.
      rewrite IHl.
      rewrite app_assoc.
      reflexivity.
Qed.

Lemma getAllRules_fold_right_ConcatMod : forall (b: Mod) (l:list Mod), getAllRules (List.fold_right ConcatMod b l)=(concat (List.map getAllRules l))++(getAllRules b).
Proof.
    induction l.
    + simpl.
      reflexivity.
    + simpl.
      rewrite IHl.
      rewrite app_assoc.
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
 
  Hint Rewrite map1 fold_right1 getAllRules_ConcatMod getAllMethods_ConcatMod getCallsPerMod_ConcatMod map_getCallsPerMod_map_BaseRegFile : kami_rewrite_db.
  Hint Rewrite getCallsPerMod_fold_right_ConcatMod getCallsPerMod_BaseRegFile : kami_rewrite_db.

  Theorem getAllRegisters_ConcatMod: forall a b, getAllRegisters (ConcatMod a b)=getAllRegisters(a)++getAllRegisters(b).
  Proof.
     reflexivity.
  Qed.

  (*Axiom EquivThenEqual: prop_extensionality.

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
  Qed.*)

Theorem DisjKey_Append1:
  forall T Q (x:list (T*Q)) y z (W:forall (a1:T) (a2:T), {a1=a2}+{a1<>a2}),
  DisjKey (x++y) z<->(DisjKey x z /\ DisjKey y z).
  Proof.
    intros.
    rewrite ?DisjKeyWeak_same.
    induction x.
    + simpl.
      unfold DisjKeyWeak.
      simpl.
      split.
      - intros.
        * split.
          tauto.
          apply H.
      - intros.
        inversion H. subst. clear H.
        eapply H3.
        apply H0.
        apply H1.
    + simpl.
      repeat (rewrite <- DisjKeyWeak_same).
      rewrite ?DisjKey_Cons1.
      rewrite ?DisjKeyWeak_same.
      split.
      - intros.
        inversion H; subst; clear H.
        split.
        * split.
          ++ apply H0.
          ++ rewrite IHx in H1.
             inversion H1; subst; clear H1.
             apply H.
        * rewrite IHx in H1.
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
      - apply W.
      - apply W.
      - apply W.
      - apply W.
      - apply W.
      - apply W.
      - apply W.
      - apply W.
    + apply W.
    + apply W.
    + apply W.
Qed.

  Theorem DisjKey_Append2:
    forall T Q (x:list (T*Q)) y z (W:forall (a1:T) (a2:T), {a1=a2}+{a1<>a2}),
           DisjKey x (y++z)<->(DisjKey x y /\ DisjKey x z).
  Proof.
    intros.
    rewrite ?DisjKeyWeak_same.
    induction y.
    + simpl.
      unfold DisjKeyWeak.
      split.
      - intros.
        tauto.
      - simpl.
        intros.
        inversion H; subst; clear H.
        assert (List.In k (List.map fst x) -> List.In k (List.map fst z) -> False).
        apply H3.
        apply H.
        apply H0.
        apply H1.
    + simpl.
      repeat (rewrite <- DisjKeyWeak_same).
      rewrite ?DisjKey_Cons2.
      rewrite ?DisjKeyWeak_same.
      split.
      - intros.
        inversion H; subst; clear H.
        * split.
          ++ split.
             -- apply H0.
             -- apply IHy in H1.
                inversion H1; subst; clear H1.
                apply H.
          ++ apply IHy in H1.
             inversion H1; subst; clear H1.
             apply H2.
      - intros.
        inversion H; subst; clear H.
        inversion H0; subst; clear H0.
        split.
        * apply H.
        * apply IHy.
          split.
          ++ apply H2.
          ++ apply H1.
      - apply W.
      - apply W.
      - apply W.
      - apply W.
      - apply W.
      - apply W.
      - apply W.
      - apply W.
    + apply W.
    + apply W.
    + apply W.
  Qed.

  Theorem DisjKey_In_map2:
    forall A B a (k:A) r l (W:forall (a1:A) (a2:A), {a1=a2}+{a1<>a2}), @DisjKey A B a ((k,r)::l)<->(~List.In k (List.map fst a) /\ (DisjKey a l)).
  Proof.
    intros.
    rewrite DisjKey_Cons2.
    simpl.
    reflexivity.
    apply W.
  Qed.
    
  Theorem DisjKey_In_map1: forall A B b (k:A) r l (W:forall (a1:A) (a2:A), {a1=a2}+{a1<>a2}),
                           @DisjKey A B ((k,r)::l) b<->(~List.In k (List.map fst b) /\ (DisjKey l b)).
  Proof.
    intros.
    rewrite DisjKey_Cons1.
    simpl.
    reflexivity.
    apply W.
  Qed.

  Theorem DisjKey_In_map_fst2: forall A B a (f:(A*B)) l (W:forall (a1:A) (a2:A), {a1=a2}+{a1<>a2}),
                               @DisjKey A B a (f::l)<->(~List.In (fst f) (List.map fst a) /\ (DisjKey a l)).
  Proof.
    intros.
    rewrite DisjKey_Cons2.
    reflexivity.
    apply W.
  Qed.

    
  Theorem DisjKey_In_map_fst1: forall A B b (f:(A*B)) l (W:forall (a1:A) (a2:A), {a1=a2}+{a1<>a2}),
          @DisjKey A B (f::l) b<->(~List.In (fst f) (List.map fst b) /\ (DisjKey l b)).
  Proof.
    intros.
    rewrite DisjKey_Cons1.
    reflexivity.
    apply W.
  Qed.

  Theorem map_getAllRegisters_map_RegFileBase: forall m,
    (List.map getAllRegisters (List.map (fun mm: RegFileBase =>  (Base (BaseRegFile mm))) m))=
        (List.map (fun mm: RegFileBase => getRegFileRegisters mm) m).
  Proof.
      induction m.
      + reflexivity.
      + simpl.
        rewrite IHm.
        reflexivity.
  Qed.

  Theorem map_getAllMethods_map_RegFileBase: forall m,
    (List.map getAllMethods (List.map (fun mm: RegFileBase =>  (Base (BaseRegFile mm))) m))=
        (List.map (fun mm: RegFileBase => getRegFileMethods mm) m).
  Proof.
      induction m.
      + reflexivity.
      + simpl.
        rewrite IHm.
        reflexivity.
  Qed.

  Theorem concat_map_getAllRules_map_RegFileBase: forall m,
    (concat (List.map getAllRules (List.map (fun mm: RegFileBase =>  (Base (BaseRegFile mm))) m))) = List.nil.
  Proof.
      induction m.
      + reflexivity.
      + simpl.
        rewrite IHm.
        reflexivity.
  Qed.

  Hint Rewrite getAllRegisters_fold_right_ConcatMod getAllMethods_fold_right_ConcatMod
       getAllRules_fold_right_ConcatMod
       concat_map_getAllRules_map_RegFileBase
       map_getAllMethods_map_RegFileBase map_getAllRegisters_map_RegFileBase : kami_rewrite_db.
  Hint Rewrite getAllRegisters_ConcatMod DisjKey_Append1 DisjKey_Append2 DisjKey_In_map2 DisjKey_In_map1 : kami_rewrite_db.
  Hint Rewrite DisjKey_In_map_fst2 DisjKey_In_map_fst1: kami_rewrite_db.

  Theorem getAllRegisters_BaseMod: forall regs rules dms,
      getAllRegisters (BaseMod regs rules dms)=regs.
  Proof.
      simpl.
      reflexivity.
  Qed.
  
  Theorem append_equal_prefix: forall T (a: list T) (b: list T) (c: list T), (a++b=a++c)->(b=c).
  Proof.
    intros.
    induction a.
    + rewrite ?app_nil_l.
      apply H.
    + inversion H; subst; clear H.
      apply IHa.
      apply H1.
  Qed.
  
  (*Theorem append_nequal_prefix: forall T (a: list T) (b: list T) (c: list T), (List.app a b<>List.app a c)<>(b=c).
  Proof.
      induction a.
      + reflexivity.
      + intros.
        simpl.
        destruct eq.
  Admitted.*)
    
  Hint Rewrite getAllRegisters_BaseMod append_equal_prefix : kami_rewrite_db.

  Theorem getAllRegisters_makeModule_MERegister: forall a b, getAllRegisters (makeModule ((MERegister a)::b))=a::getAllRegisters (makeModule b).
Proof.
    simpl.
    intros.
    reflexivity.
Qed.

Theorem getAllRegisters_makeModule_MERule: forall a b, getAllRegisters (makeModule ((MERule a)::b))=getAllRegisters (makeModule b).
Proof.
    simpl.
    intros.
    reflexivity.
Qed.

Theorem getAllRegisters_makeModule_Registers: forall a b, getAllRegisters (makeModule ((Registers a)++b))=a++getAllRegisters (makeModule b).
Proof.
    simpl.
    intros.
    induction a.
    + simpl.
      reflexivity.
    + simpl.
      rewrite IHa.
      reflexivity.
Qed.

Hint Rewrite getAllRegisters_makeModule_MERegister
             getAllRegisters_makeModule_Registers
           getAllRegisters_makeModule_MERule : kami_rewrite_db.

Theorem in_app: forall T (x:T) (a:List.list T) (b:List.list T), (List.In x (a++b)) <-> (List.In x a)\/(List.In x b).
Proof.
    intros.
    split.
    + intros.
      induction a.
      - simpl in H.
        right.
        apply H.
      - simpl in H.
        simpl.
        inversion H; subst; clear H.
        * left.
          left.
          reflexivity.
        * apply <- or_assoc.
          right.
          apply IHa.
          apply H0.
    + intros.
      inversion H; subst; clear H.
      - induction a.
        * unfold List.In in H0.
          inversion H0.
        * simpl.
          simpl in H0.
          inversion H0; subst; clear H0.
          ++ left.
             reflexivity.
          ++ right.
             apply IHa.
             apply H.
      - induction a.
        * simpl.
          apply H0.
        * simpl.
          right.
          apply IHa.
Qed.

Hint Rewrite in_app : kami_rewrite_db.

Lemma getAllMethods_makeModule_append: forall a b, getAllMethods (makeModule (a++b))=getAllMethods (makeModule a)++getAllMethods (makeModule b).
Proof.
    induction a.
    + reflexivity.
    + intros.
      destruct a.
      - apply IHa.
      - apply IHa.
      - unfold makeModule.
        simpl.
        simpl in IHa.
        rewrite IHa.
        reflexivity.
Qed.

Hint Rewrite getAllMethods_makeModule_append : kami_rewrite_db.

Lemma getAllMethods_makeModule_MERegister: forall a b, getAllMethods (makeModule ((MERegister a)::b))=getAllMethods (makeModule b).
Proof.
    simpl.
    reflexivity.
Qed.

Hint Rewrite getAllMethods_makeModule_MERegister : kami_rewrite_db.

Lemma getAllMethods_makeModule_MERule: forall a b, getAllMethods (makeModule ((MERule a)::b))=getAllMethods (makeModule b).
Proof.
    simpl.
    reflexivity.
Qed.

Hint Rewrite getAllMethods_makeModule_MERule : kami_rewrite_db.

Lemma getAllMethods_makeModule_Registers: forall a, getAllMethods (makeModule (Registers a))=[].
Proof.
    induction a.
    + reflexivity.
    + simpl.
      apply IHa.
Qed.

Hint Rewrite getAllMethods_makeModule_Registers : kami_rewrite_db.

Lemma getAllRules_makeModule_append: forall a b, getAllRules (makeModule (a++b))=getAllRules (makeModule a)++getAllRules (makeModule b).
Proof.
    induction a.
    + reflexivity.
    + intros.
      destruct a.
      - apply IHa.
      - unfold makeModule.
        simpl.
        simpl in IHa.
        rewrite IHa.
        reflexivity.
      - apply IHa.
Qed.

Hint Rewrite getAllRules_makeModule_append : kami_rewrite_db.

Lemma getAllRules_makeModule_MERegister: forall a b, getAllRules (makeModule ((MERegister a)::b))=getAllRules (makeModule b).
Proof.
    simpl.
    reflexivity.
Qed.

Hint Rewrite getAllRules_makeModule_MERegister : kami_rewrite_db.

Lemma getAllRules_makeModule_MERule: forall a b, getAllRules (makeModule ((MERule a)::b))=a::(getAllRules (makeModule b)).
Proof.
    simpl.
    reflexivity.
Qed.

Hint Rewrite getAllRules_makeModule_MERule : kami_rewrite_db.

Lemma getAllRules_makeModule_Registers: forall a, getAllRules (makeModule (Registers a))=[].
Proof.
    induction a.
    + reflexivity.
    + simpl.
      apply IHa.
Qed.

Hint Rewrite getAllRules_makeModule_Registers : kami_rewrite_db.

Hint Rewrite map_app : kami_rewrite_db.

