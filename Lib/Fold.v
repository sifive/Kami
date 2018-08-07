Require Import Recdef List Omega Div2.

Import ListNotations.

Set Implicit Arguments.
Set Asymmetric Patterns.

Local  Ltac name_term n t H := 
  assert (H: exists n', n' = t);
  try (exists t; reflexivity);
  destruct H as [n H]. 


Section UnApp.
  Context {A: Type}.

  Fixpoint unapp (n:nat)(m:list A) : list A * list A:=
    match n with
    | 0 => ([], m)
    | S n => match m with
             | nil => ([], [])
             | x::xs => let (m1, m2) := unapp n xs in
                        (x::m1, m2)
             end
    end.

  Lemma unapp_wont_expand: 
    forall n (m m1 m2: list A), 
      unapp n m = (m1, m2) -> 
      length m1 <= length m /\ length m2 <= length m. 
  Proof. 
    induction n as [| n]; intros * UA. 
    - simpl in UA. injection UA; intros M1 M2.
      subst m1 m2. auto with arith.
    - destruct m. 
      + simpl in UA.
        injection UA; intros M1 M2. 
        subst m1 m2. auto with arith. 
      + simpl in UA.
        name_term ua' (unapp n m) UA'.
        rewrite <- UA' in UA.
        destruct ua' as [m1' m2'].
        injection UA; intros M1 M2; subst m1 m2; clear UA.
        symmetry in UA'.
        apply IHn in UA'.
        simpl.
        omega. 
  Qed.        
  
  Lemma unapp_app: 
    forall n (m m1 m2: list A),
      (m1, m2) = unapp n m -> 
      m1 ++ m2 = m.
  Proof. 
    intros n m.
    revert n.
    induction m as [| x xs]; intros * UA.
    - destruct n as [| n'];
        simpl in UA;
        injection UA; intros M1 M2; subst m1 m2; clear UA;
          simpl; auto with arith.
    - destruct n as [| n'];
        simpl in UA.
      + injection UA; intros M1 M2; subst m1 m2; clear UA.
        reflexivity.
      + name_term ua' (unapp n' xs) UA'.  rewrite <- UA' in UA.
        destruct ua' as [m1' m2'].
        injection UA; intros M1 M2; subst m1 m2; clear UA.
        simpl. 
        apply IHxs in UA'.
        subst xs.
        reflexivity.
  Qed.

  Lemma unapp_reduce_m1: 
    forall n (m m1 m2: list A), 
      unapp n m = (m1, m2) -> 
      n < length m -> 
      length m1 < length m. 
  Proof. 
    intros n m. 
    revert n.
    induction m as [| x xs];
      intros * UA NltM. 
    - simpl in NltM. inversion NltM.
    - destruct n as [| n].
      + unfold unapp in UA.
        injection UA; intros M1 M2; subst m1 m2; clear UA.
        simpl. auto with arith.
      + simpl in UA.
        simpl in NltM. 
        apply lt_S_n in NltM.
        name_term ua' (unapp n xs) UA'.  rewrite <- UA' in UA.
        destruct ua' as [m1' m2'].
        injection UA; intros M1 M2; subst m1 m2; clear UA.
        symmetry in UA'.
        apply IHxs in UA'; auto.
        simpl.
        omega. 
  Qed. 



  Lemma unapp_reduce_m2: 
    forall n (m m1 m2: list A), 
      unapp n m = (m1, m2)-> 
      n > 0 ->
      length m > 0 -> 
      length m2 < length m. 
  Proof. 
    intros * UA Ngt0 Mgt0. 
    cut (length m1 > 0). 
    {
      intro H.
      symmetry in UA.
      apply unapp_app in UA.
      subst m.
      rewrite app_length in *.
      omega. 
    }
    destruct n as [| n']; destruct m as [| x xs].
    - inversion Ngt0.
    - inversion Ngt0.
    - simpl in Mgt0.
      inversion Mgt0.      
    - simpl in UA.
      name_term ua' (unapp n' xs) UA'.  rewrite <- UA' in UA.
      destruct ua' as [m1' m2'].
      injection UA; intros M1 M2; subst m1 m2; clear UA.
      simpl. auto with arith.
  Qed.

  Definition unapp_half(m: list A) :=
    let n := length m in 
    let n2 := div2 n in
    let n1 := n - n2 in
    unapp n1 m.

  Lemma unapp_half_app: 
    forall m m1 m2,
      (m1, m2) = unapp_half m -> 
      m1 ++ m2 = m.
  Proof. 
    induction m as [| x xs]; intros * SP. 
    inversion SP; auto.
    unfold unapp_half in SP.
    apply unapp_app in SP.
    auto.
  Qed.

  Lemma div2_SS: 
    forall n, div2 (S (S n)) > 0.
  Proof. 
    induction n; simpl; auto with arith.
  Qed. 


  
  Lemma unapp_half_nonnil_reduces: 
    forall m m1 m2, 
      unapp_half m = (m1,m2) -> 
      length m > S 0 -> 
      length m1 < length m /\ length m2 < length m.
  Proof. 
    intros * SP MgtO.
    unfold unapp_half in SP.
    name_term k (length m) LEN. 
    rewrite <- LEN in *.
    name_term n (k - div2 k) N1. 
    rewrite <- N1 in SP.     
    assert (DK: div2 k < k) 
      by (apply lt_div2; auto with arith).
    name_term d (div2 k) D. 
    rewrite <- D in *.
    destruct m as [| x1 xs]. 
    simpl in LEN. subst k. inversion DK.
    destruct xs as [| x2 xs].
    simpl in LEN. subst k. inversion MgtO. inversion H0.
    assert (DgtO: d > 0) by (subst k d; apply div2_SS). 
    assert (NltM: n < length (x1::x2::xs))
      by (simpl in *; omega). 
    subst k.
    split. 
    - apply unapp_reduce_m1 with (n:=n) (m2:=m2); auto.
    - assert (n > 0) by omega. 
      assert (length (x1::x2::xs) > 0) by (simpl; omega).
      apply unapp_reduce_m2 with (n:=n) (m1:=m1); auto.
  Qed. 


End UnApp.

Lemma unapp_map A B (f: A -> B): 
  forall n (m m1 m2: list A),
    (m1, m2) = unapp n m ->
    (map f m1, map f m2) = unapp n (map f m).
Proof.
    intros n m.
    revert n.
    induction m as [| x xs]; intros * UA.
    - destruct n as [| n'];
        simpl in UA;
        injection UA; intros M1 M2; subst m1 m2; clear UA;
          simpl; auto with arith.
    - destruct n as [| n'];
        simpl in UA.
      + injection UA; intros M1 M2; subst m1 m2; clear UA.
        reflexivity.
      + name_term ua' (unapp n' xs) UA'.  rewrite <- UA' in UA.
        destruct ua' as [m1' m2'].
        injection UA; intros M1 M2; subst m1 m2; clear UA.
        simpl. 
        apply IHxs in UA'.
        rewrite <- UA'.
        reflexivity.
Qed.

Lemma unapp_half_map A B (f: A -> B): 
  forall m m1 m2,
    (m1, m2) = unapp_half m ->
    (map f m1, map f m2) = unapp_half (map f m).
Proof.
  intros.
  eapply unapp_map with (f := f) in H.
  unfold unapp_half.
  rewrite map_length.
  auto.
Qed.

Section Folds.
  Variable A: Type.
  Variable f: A -> A -> A.
  Variable fComm: forall a b, f a b = f b a.
  Variable fAssoc: forall a b c, f (f a b) c = f a (f b c).
  Variable unit: A.
  Variable fUnit: forall x, f unit x = x.

  Lemma fold_right_inclusion:
    forall m1 m2 seed,
      fold_right f seed (m1 ++ m2) = fold_right f (fold_right f seed m2) m1.
  Proof.
    intro m1.
    induction m1 as [| x xs]; intros. 
    - reflexivity.
    - cut (fold_right f seed (xs ++ m2)
           = fold_right f (fold_right f seed m2) xs).
      intro C; simpl.
      now rewrite C.
      apply IHxs.
  Qed.

  (* h := fold_tree *)
  (* odot := f *)

  Function fold_tree (ls: list A) {measure length ls} :=
    match ls with
    | nil => unit
    | [x] => f x unit
    | [x;y] => f x y
    | _ => let (m1, m2) := unapp_half ls in
           f (fold_tree m1) (fold_tree m2)
    end.
  Proof.
    - abstract (intros;
                unfold unapp_half in teq2;
                symmetry in teq2;
                name_term len_x_n_l0 (length (x::y::a::l1)) LEN;
                rewrite <- LEN in *;
                simpl in LEN;
                assert (L0: len_x_n_l0 > 0) by omega;
                apply lt_div2 in L0;
                assert (len_x_n_l0 - div2 len_x_n_l0 > 0) by omega;
                symmetry in teq2;
                apply unapp_reduce_m2 in teq2; auto;
                simpl in teq2;
                [rewrite <- LEN in *;
                 apply teq2|
                 simpl;
                 auto with arith]).
    - abstract (intros;
                unfold unapp_half in teq2;
                apply unapp_reduce_m1 in teq2;
                [apply teq2|
                 clear teq2;
                 name_term len_x_n_l0 (length (x::y::a::l1)) LEN;
                 rewrite <- LEN in *;
                 simpl in LEN;
                 assert (L0: len_x_n_l0 > 0) by omega;
                 apply lt_div2 in L0;
                 assert (L1: len_x_n_l0 > 1) by omega;
                 rewrite LEN at 2;
                 simpl;
                 omega]).
  Defined.

  Lemma f_comm1 a b c:
    f a (f b c) = f b (f a c).
  Proof.
    rewrite <- fAssoc.
    rewrite <- fAssoc.
    assert (sth:f a b = f b a) by apply fComm; rewrite sth; rewrite <- sth.
    auto.
  Qed.

  Lemma f_comm2 a b c:
    f a (f b c) = f (f a b) c.
  Proof.
    rewrite <- fAssoc.
    reflexivity.
  Qed.

  Lemma fold_right_f_assoc:
    forall i m1 seed,
      f i (fold_right f seed m1) = fold_right f (f i seed) m1.
  Proof.
    intros i m1.
    assert (exists k, length m1 <= k) as [k K]
        by (exists (length m1); auto).
    revert i m1 K.
    induction k as [| k]; intros * K *.
    - assert (A1: length m1 = 0) by omega. 
      apply length_zero_iff_nil in A1.
      subst m1. 
      reflexivity.
    - destruct m1 as [| y ys].
      + reflexivity.
      + simpl in K.
        apply le_S_n in K.
        simpl.
        rewrite <- IHk; auto.
        apply f_comm1.
  Qed.

  Lemma fold_right_slideout:
    forall m seed,
      fold_right f seed m = f (fold_right f unit m) seed.
  Proof.
    induction m as [| x xs]; intros.
    - now simpl.
    - simpl.
      rewrite IHxs.
      destruct xs.
      apply f_comm2.
      apply f_comm2.
  Qed.

  Lemma fold_right_homomorphism:
    forall m1 m2,
      fold_right f unit (m1 ++ m2) = f (fold_right f unit m1) (fold_right f unit m2).
  Proof.
    intros *.
    name_term lhs (f (fold_right f unit m1) (fold_right f unit m2)) LHS.
    rewrite <- LHS.
    rewrite fold_right_inclusion.
    rewrite fold_right_slideout. 
    now subst lhs.
  Qed.

  Lemma fold_right_homomorphism_unapp:
    forall m m1 m2,
      (m1, m2) = unapp_half m ->
      fold_right f unit m = f (fold_right f unit m1) (fold_right f unit m2).
  Proof.
    intros.
    apply unapp_half_app in H.
    rewrite <- H.
    eapply fold_right_homomorphism.
  Qed.
  
  Theorem fold_right_fold_tree:
    forall m,
      fold_right f unit m = fold_tree m.
  Proof.
    intro m.
    assert (exists k, length m <= k) 
      as [k K] by (exists (length m); auto). 
    revert m K.
    induction k as [| k]; intros * K.
    - assert (A1: length m = 0) by omega. 
      apply length_zero_iff_nil in A1.
      now subst m.
    - destruct m as [| x1 xs]. now simpl.
      destruct xs as [| x2 xs]. now simpl.
      rewrite fold_tree_equation. 
      name_term tpl (unapp_half (x1::x2::xs)) Tpl;
        rewrite <- Tpl; destruct tpl as [m1 m2].
      simpl in K. 
      assert (K': S (length xs) <= k) by (rewrite le_S_n; auto); 
        clear K; rename K' into K.
      assert (length m1 <= length (x2::xs) 
              /\ length m2 <= length (x2::xs))
        as [A1 A2]. {
        symmetry in Tpl.
        apply unapp_half_nonnil_reduces in Tpl; auto.
        2: simpl; omega. 
        simpl in *.
        omega. 
      }
      simpl in A1, A2.
      assert (A3: length m1 <= k) by omega; clear A1.
      assert (A4: length m2 <= k) by omega; clear A2. 
      rewrite <- (IHk m1 A3); rewrite <- (IHk m2 A4).
      rewrite fold_right_homomorphism_unapp with (m:=(x1::x2::xs)) (m1 := m1) (m2 := m2); destruct xs; auto.
      unfold unapp_half in Tpl; simpl in *.
      inversion Tpl; clear Tpl; subst.
      simpl.
      rewrite (fComm x1 unit), (fComm x2 unit).
      rewrite ?fUnit.
      auto.
  Qed.

  Theorem fold_left_fold_right:
    forall m seed,
      fold_left f m seed = fold_right f seed m.
  Proof.
    induction m; simpl; auto; intros.
    rewrite IHm.
    rewrite fold_right_f_assoc.
    rewrite fComm.
    auto.
  Qed.


  Theorem fold_left_fold_tree:
    forall m,
      fold_left f m unit = fold_tree m.
  Proof.
    intros.
    rewrite fold_left_fold_right.
    apply fold_right_fold_tree.
  Qed.

End Folds.

Section FoldWhich.
  Variable A: Type.
  Variable decA: forall a b: A, {a = b} + {a <> b}.
  Variable which: A -> A -> bool.
  Variable whichRefl: forall a, which a a = true.
  Variable whichSym: forall x y, x = y \/ which x y = negb (which y x).
  Variable whichTrans: forall a b c, which a b = which b c -> which a c = which a b.
  
  Definition pick x y := if which x y then x else y.

  Local Lemma pickComm: forall a b, pick a b = pick b a.
  Proof.
    unfold pick; intros.
    specialize (whichSym a b).
    destruct whichSym; subst; auto.
    rewrite H.
    destruct (which b a); auto.
  Qed.

  Local Lemma pickAssoc: forall a b c, pick (pick a b) c = pick a (pick b c).
  Proof.
    unfold pick; intros.
    case_eq (which b c); case_eq (which a b); intros; auto.
    - erewrite whichTrans; eauto.
      rewrite H; auto.
    - rewrite H0; auto.
    - rewrite H0.
      erewrite whichTrans; eauto.
      rewrite H; auto.
  Qed.
      
  Variable unit: A.
  Variable whichUnit: forall x, x <> unit -> which unit x = false.
  
  Local Lemma pickUnit: forall x, pick unit x = x.
  Proof.
    unfold pick; intros.
    destruct (decA unit x); subst.
    destruct (which x x); auto.
    assert (sth: x <> unit) by (intro; subst; tauto).
    specialize (whichUnit sth).
    rewrite whichUnit; auto.
  Qed.

  Local Lemma pickUnit_both: forall x y, pick x y = unit -> x = unit /\ y = unit.
  Proof.
    intros.
    unfold pick in *.
    case_eq (which x y); intros sth; rewrite sth in *; subst.
    - split; auto.
      destruct (decA y unit); auto.
      specialize (whichUnit n).
      congruence.
    - split; auto.
      specialize (whichSym x unit).
      destruct whichSym; auto.
      rewrite H in sth.
      rewrite Bool.negb_false_iff in sth.
      rewrite sth in *; simpl in *.
      destruct (decA x unit); auto.
      specialize (whichUnit n).
      congruence.
  Qed.

  Lemma fold_right_unit ls:
    fold_right pick unit ls = unit -> forall x, In x ls -> x = unit.
  Proof.
    induction ls; simpl; auto; intros.
    - tauto.
    - destruct H0; subst.
      apply pickUnit_both in H.
      destruct H as [s1 s2]; subst; auto.
      apply pickUnit_both in H.
      destruct H as [s3 s4].
      eapply IHls; eauto.
  Qed.

  Theorem which1_fold_right:
    forall ls,
      forall i, i < length ls -> which (fold_right pick unit ls) (nth i ls unit) = true.
  Proof.
    induction ls; simpl; auto; intros.
    - Omega.omega.
    - unfold pick in *.
      remember (fold_right (fun x y => if which x y then x else y) unit ls) as sth.
      destruct i; simpl in *.
      + case_eq (which a sth); intros sth2.
        * subst; eapply whichRefl; eauto.
        * destruct (decA sth a); simpl in *.
          -- subst; rewrite whichRefl; auto.
          -- specialize (whichSym sth a).
             destruct whichSym; [tauto|].
             rewrite H0 in *.
             rewrite Bool.negb_true_iff.
             auto.
      + case_eq (which a sth); intros sth2.
        * specialize (IHls i ltac:(Omega.omega)).
          rewrite <- IHls in sth2.
          pose proof (@whichTrans _ _ _ sth2).
          congruence.
        * specialize (IHls i ltac:(Omega.omega)).
          auto.
  Qed.

  Theorem which1_fold_tree:
    forall ls,
      forall i, i < length ls -> which (fold_tree pick unit ls) (nth i ls unit) = true.
  Proof.
    intros.
    rewrite <- fold_right_fold_tree; auto; intros.
    - eapply which1_fold_right; eauto.
    - apply pickComm.
    - apply pickAssoc.
    - apply pickUnit.
  Qed.

  Theorem which1_fold_left:
    forall ls,
      forall i, i < length ls -> which (fold_left pick ls unit) (nth i ls unit) = true.
  Proof.
    intros.
    rewrite fold_left_fold_right; auto; intros.
    - eapply which1_fold_right; eauto.
    - apply pickComm.
    - apply pickAssoc.
  Qed.

  Theorem which2_fold_right:
    forall ls,
      fold_right pick unit ls <> unit ->
      exists n, n < length ls /\ nth n ls unit = fold_right pick unit ls.
  Proof.
    induction ls; simpl; auto; intros.
    - tauto.
    - destruct (decA (fold_right pick unit ls) unit); simpl in *.
      + rewrite e in *.
        rewrite pickComm in *.
        rewrite pickUnit in *; subst.
        exists 0; repeat split; auto; try Omega.omega; intros.
      + specialize (IHls n).
        destruct IHls as [j [jLen cond1]].
        subst.
        rewrite <- cond1 in *.
        unfold pick in *.
        case_eq (which a (nth j ls unit)); intros sth; rewrite sth in *; subst.
        * exists 0; repeat split; auto; try Omega.omega; intros.
        * exists (S j); repeat split; auto; try Omega.omega; intros.
  Qed.

  Theorem which2_fold_tree:
    forall ls,
      fold_tree pick unit ls <> unit ->
      exists n, n < length ls /\ nth n ls unit = fold_tree pick unit ls.
  Proof.
    intros.
    rewrite <- fold_right_fold_tree in *; auto; intros.
    - eapply which2_fold_right; eauto; auto.
    - apply pickComm.
    - apply pickAssoc.
    - apply pickUnit.
    - apply pickComm.
    - apply pickAssoc.
    - apply pickUnit.
  Qed.

  Theorem which2_fold_left:
    forall ls,
      fold_left pick ls unit <> unit ->
      exists n, n < length ls /\ nth n ls unit = fold_left pick ls unit.
  Proof.
    intros.
    rewrite fold_left_fold_right in *; auto; intros.
    - eapply which2_fold_right; eauto; auto.
    - apply pickComm.
    - apply pickAssoc.
    - apply pickComm.
    - apply pickAssoc.
  Qed.

   Theorem whichNonUnit_fold_right:
    forall ls val,
      val = fold_right pick unit ls ->
      val <> unit ->
      exists n, n < length ls /\ nth n ls unit = val /\ forall i, i < length ls -> i <> n -> which val (nth i ls unit) = true.
  Proof.
    induction ls; simpl; auto; intros.
    - tauto.
    - destruct (decA (fold_right pick unit ls) unit); simpl in *.
      + rewrite e in *.
        rewrite pickComm in *.
        rewrite pickUnit in *; subst.
        exists 0; repeat split; auto; try Omega.omega; intros.
        destruct i; auto.
        pose proof (fold_right_unit _ e) as sth.
        specialize (sth (nth i ls unit) (nth_In (n := i) ls unit ltac:(Omega.omega))).
        rewrite sth.
        specialize (whichSym a unit).
        destruct whichSym as [whichSym0 | whichSym0]; auto.
        rewrite whichSym0.
        rewrite Bool.negb_true_iff.
        auto.
      + specialize (IHls _ eq_refl n).
        destruct IHls as [j [jLen [cond1 cond2]]].
        subst.
        rewrite <- cond1 in *.
        unfold pick in *.
        case_eq (which a (nth j ls unit)); intros sth; rewrite sth in *; subst.
        * exists 0; repeat split; auto; try Omega.omega; intros.
          destruct i; auto.
          destruct (Nat.eq_dec i j); subst; [auto|].
          specialize (cond2 i ltac:(Omega.omega) n0).
          rewrite <- cond2 in sth.
          pose proof (whichTrans sth).
          congruence.
        * exists (S j); repeat split; auto; try Omega.omega; intros.
          destruct i; auto.
          -- specialize (whichSym (nth j ls unit) a).
             destruct whichSym as [whichSym0 | whichSym0]; auto.
             ++ rewrite whichSym0 in *.
                eapply whichRefl; eauto.
             ++ rewrite whichSym0.
                rewrite Bool.negb_true_iff; auto.
          -- eapply cond2; eauto; Omega.omega.
  Qed.

  Theorem whichNonUnit_fold_left:
    forall ls val,
      val = fold_left pick ls unit ->
      val <> unit ->
      exists n, n < length ls /\ nth n ls unit = val /\ forall i, i < length ls -> i <> n -> which val (nth i ls unit) = true.
  Proof.
    intros.
    rewrite fold_left_fold_right in H; auto; intros.
    - eapply whichNonUnit_fold_right; eauto.
    - apply pickComm.
    - apply pickAssoc.
  Qed.

  Theorem whichNonUnit_fold_tree:
    forall ls val,
      val = fold_tree pick unit ls ->
      val <> unit ->
      exists n, n < length ls /\ nth n ls unit = val /\ forall i, i < length ls -> i <> n -> which val (nth i ls unit) = true.
  Proof.
    intros.
    rewrite <- fold_right_fold_tree in H; auto; intros.
    - eapply whichNonUnit_fold_right; eauto.
    - apply pickComm.
    - apply pickAssoc.
    - apply pickUnit.
  Qed.
End FoldWhich.
