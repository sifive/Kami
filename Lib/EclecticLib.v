Require Import String Coq.Lists.List Omega Fin.

Import ListNotations.

Set Implicit Arguments.
Set Asymmetric Patterns.


Section fold_left_right.
  Variable A B: Type.
  Variable f: A -> B -> A.
  Variable f_comm: forall x i j, f (f x i) j = f (f x j) i.

  Lemma fold_left_right_comm ls:
    forall init,
      fold_left f ls init = fold_right (fun x acc => f acc x) init ls.
  Proof.
    induction ls; simpl; auto; intros.
    rewrite <- IHls; simpl.
    clear IHls.
    generalize init; clear init.
    induction ls; simpl; auto; intros.
    rewrite <- IHls.
    rewrite f_comm.
    auto.
  Qed.
End fold_left_right.

Section fold_left_map.
  Variable A B C: Type.
  Variable f: A -> B -> A.
  Variable g: C -> B.
  
  Lemma fold_left_dist_map ls:
    forall init,
      fold_left f (map g ls) init = fold_left (fun acc x => f acc (g x)) ls init.
  Proof.
    induction ls; simpl; auto.
  Qed.
End fold_left_map.

Fixpoint range b t :=
  match t with
  | S p => (match Nat.eq_dec b p with
            | left _ => nil
            | right _ => range b p
            end ++ p :: nil)%list
  | 0 => nil
  end.

Infix "upto" := range (at level 15, no associativity).

Section map_fold_eq.
  Variable A: Type.
  Variable f: A -> A.

  Fixpoint zeroToN n :=
    match n with
    | 0 => nil
    | S m => zeroToN m ++ m :: nil
    end.

  Lemma zeroToN_upto n: zeroToN n = 0 upto n.
  Proof.
    induction n; simpl; auto.
    rewrite IHn.
    f_equal.
    destruct n; auto.
  Qed.
    
  Fixpoint transform_nth_left ls i :=
    match ls with
    | nil => nil
    | x :: xs => match i with
                 | 0 => f x :: xs
                 | S m => x :: transform_nth_left xs m
                 end
    end.

  Lemma transform_nth_left_length' ls:
    forall i,
      length (transform_nth_left ls i) = length ls.
  Proof.
    induction ls; simpl; auto; intros.
    destruct i; simpl; auto; intros.
  Qed.

  Lemma transform_nth_left_length ns:
    forall ls,
      length (fold_left transform_nth_left ns ls) = length ls.
  Proof.
    induction ns; simpl; auto; intros.
    rewrite IHns.
    apply transform_nth_left_length'.
  Qed.

  Lemma transform_nth_tail a ls:
    forall i,
      transform_nth_left (a :: ls) (S i) = a :: transform_nth_left ls i.
  Proof.
    induction ls; destruct i; simpl; auto.
  Qed.

  Lemma zeroToSN n:
    zeroToN n ++ [n] = 0 :: map S (zeroToN n).
  Proof.
    induction n; simpl; auto.
    rewrite map_app.
    rewrite app_comm_cons.
    rewrite <- IHn.
    auto.
  Qed.

                   
  Lemma map_fold_left_eq' ls: map f ls = fold_left transform_nth_left (zeroToN (length ls)) ls.
  Proof.
    induction ls; simpl; auto.
    rewrite IHls.
    rewrite zeroToSN; simpl.
    rewrite fold_left_dist_map.
    clear IHls.
    remember (f a) as x.
    remember (zeroToN (length ls)) as ys.
    clear Heqx a Heqys.
    generalize ls x; clear x ls.
    induction ys; simpl; auto.
  Qed.

  Lemma map_fold_left_eq ls: map f ls = fold_left transform_nth_left (0 upto (length ls)) ls.
  Proof.
    rewrite <- zeroToN_upto.
    apply map_fold_left_eq'.
  Qed.
End map_fold_eq.

Section map_fold_eq_gen.
  Variable A: Type.
  Variable f: A -> nat -> A.

  Fixpoint transform_nth_left_gen ls i :=
    match ls with
    | nil => nil
    | x :: xs => match i with
                 | 0 => f x i :: xs
                 | S m => x :: transform_nth_left_gen xs m
                 end
    end.
End map_fold_eq_gen.
    

Section map_fold_eq'.
  Variable A: Type.
  Variable f: A -> A.

  Fixpoint transform_nth_right i ls :=
    match ls with
    | nil => nil
    | x :: xs => match i with
                 | 0 => f x :: xs
                 | S m => x :: transform_nth_right m xs
                 end
    end.

  Lemma transform_left_right_eq x: forall y, transform_nth_left f x y = transform_nth_right y x.
  Proof.
    induction x; destruct y; simpl; auto; intros.
    f_equal; auto.
  Qed.

  Lemma transform_nth_left_comm ls:
    forall i j,
      transform_nth_left f (transform_nth_left f ls i) j = transform_nth_left f (transform_nth_left f ls j) i.
  Proof.
    induction ls; destruct i, j; simpl; auto; intros; f_equal.
    auto.
  Qed.
    
  Lemma transform_nth_right_comm ls:
    forall i j,
      transform_nth_right j (transform_nth_right i ls) = transform_nth_right i (transform_nth_right j ls).
  Proof.
    intros.
    rewrite <- ?transform_left_right_eq.
    apply transform_nth_left_comm.
  Qed.
      
  
  Lemma map_fold_right_eq' ls: map f ls = fold_right transform_nth_right ls (zeroToN (length ls)).
  Proof.
    rewrite <- fold_left_right_comm by apply transform_nth_right_comm.
    rewrite map_fold_left_eq'.
    remember (zeroToN (length ls)) as xs.
    clear Heqxs.
    generalize ls; clear ls.
    induction xs; simpl; auto; intros.
    rewrite IHxs.
    rewrite transform_left_right_eq.
    auto.
  Qed.

  Lemma map_fold_right_eq ls: map f ls = fold_right transform_nth_right ls (0 upto (length ls)).
  Proof.
    rewrite <- zeroToN_upto.
    eapply map_fold_right_eq'.
  Qed.
End map_fold_eq'.



Fixpoint getFins n :=
  match n return list (Fin.t n) with
  | 0 => nil
  | S m => Fin.F1 :: map Fin.FS (getFins m)
  end.

Definition mapOrFins n (x: Fin.t n) := fold_left (fun a b => x = b \/ a) (getFins n) False.

Lemma fold_left_or_init: forall A (f: A -> Prop) ls (P: Prop), P -> fold_left (fun a b => f b \/ a) ls P.
Proof.
  induction ls; simpl; intros; auto.
Qed.

Lemma fold_left_or_impl: forall A (f: A -> Prop) ls (g: A -> Prop)
                                (P Q: Prop), (P -> Q) -> (forall a, f a -> g a) ->
                                             fold_left (fun a b => f b \/ a) ls P ->
                                             fold_left (fun a b => g b \/ a) ls Q.
Proof.
  induction ls; simpl; intros; auto.
  eapply IHls with (P := f a \/ P) (Q := g a \/ Q); try tauto.
  specialize (H0 a).
  tauto.
Qed.

Lemma fold_left_map A B C (f: A -> B) (g: C -> B -> C) ls:
  forall init,
    fold_left g (map f ls) init =
    fold_left (fun c a => g c (f a)) ls init.
Proof.
  induction ls; simpl; auto.
Qed.

Lemma mapOrFins_true n: forall (x: Fin.t n), mapOrFins x.
Proof.
  induction x; unfold mapOrFins in *; simpl; intros.
  - apply fold_left_or_init; auto.
  - rewrite fold_left_map.
    eapply (@fold_left_or_impl _ (fun b => x = b) (getFins n) _ False (Fin.FS x = Fin.F1 \/ False)); try tauto; congruence.
Qed.



Lemma list_split A B C (f: A -> C) (g: B -> C): forall l l1 l2,
    map f l = map g l1 ++ map g l2 ->
    exists l1' l2',
      l = l1' ++ l2' /\
      map f l1' = map g l1 /\
      map f l2' = map g l2.
Proof.
  induction l; simpl; auto; intros.
  - apply eq_sym in H.
    apply app_eq_nil in H; destruct H as [s1 s2].
    apply map_eq_nil in s1.
    apply map_eq_nil in s2.
    subst.
    exists nil, nil; simpl; auto.
  - destruct l1; simpl in *.
    + destruct l2; simpl in *.
      * discriminate.
      * inversion H; subst; clear H.
        specialize (IHl nil l2 H2).
        destruct IHl as [l1' [l2' [s1 [s2 s3]]]].
        simpl in *.
        apply map_eq_nil in s2; subst; simpl in *.
        exists nil, (a :: l2'); simpl; auto.
    + inversion H; subst; clear H.
      specialize (IHl _ _ H2).
      destruct IHl as [l1' [l2' [s1 [s2 s3]]]].
      exists (a :: l1'), l2'; simpl; repeat split; auto.
      * f_equal; auto.
      * f_equal; auto.
Qed.

Lemma nth_error_len A B i:
  forall (la: list A) (lb: list B) a,
    nth_error la i = None ->
    nth_error lb i = Some a ->
    length la = length lb ->
    False.
Proof.
  induction i; destruct la; destruct lb; simpl; auto; intros; try congruence.
  inversion H.
  eapply IHi; eauto.
Qed.

(* fold_right *)
Section list.
  Variable A: Type.
  Variable fn: A -> bool.

  Fixpoint remove_fn (ls: list A) :=
  match ls with
  | nil => nil
  | x :: xs => if fn x then remove_fn xs else x :: remove_fn xs
  end.

  Definition SubList (l1 l2: list A) :=
    forall x, In x l1 -> In x l2.

  Lemma SubList_app_l (l1 l2 ls: list A): SubList (l1 ++ l2) ls -> SubList l1 ls /\ SubList l2 ls.
  Proof.
    firstorder.
  Qed.

  Lemma SubList_app_r (ls l1 l2: list A): SubList ls l1 -> SubList ls (l1 ++ l2).
  Proof.
    firstorder.
  Qed.

  Lemma SubList_transitive (l1 l2 l3: list A): SubList l1 l2 -> SubList l2 l3 ->
                                               SubList l1 l3.
  Proof.
    firstorder.
  Qed.

  Lemma SubList_cons a (l ls: list A): SubList (a :: l) ls -> In a ls /\ SubList l ls.
  Proof.
    firstorder.
  Qed.

  Definition SameList (l1 l2: list A) := SubList l1 l2 /\ SubList l2 l1.

  Definition DisjList (l1 l2: list A) :=
    forall x, ~ In x l1 \/ ~ In x l2.

  Lemma remove_fn_sublist (ls: list A):
    SubList (remove_fn ls) ls.
  Proof.
    induction ls; unfold SubList; simpl; auto; intros.
    destruct (fn a); simpl in *; auto.
    destruct H; auto.
  Qed.

  Variable decA: forall x y: A, {x = y} + {x <> y}.
  Fixpoint subtract_list l1 l2 :=
    match l2 with
    | nil => l1
    | x :: xs => subtract_list (remove decA x l1) xs
    end.
  Lemma subtract_list_nil_l (l: list A): subtract_list l [] = l.
  Proof.
    reflexivity.
  Qed.

  Lemma subtract_list_nil_r (l: list A): subtract_list [] l = [].
  Proof.
    induction l; auto.
  Qed.
End list.

Lemma SubList_map A B (f: A -> B)
      l1 l2:
  SubList l1 l2 ->
  SubList (map f l1) (map f l2).
Proof.
  unfold SubList; intros.
  rewrite in_map_iff in *.
  repeat match goal with
         | H: exists x, _ |- _ => destruct H
         | H: _ /\ _ |- _ => destruct H
         end; subst.
  apply H in H1.
  firstorder fail.
Qed.

Lemma SubList_map2 A B C (f: A -> C) (g: B -> C)
      l1 l2 l3: SubList (map f l1) (map g l2) ->
                SubList l2 l3 ->
                SubList (map f l1) (map g l3).
Proof.
  intros.
  unfold SubList in *; intros.
  specialize (H x H1).
  rewrite in_map_iff in H, H1.
  repeat match goal with
         | H: exists x, _ |- _ => destruct H
         | H: _ /\ _ |- _ => destruct H
         end; subst.
  specialize (H0 x1 H3).
  rewrite in_map_iff.
  exists x1; auto.
Qed.

Section Filter.
  Variable A: Type.
  Variable f g: A -> bool.
  
  Lemma filter_complement_same (ls: list A):
    SameList (filter f ls ++ filter (fun x => negb (f x)) ls) ls.
  Proof.
    induction ls; unfold SameList in *; simpl; auto; intros.
    - unfold SubList; auto.
    - destruct IHls.
      split; destruct (f a); unfold SubList in *.
      + firstorder fail.
      + intros.
        rewrite in_app_iff in H1; simpl in *.
        clear - H H1.
        firstorder.
      + firstorder fail.
      + intros.
        specialize (H0 x).
        rewrite in_app_iff in *; simpl in *.
        clear - H0 H1.
        firstorder fail.
  Qed.

  Variable B: Type.
  Variable h: A -> B.
  Lemma filter_complement_map_same (ls: list A):
    SameList (map h (filter f ls) ++ map h (filter (fun x => negb (f x)) ls)) (map h ls).
  Proof.
    induction ls; unfold SameList in *; simpl; auto; intros.
    - unfold SubList; auto.
    - destruct IHls.
      split; destruct (f a); unfold SubList in *.
      + firstorder fail.
      + intros.
        rewrite in_app_iff in H1; simpl in *.
        clear - H H1.
        firstorder.
      + firstorder fail.
      + intros.
        specialize (H0 x).
        rewrite in_app_iff in *; simpl in *.
        clear - H0 H1.
        firstorder fail.
  Qed.

  Variable gImpF: forall a, g a = true -> f a = true.

  Lemma SubList_strengthen_filter (l ls: list A):
    SubList l (filter g ls) ->
    SubList l (filter f ls).
  Proof.
    unfold SubList; intros.
    specialize (H _ H0).
    rewrite filter_In in *.
    destruct H.
    apply gImpF in H1.
    auto.
  Qed.
End Filter.

Definition getBool A B (x: {A} + {B}) : bool :=
  match x with
  | left _ => true
  | right _ => false
  end.

Section SubList_filter.
  Variable A B: Type.
  Variable f: A -> B.
  Variable Bdec: forall b1 b2: B, {b1 = b2} + {b1 <> b2}.

  Lemma SubList_filter_map: forall l1 l2 l3,
      SubList l1 l2 ->
      SubList (map f l1) l3 ->
      SubList l1 (filter (fun x => getBool (in_dec Bdec (f x) l3)) l2).
  Proof.
    unfold SubList; intros.
    rewrite filter_In.
    specialize (H _ H1).
    split; [auto | ].
    unfold getBool.
    destruct (in_dec Bdec (f x) l3); [auto | ].
    apply in_map with (f := f) in H1.
    specialize (H0 (f x) H1).
    tauto.
  Qed.

  Lemma SubList_filter_Disj: forall l1 l2 l3 l4,
      SubList l1 l2 ->
      SubList (map f l1) l3 ->
      DisjList l3 l4 ->
      SubList l1 (filter (fun x => negb (getBool (in_dec Bdec (f x) l4))) l2).
  Proof.
    unfold SubList; intros.
    rewrite filter_In.
    specialize (H _ H2).
    split; [auto | ].
    unfold getBool.
    destruct (in_dec Bdec (f x) l4); [|auto].
    apply in_map with (f := f) in H2.
    specialize (H0 (f x) H2).
    firstorder fail.
  Qed.
    
End SubList_filter.

Lemma filter_false: forall A (l: list A), filter (fun _ => false) l = nil.
Proof.
  induction l; simpl; auto.
Qed.

Section filter_app.
  Variable A: Type.
  Variable f: A -> bool.

  Lemma filter_app: forall l1 l2, filter f (l1 ++ l2) = filter f l1 ++ filter f l2.
  Proof.
    induction l1; simpl; auto; intros.
    destruct (f a); simpl; f_equal; firstorder fail.
  Qed.
End filter_app.

Lemma In_nil A l: (forall a: A, ~ In a l) -> l = nil.
Proof.
  induction l; auto; intros.
  exfalso.
  simpl in H.
  specialize (H a).
  assert (a <> a /\ ~ In a l) by firstorder.
  firstorder.
Qed.

Section filterSmaller.
  Variable A: Type.
  Variable g: A -> bool.
  
  Lemma filter_smaller: forall l l1, filter g l = l1 ++ l -> l1 = nil.
  Proof.
    induction l; simpl; intros.
    - rewrite app_nil_r in *; subst; auto.
    - destruct (g a), l1; simpl in *; auto.
      + inversion H; subst; clear H.
        specialize (IHl (l1 ++ [a0])).
        rewrite <- app_assoc in IHl.
        specialize (IHl H2).
        apply app_eq_nil in IHl.
        destruct IHl.
        discriminate.
      + specialize (IHl ((a0 :: l1) ++ [a])).
        rewrite <- app_assoc in IHl.
        specialize (IHl H).
        apply app_eq_nil in IHl.
        destruct IHl.
        discriminate.
  Qed.

  Variable h: A -> bool.
  Variable hKeepsMore: forall a, g a = true -> h a = true.
  Lemma filter_strengthen_same l:
    filter g l = l ->
    filter h l = l.
  Proof.
    induction l; simpl; auto; intros.
    specialize (@hKeepsMore a).
    destruct (g a), (h a); inversion H.
    - specialize (IHl H1).
      congruence.
    - specialize (@hKeepsMore eq_refl); discriminate.
    - assert (sth: filter g l = [a] ++ l) by (apply H).
      apply filter_smaller in sth.
      discriminate.
    - assert (sth: filter g l = [a] ++ l) by (apply H).
      apply filter_smaller in sth.
      discriminate.
  Qed.
End filterSmaller.

Section filter_nil.
  Variable A: Type.
  Variable f: A -> bool.
  
  Lemma filter_nil1: forall l, filter f l = nil -> forall a, In a l -> f a = false.
  Proof.
    induction l.
    - simpl; auto; intros; try tauto.
    - intros.
      simpl in *.
      case_eq (f a); intros.
      + rewrite H1 in *; simpl in *; discriminate.
      + destruct H0; [subst; auto | ].
        rewrite H1 in *; simpl in *.
        eapply IHl; eauto.
  Qed.

  Lemma filter_nil2: forall l, (forall a, In a l -> f a = false) -> filter f l = nil.
  Proof.
    induction l; auto.
    intros.
    simpl.
    assert (sth: forall a, In a l -> f a = false) by firstorder.
    specialize (IHl sth).
    case_eq (f a); intros; auto.
    specialize (H a (or_introl eq_refl)); auto.
    rewrite H in *; discriminate.
  Qed.
End filter_nil.

Definition key_not_In A B key (ls: list (A * B)) := forall v, ~ In (key, v) ls.

Section DisjKey.
  Variable A B: Type.
  Section l1_l2.
    Variable l1 l2: list (A * B).

    Definition DisjKey :=
      forall k, ~ In k (map fst l1) \/ ~ In k (map fst l2).
    
    Variable Adec: forall a1 a2: A, {a1 = a2} + {a1 <> a2}.
    
    Definition DisjKeyWeak :=
      forall k, In k (map fst l1) -> In k (map fst l2) -> False.

    Lemma Demorgans (P Q: A -> Prop) (Pdec: forall a, {P a} + {~ P a})
          (Qdec: forall a, {Q a} + {~ Q a}):
      (forall a, ~ P a \/ ~ Q a) <-> (forall a, P a -> Q a -> False).
    Proof.
      split; intros; firstorder fail.
    Qed.

    Lemma DisjKeyWeak_same:
      DisjKey <-> DisjKeyWeak.
    Proof.
      unfold DisjKeyWeak.
      apply Demorgans;
        intros; apply (in_dec Adec); auto.
    Qed.
  End l1_l2.

  Lemma DisjKey_nil_r: forall l, DisjKey l nil.
  Proof.
    unfold DisjKey; simpl; intros.
    tauto.
  Qed.

  Lemma DisjKey_nil_l: forall l, DisjKey nil l.
  Proof.
    unfold DisjKey; simpl; intros.
    tauto.
  Qed.
End DisjKey.

Section FilterMap.
  Variable A B C: Type.
  Variable Adec: forall a1 a2: A, {a1 = a2} + {a1 <> a2}.
  Variable f: B -> C.

  Lemma filter_In_map_same l:
    filter (fun x => getBool (in_dec Adec (fst x) (map fst l)))
           (map (fun x => (fst x, f (snd x))) l) = map (fun x => (fst x, f (snd x))) l.
  Proof.
    induction l; simpl; auto.
    destruct (Adec (fst a) (fst a)); simpl; [f_equal |exfalso; tauto].
    match goal with
    | H: filter ?g ?l = ?l |- filter ?h ?l = ?l =>
      apply (filter_strengthen_same g h); auto
    end.
    intros.
    destruct (Adec (fst a) (fst a0)); auto.
    destruct (in_dec Adec (fst a0) (map fst l)); auto.
  Qed.

  Lemma filter_DisjKeys l1:
    forall l2,
      DisjKey l1 l2 ->
      filter (fun x : A * C => getBool (in_dec Adec (fst x) (map fst l1)))
             (map (fun x : A * B => (fst x, f (snd x))) l2) = nil.
  Proof.
    induction l2; intros; auto.
    assert (sth: DisjKey l1 l2).
    { unfold DisjKey; intros.
      specialize (H k).
      destruct H; firstorder fail.
    }
    specialize (IHl2 sth).
    simpl.
    rewrite IHl2.
    destruct (in_dec Adec (fst a) (map fst l1)); simpl; auto.
    rewrite DisjKeyWeak_same in H; auto.
    unfold DisjKeyWeak in *.
    specialize (H (fst a) i (or_introl eq_refl)).
    tauto.
  Qed.

  Lemma filter_DisjKeys_negb l1:
    forall l2,
      DisjKey l1 l2 ->
      filter (fun x : A * C => negb (getBool (in_dec Adec (fst x) (map fst l1))))
             (map (fun x : A * B => (fst x, f (snd x))) l2) =
      (map (fun x => (fst x, f (snd x))) l2).
  Proof.
    induction l2; intros; auto.
    assert (sth: DisjKey l1 l2).
    { unfold DisjKey, key_not_In in *; intros.
      specialize (H k).
      destruct H; firstorder fail.
    }
    specialize (IHl2 sth).
    simpl.
    rewrite IHl2.
    destruct (in_dec Adec (fst a) (map fst l1)); simpl; auto.
    rewrite DisjKeyWeak_same in H; auto.
    unfold DisjKeyWeak in *.
    specialize (H _ i (or_introl eq_refl)).
    tauto.
  Qed.
    
  Lemma filter_negb l1:
      filter (fun x : A * C => negb (getBool (in_dec Adec (fst x) (map fst l1))))
             (map (fun x : A * B => (fst x, f (snd x))) l1) = nil.
  Proof.
    induction l1; simpl; intros; auto.
    destruct (Adec (fst a) (fst a)); [simpl | exfalso; tauto].
    pose proof (filter_nil1 _ _ IHl1) as sth.
    simpl in sth.
    apply filter_nil2; intros.
    destruct (Adec (fst a) (fst a0)); auto.
    destruct (in_dec Adec (fst a0) (map fst l1)); auto.
    exfalso.
    rewrite in_map_iff in *.
    destruct H as [? [? ?]].
    assert (exists x, fst x = fst a0 /\ In x l1).
    exists x; split; auto.
    destruct x, a0; auto; simpl in *.
    inversion H; auto.
    tauto.
  Qed.
    
  Lemma filter_In_map_prod (l1: list (A * B)):
      forall l2,
        DisjKey l1 l2 ->
        filter (fun x => getBool (in_dec Adec (fst x) (map fst l1)))
               (map (fun x => (fst x, f (snd x))) (l1 ++ l2)) =
        map (fun x => (fst x, f (snd x))) l1.
  Proof.
    intros.
    rewrite map_app, filter_app.
    rewrite filter_DisjKeys with (l2 := l2); auto.
    rewrite app_nil_r.
    apply filter_In_map_same.
  Qed.
End FilterMap.

Section FilterMap2.
  Variable A B: Type.
  Variable f: A -> B.
  Variable g: B -> bool.

  Lemma filter_map_simple ls: filter g (map f ls) = map f (filter (fun x => g (f x)) ls).
  Proof.
    induction ls; simpl; auto.
    case_eq (g (f a)); intros; simpl; f_equal; auto.
  Qed.
End FilterMap2.

Lemma SubList_filter A (l1 l2: list A) (g: A -> bool):
  SubList l1 l2 ->
  SubList (filter g l1) (filter g l2).
Proof.
  unfold SameList, SubList; simpl; intros.
  intros; rewrite filter_In in *.
  destruct H0; split; auto.
Qed.  

Lemma SameList_filter A (l1 l2: list A) (g: A -> bool):
  SameList l1 l2 ->
  SameList (filter g l1) (filter g l2).
Proof.
  unfold SameList, SubList; simpl; intros.
  destruct H; split; intros; rewrite filter_In in *; destruct H1; split; auto.
Qed.

Fixpoint mapProp A (P: A -> Prop) ls :=
  match ls with
  | nil => True
  | x :: xs => P x /\ mapProp P xs
  end.

Fixpoint mapProp2 A B (P: A -> B -> Prop) (ls: list (A * B)) :=
  match ls with
  | nil => True
  | (x, y) :: ps => P x y /\ mapProp2 P ps
  end.
  
Fixpoint mapProp_len A B (P: A -> B -> Prop) (la: list A) (lb: list B) :=
  match la, lb with
  | (x :: xs), (y :: ys) => P x y /\ mapProp_len P xs ys
  | _, _ => True
  end.

Lemma mapProp_len_conj A B (P Q: A -> B -> Prop):
  forall (la: list A) (lb: list B),
    mapProp_len (fun a b => P a b /\ Q a b) la lb <->
    mapProp_len P la lb /\ mapProp_len Q la lb.
Proof.
  induction la; destruct lb; simpl; auto; try tauto; intros.
  split; intros; firstorder fail.
Qed.  

Section zip.
  Variable A B: Type.
  Lemma fst_combine (la: list A): forall (lb: list B), length la = length lb -> map fst (combine la lb) = la.
  Proof.
    induction la; simpl; intros; auto.
    destruct lb; simpl in *; try congruence.
    inversion H.
    specialize (IHla _ H1).
    f_equal; auto.
  Qed.

  Lemma snd_combine (la: list A): forall (lb: list B), length la = length lb -> map snd (combine la lb) = lb.
  Proof.
    induction la; simpl; intros; auto.
    - destruct lb; simpl in *; try congruence.
    - destruct lb; simpl in *; try congruence.
      inversion H.
      specialize (IHla _ H1).
      f_equal; auto.
  Qed.
End zip.

Lemma mapProp2_len_same A B (P: A -> B -> Prop) la:
  forall lb, length la = length lb -> mapProp_len P la lb <-> mapProp2 P (combine la lb).
Proof.
  induction la; simpl; intros; try tauto.
  destruct lb; try tauto.
  inversion H.
  specialize (IHla _ H1).
  split; intros; destruct H0;
    firstorder fail.
Qed.

Definition nthProp A (P: A -> Prop) la :=
  forall i, match nth_error la i with
            | Some a => P a
            | _ => True
            end.

Definition nthProp2 A B (P: A -> B -> Prop) la lb :=
  forall i, match nth_error la i, nth_error lb i with
            | Some a, Some b => P a b
            | _, _ => True
            end.

Lemma mapProp_nthProp A (P: A -> Prop) ls:
  mapProp P ls <-> nthProp P ls.
Proof.
  unfold nthProp.
  induction ls; simpl; auto; split; intros; auto.
  - destruct i; simpl; auto.
  - destruct i; simpl; try tauto.
    pose proof ((proj1 IHls) (proj2 H)).
    apply H0; auto.
  - destruct IHls.
    pose proof (H 0); simpl in *.
    split; auto.
    assert (sth: forall i, match nth_error (a :: ls) (S i) with
                           | Some a => P a
                           | None => True
                           end) by (intros; eapply (H (S i)); eauto).
    simpl in sth.
    eapply H1; eauto.
Qed.

Lemma mapProp2_nthProp A B (P: A -> B -> Prop) ls:
  mapProp2 P ls <-> forall i, match nth_error ls i with
                              | Some (a, b) => P a b
                              | _ => True
                              end.
Proof.
  induction ls; simpl; auto; split; intros; auto.
  - destruct i; simpl; auto.
  - destruct a; destruct i; simpl; try tauto.
    pose proof ((proj1 IHls) (proj2 H)).
    apply H0; auto.
  - destruct a, IHls.
    pose proof (H 0); simpl in *.
    split; auto.
    assert (sth: forall i, match nth_error ((a, b) :: ls) (S i) with
                           | Some (a, b) => P a b
                           | None => True
                           end) by (intros; eapply (H (S i)); eauto).
    simpl in sth.
    eapply H1; eauto.
Qed.

Lemma mapProp_len_nthProp2 A B (P: A -> B -> Prop) la lb:
  length la = length lb ->
  mapProp_len P la lb <-> nthProp2 P la lb.
Proof.
  unfold nthProp2.
  intros.
  apply mapProp2_len_same with (P := P) in H.
  rewrite H; clear H.
  generalize lb; clear lb.
  induction la; destruct lb; simpl; split; auto; intros; try destruct i; simpl; auto.
  - destruct (nth_error la i); simpl; auto.
  - tauto.
  - apply IHla; tauto.
  - pose proof (H 0); simpl in *.
    split; auto.
    assert (sth: forall i, match nth_error (a :: la) (S i) with
                           | Some a => match nth_error (b :: lb) (S i) with
                                       | Some b => P a b
                                       | None => True
                                       end
                           | None => True
                           end) by (intros; eapply (H (S i)); eauto).
    simpl in sth.
    eapply IHla; eauto.
Qed.

Lemma prod_dec A B
      (Adec: forall a1 a2: A, {a1 = a2} + {a1 <> a2})
      (Bdec: forall b1 b2: B, {b1 = b2} + {b1 <> b2}):
  forall x y: (A * B), {x = y} + {x <> y}.
Proof.
  decide equality.
Qed.

Lemma DisjKey_Commutative A B (l1 l2: list (A * B)): DisjKey l1 l2 -> DisjKey l2 l1.
Proof.
  unfold DisjKey, key_not_In; intros.
  firstorder fail.
Qed.

Section filter.
  Variable A: Type.
  Variable g: A -> bool.
  Lemma filter_length_le: forall ls, length (filter g ls) <= length ls.
  Proof.
    induction ls; simpl; intros; auto.
    destruct (g a); simpl; try omega.
  Qed.

  Lemma filter_length_same: forall ls, length (filter g ls) = length ls -> filter g ls = ls.
  Proof.
    induction ls; simpl; intros; auto.
    destruct (g a); f_equal.
    - apply IHls; auto.
    - pose proof (filter_length_le ls).
      Omega.omega.
  Qed.

  Lemma map_filter B (f: A -> B): forall ls,
      map f (filter g ls) = map f ls -> filter g ls = ls.
  Proof.
    intros.
    pose proof (map_length f (filter g ls)) as sth1.
    pose proof (map_length f ls) as sth2.
    rewrite H in *.
    rewrite sth1 in sth2.
    apply filter_length_same; auto.
  Qed.

  Lemma filter_true_list: forall ls (true_list: forall a, In a ls -> g a = true),
      filter g ls = ls.
  Proof.
    induction ls; simpl; auto; intros.
    case_eq (g a); intros.
    - f_equal.
      apply IHls; auto.
    - specialize (true_list a).
      clear - true_list H; firstorder congruence.
  Qed.

  Lemma filter_false_list: forall ls (false_list: forall a, In a ls -> g a = false),
      filter g ls = [].
  Proof.
    induction ls; simpl; auto; intros.
    case_eq (g a); intros.
    - specialize (false_list a).
      clear - false_list H; firstorder congruence.
    - apply IHls; auto.
  Qed.
End filter.

Lemma filter_in_dec_map A: forall (ls: list (string * A)),
    filter (fun x => id (getBool (in_dec string_dec (fst x) (map fst ls)))) ls = ls.
Proof.
  intros.
  eapply filter_true_list; intros.
  pose proof (in_map fst _ _ H) as sth.
  destruct (in_dec string_dec (fst a) (map fst ls)); simpl; auto.
Qed.

Lemma filter_not_in_dec_map A: forall (l1 l2: list (string * A)),
    DisjKey l1 l2 ->
    filter (fun x => id (getBool (in_dec string_dec (fst x) (map fst l1)))) l2 = [].
Proof.
  intros.
  eapply filter_false_list; intros.
  pose proof (in_map fst _ _ H0) as sth.
  destruct (in_dec string_dec (fst a) (map fst l1)); simpl; auto.
  firstorder fail.
Qed.

Lemma filter_negb_in_dec_map A: forall (ls: list (string * A)),
    filter (fun x => negb (getBool (in_dec string_dec (fst x) (map fst ls)))) ls = [].
Proof.
  intros.
  eapply filter_false_list; intros.
  pose proof (in_map fst _ _ H) as sth.
  destruct (in_dec string_dec (fst a) (map fst ls)); simpl; auto.
  firstorder fail.
Qed.

Lemma filter_negb_not_in_dec_map A: forall (l1 l2: list (string * A)),
    DisjKey l1 l2 ->
    filter (fun x => negb (getBool (in_dec string_dec (fst x) (map fst l1)))) l2 = l2.
Proof.
  intros.
  eapply filter_true_list; intros.
  pose proof (in_map fst _ _ H0) as sth.
  destruct (in_dec string_dec (fst a) (map fst l1)); simpl; auto.
  firstorder fail.
Qed.

Lemma SameList_map A B (f: A -> B):
  forall l1 l2, SameList l1 l2 -> SameList (map f l1) (map f l2).
Proof.
  unfold SameList, SubList in *; intros.
  setoid_rewrite in_map_iff; split; intros; destruct H; subst; firstorder fail.
Qed.

Lemma SameList_map_map A B C (f: A -> B) (g: B -> C):
  forall l1 l2, SameList (map f l1) (map f l2) -> SameList (map (fun x => g (f x)) l1) (map (fun x => g (f x)) l2).
Proof.
  intros.
  apply SameList_map with (f := g) in H.
  rewrite ?map_map in H.
  auto.
Qed.

Lemma filter_contra A B (f: A -> B) (g h: B -> bool):
  forall ls,
    (forall a, g (f a) = true -> h (f a) = false -> ~ In (f a) (map f ls)) ->
    (forall a, h (f a) = true -> g (f a) = false -> ~ In (f a) (map f ls)) ->
    filter (fun x => g (f x)) ls = filter (fun x => h  (f x)) ls.
Proof.
  induction ls; simpl; auto; intros.
  assert (filter (fun x => g (f x)) ls = filter (fun x => h (f x)) ls) by (firstorder first).
  specialize (H a); specialize (H0 a).
  case_eq (g (f a)); case_eq (h (f a)); intros.
  - f_equal; auto.
  - rewrite H2, H3 in *.
    firstorder fail.
  - rewrite H2, H3 in *.
    firstorder fail.
  - auto.
Qed.

Lemma filter_map_app_sameKey A B (f: A -> B) (Bdec: forall b1 b2: B, {b1 = b2} + {b1 <> b2}):
  forall ls l1 l2,
    (forall x, ~ In x l1 \/ ~ In x l2) ->
    map f ls = l1 ++ l2 ->
    ls = (filter (fun x => getBool (in_dec Bdec (f x) l1)) ls)
           ++ filter (fun x => getBool (in_dec Bdec (f x) l2)) ls.
Proof.
  induction ls; simpl; auto; intros.
  destruct l1.
  - simpl in *; destruct l2; simpl in *.
    + discriminate.
    + inversion H0; subst; clear H0.
      destruct (Bdec (f a) (f a)); [simpl| exfalso; tauto].
      rewrite filter_false; simpl.
      f_equal.
      rewrite filter_true_list; auto; intros.
      destruct (Bdec (f a) (f a0)); auto.
      destruct (in_dec Bdec (f a0) (map f ls)); auto; simpl.
      apply (in_map f) in H0.
      tauto.
  - inversion H0; subst; clear H0.
    destruct (in_dec Bdec (f a) l2); [assert (~ In (f a) l2) by (specialize (H (f a)); firstorder fail); exfalso; tauto|].
    unfold getBool at 4.
    unfold getBool at 1.
    destruct (in_dec Bdec (f a) (f a :: l1)); [| exfalso; simpl in *; tauto].
    assert (sth: forall A (a: A) l1 l2, (a :: l1) ++ l2 = a :: l1 ++ l2) by auto.
    rewrite sth.
    f_equal; clear sth.
    assert (sth: forall x, ~ In x l1 \/ ~ In x l2) by (clear - H; firstorder fail).
    specialize (IHls _ _ sth H3).
    rewrite IHls at 1.
    f_equal.
    destruct (in_dec Bdec (f a) l1).
    + eapply filter_contra with (f := f) (g := fun x => getBool (in_dec Bdec x l1)) (h := fun x => getBool (in_dec Bdec x (f a :: l1))); auto; intros; intro; simpl in *.
      * destruct (Bdec (f a) (f a0)); try discriminate.
        destruct (in_dec Bdec (f a0) l1); discriminate.
      * rewrite H3 in H2.
        rewrite in_app_iff in *.
        destruct (in_dec Bdec (f a0) l1); simpl in *; destruct (Bdec (f a) (f a0)); simpl in *; firstorder congruence.
    + eapply filter_contra with (f := f) (g := fun x => getBool (in_dec Bdec x l1)) (h := fun x => getBool (in_dec Bdec x (f a :: l1))); auto; intros; intro; simpl in *.
      * destruct (Bdec (f a) (f a0)); try discriminate.
        destruct (in_dec Bdec (f a0) l1); discriminate.
      * rewrite H3 in H2.
        rewrite in_app_iff in *.
        destruct (in_dec Bdec (f a0) l1); simpl in *; destruct (Bdec (f a) (f a0)); simpl in *; firstorder congruence.
Qed.

Lemma nth_error_map A B (f: A -> B) (P: B -> Prop) i:
  forall ls,
    match nth_error (map f ls) i with
    | Some b => P b
    | None => True
    end <-> match nth_error ls i with
            | Some a => P (f a)
            | None => True
            end.
Proof.
  induction i; destruct ls; simpl; auto; intros; tauto.
Qed.

Lemma length_combine_cond A B: forall l1 l2, length l1 = length l2 ->
                                    length (@combine A B l1 l2) = length l1.
Proof.
  induction l1; destruct l2; simpl; auto.
Qed.

Lemma nth_error_combine A B C (f: (A * B) -> C) (P: C -> Prop) i: forall l1 l2,
    length l1 = length l2 ->
    (match nth_error (map f (combine l1 l2)) i with
     | Some c => P c
     | None => True
     end <-> match nth_error l1 i, nth_error l2 i with
             | Some a, Some b => P (f (a,b))
             | _, _ => True
             end).
Proof.
  induction i; destruct l1, l2; simpl; intros; try tauto.
  - congruence.
  - inversion H.
    apply IHi; auto.
Qed.

Definition zip4 {A B C D} (l1 : list A) (l2 : list B) (l3 : list C) (l4 : list D) :=
  List.combine (List.combine l1 l2) (List.combine l3 l4).



Lemma nthProp2_cons A B (P: A -> B -> Prop):
  forall la lb a b,
    nthProp2 P (a :: la) (b :: lb) <->
    (nthProp2 P la lb /\ P a b).
Proof.
  intros.
  unfold nthProp2.
  split; intros.
  - split; intros.
    + specialize (H (S i)).
      simpl in *; auto.
    + specialize (H 0); simpl in *; auto.
  - destruct i; simpl in *; destruct H; auto.
    eapply H; eauto.
Qed.


Lemma combine_length A B n:
  forall (l1: list A) (l2: list B),
    length l1 = n ->
    length l2 = n ->
    length (List.combine l1 l2) = n.
Proof.
  induction n; simpl; intros; auto.
  - rewrite length_zero_iff_nil in *; subst; auto.
  - destruct l1, l2; simpl in *; try discriminate.
    specialize (IHn l1 l2 ltac:(Omega.omega) ltac:(Omega.omega)).
    Omega.omega.
Qed.

Lemma zip4_length A B C D n:
  forall (l1: list A) (l2: list B) (l3: list C) (l4: list D),
    length l1 = n ->
    length l2 = n ->
    length l3 = n ->
    length l4 = n ->
    length (zip4 l1 l2 l3 l4) = n.
Proof.
  unfold zip4; intros.
  assert (length (List.combine l1 l2) = n) by (eapply combine_length; eauto).
  assert (length (List.combine l3 l4) = n) by (eapply combine_length; eauto).
  eapply combine_length; eauto.
Qed.

Lemma length_upto t:
  forall b,
    (t > b \/ t = 0)%nat ->
    length (b upto t) = (t - b)%nat.
Proof.
  induction t; simpl; auto; intros.
  destruct (Nat.eq_dec b t); simpl; subst.
  - destruct t; auto.
    Omega.omega.
  - specialize (IHt b ltac:(Omega.omega)).
    rewrite app_length.
    rewrite IHt.
    simpl.
    destruct b; Omega.omega.
Qed.

Lemma nth_combine A B n:
  forall (l1: list A) (l2: list B) a b,
    length l1 = n ->
    length l2 = n ->
    forall i, (i < n)%nat ->
              nth i (List.combine l1 l2) (a,b) = (nth i l1 a, nth i l2 b).
Proof.
  induction n; simpl; auto; intros.
  - Omega.omega.
  - destruct l1, l2; simpl in *; try discriminate.
    destruct i; simpl in *; auto.
    specialize (IHn l1 l2 a b ltac:(Omega.omega) ltac:(Omega.omega) i ltac:(Omega.omega)); auto.
Qed.

Lemma nth_zip4 A B C D n:
  forall (l1: list A) (l2: list B) (l3: list C) (l4: list D) a b c d,
    length l1 = n ->
    length l2 = n ->
    length l3 = n ->
    length l4 = n ->
    forall i, (i < n)%nat ->
              nth i (zip4 l1 l2 l3 l4) ((a, b), (c, d)) = ((nth i l1 a, nth i l2 b), (nth i l3 c, nth i l4 d)).
Proof.
  unfold zip4; intros.
  assert (length (List.combine l1 l2) = n) by (eapply combine_length; eauto).
  assert (length (List.combine l3 l4) = n) by (eapply combine_length; eauto).
  repeat erewrite nth_combine; eauto.
Qed.

Lemma length_minus1_nth A ls:
  forall (a b: A),
    nth (length ls) (ls ++ a :: nil) b = a.
Proof.
  induction ls; simpl; auto.
Qed.

Lemma upto_0_n_length n:
  0 <> n ->
  length (0 upto n) <> 0.
Proof.
  intros; intro.
  destruct n; [tauto|].
  rewrite length_upto in * by (Omega.omega).
  Omega.omega.
Qed.

Lemma nth_0_upto_n_0 n:
  nth 0 (0 upto n) 0 = 0.
Proof.
  induction n; simpl; auto.
  match goal with
  | |- context [if ?P then _ else _] => destruct P; simpl; auto
  end.
  rewrite app_nth1; auto.
  pose proof (upto_0_n_length n0).
  Omega.omega.
Qed.

Lemma nth_0_upto_n n:
  forall i,
    (i < n)%nat ->
    nth i (0 upto n) 0 = i.
Proof.
  induction n; simpl; intros; auto.
  - Omega.omega.
  - match goal with
    | |- context [if ?P then _ else _] => destruct P; simpl; auto; subst
    end.
    + destruct i; auto; try Omega.omega.
    + destruct (Nat.eq_dec i n); subst.
      * pose proof (@length_upto n 0 ltac:(Omega.omega)) as sth.
        assert (sth2: (n - 0)%nat = n) by Omega.omega.
        rewrite sth2 in *.
        rewrite <- sth at 1.
        rewrite length_minus1_nth.
        auto.
      * rewrite app_nth1.
        -- eapply IHn; eauto.
           Omega.omega.
        -- rewrite (@length_upto n 0 ltac:(Omega.omega)).
           Omega.omega.
Qed.

Lemma log2_up_pow2 n:
  (n <= Nat.pow 2 (Nat.log2_up n))%nat.
Proof.
  destruct n; simpl; auto.
  pose proof (Nat.log2_log2_up_spec (S n) ltac:(Omega.omega)).
  Omega.omega.
Qed.

Lemma append_remove_prefix a:
  forall b c,
    (a ++ b)%string = (a ++ c)%string <->
    b = c.
Proof.
  induction a; simpl; intros; auto.
  - reflexivity.
  - split; intros; subst; auto.
    inversion H.
    eapply IHa; eauto.
Qed.

Lemma append_nil a:
  (a ++ "")%string = a.
Proof.
  induction a; simpl; auto; intros.
  rewrite IHa.
  auto.
Qed.
  
Lemma append_assoc a:
  forall b c,
    (a ++ (b ++ c))%string = ((a ++ b) ++ c)%string.
Proof.
  induction a; simpl; auto; intros.
  f_equal; auto.
Qed.

Lemma append_cons a b:
  (String a b)%string = (String a EmptyString ++ b)%string.
Proof.
  auto.
Qed.

Lemma append_eq_nil:
  forall a b,
    (a ++ b)%string = EmptyString <-> a = EmptyString /\ b = EmptyString.
Proof.
  induction a; destruct b; simpl; split; intros; auto.
  - destruct H; congruence.
  - congruence.
  - destruct H; congruence.
  - congruence.
  - destruct H; congruence.
Qed.
  

Lemma append_cons_suffix:
  forall b c a,
    (b ++ String a "")%string = (c ++ String a "")%string <->
    b = c.
Proof.
  induction b; destruct c; simpl; split; intros; auto.
  - inversion H; subst.
    apply eq_sym in H2.
    rewrite append_eq_nil in H2.
    destruct H2.
    congruence.
  - congruence.
  - inversion H; subst.
    apply append_eq_nil in H2.
    destruct H2; congruence.
  - congruence.
  - inversion H; subst.
    f_equal.
    eapply IHb; eauto.
  - inversion H; subst.
    auto.
Qed.

Lemma append_remove_suffix a:
  forall b c,
    (b ++ a)%string = (c ++ a)%string <->
    b = c.
Proof.
  induction a; simpl; intros; auto; split; intros; subst; auto.
  - rewrite ?append_nil in H.
    auto.
  - rewrite append_cons in H.
    rewrite ?append_assoc in H.
    rewrite IHa in H.
    rewrite append_cons_suffix in H.
    auto.
Qed.


Ltac discharge_appendage :=
  repeat match goal with
         | H: (?a ++ ?b)%string = (?a ++ ?c)%string |- _ =>
           rewrite append_remove_prefix in H; subst
         | H: (?a ++ ?b)%string = (?c ++ ?b)%string |- _ =>
           rewrite append_remove_suffix in H; subst
         | H: _ \/ _ |- _ => destruct H; subst
         end.

Ltac discharge_DisjKey :=
  match goal with
  | |- DisjKey ?P ?Q => rewrite DisjKeyWeak_same by apply string_dec;
                        let k := fresh in
                        let H1 := fresh in
                        let H2 := fresh in
                        unfold DisjKeyWeak; simpl; intros k H1 H2
  end;
  discharge_appendage;
  subst;
  auto;
  try discriminate.


Local Example test_normaldisj:
  DisjKey (map (fun x => (x, 1)) ("a" :: "b" :: "c" :: nil))%string
          (map (fun x => (x, 2)) ("d" :: "e" :: nil))%string.
Proof.
  simpl.
  discharge_DisjKey.
Qed.

Local Example test_prefix_disj a:
  DisjKey (map (fun x => ((a ++ x)%string, 1)) ("ab" :: "be" :: "cs" :: nil))%string
          (map (fun x => ((a ++ x)%string, 2)) ("de" :: "et" :: nil))%string.
Proof.
  simpl.
  discharge_DisjKey.
Qed.

Local Example test_suffix_disj a:
  DisjKey (map (fun x => ((x ++ a)%string, 1)) ("ab" :: "be" :: "cs" :: nil))%string
          (map (fun x => ((x ++ a)%string, 2)) ("de" :: "et" :: nil))%string.
Proof.
  simpl.
  discharge_DisjKey.
Qed.


