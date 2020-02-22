Require Import String Coq.Lists.List Omega Fin Eqdep Bool Coq.ZArith.Zdiv Lia.
Require Import Coq.Arith.Even.
Require Import Coq.Arith.Div2.
Require Import Coq.NArith.NArith.
Require Import Arith_base.
Require Import Arith Coq.ZArith.Znat Psatz.

Import ListNotations.

Set Implicit Arguments.
Set Asymmetric Patterns.

Section NubBy.
  Variable A : Type.
  Variable f: A -> A -> bool.

  Definition nubBy (ls: list A) :=
    fold_right (fun x acc => if existsb (f x) acc
                             then acc
                             else x :: acc) nil ls.
End NubBy.

Section Tree.
  Inductive Tree (A: Type): Type :=
  | Leaf (_: list A)
  | Node (_: list (Tree A)).

  Fixpoint flattenTree A (t: Tree A): list A :=
    match t with
    | Leaf xs => xs
    | Node xs =>
      (fix fold xs :=
         match xs with
         | nil => nil
         | x :: xs => flattenTree x ++ fold xs
         end) xs
    end.
End Tree.

Fixpoint string_rev (ls: string) :=
  match ls with
  | EmptyString => EmptyString
  | String x xs => append (string_rev xs) (String x EmptyString)
  end.

(* Definition in_decb{X}(eqb : X -> X -> bool) : X -> list X -> bool :=
  fun x => existsb (eqb x).

Lemma in_decb_In{X} : forall eqb : X -> X -> bool,
  (forall x y, eqb x y = true <-> x = y) -> forall x xs, in_decb eqb x xs = true <-> In x xs.
Proof.
  intros; unfold in_decb;
  rewrite existsb_exists.
  split.
  intros [y [Hy1 Hy2]].
  rewrite H in Hy2; congruence.
  intro.
  exists x; split; [auto | rewrite H; auto].
Qed. *)

Fixpoint Fin_t_foldr
         (A : Type)
         (n : nat)
         (init : A)
  := match n return
           forall (f : Fin.t n -> A -> A), A
     with
     | 0 => fun _ => init
     | S m => fun f => f Fin.F1 (Fin_t_foldr m init (fun i => f (Fin.FS i)))
     end.

Section nth_Fin.
  Variable A: Type.
  Fixpoint nth_Fin (ls: list A): Fin.t (length ls) -> A :=
    match ls return Fin.t (length ls) -> A with
    | nil => fun pf => Fin.case0 _ pf
    | x :: xs => fun i =>
                   match i in Fin.t n return n = length (x :: xs) -> A with
                   | Fin.F1 _ => fun _ => x
                   | Fin.FS _ y => fun pf =>
                                     nth_Fin xs
                                             match eq_add_S _ _ pf in _ = Y return Fin.t Y with
                                             | eq_refl => y
                                             end
                   end eq_refl
    end.

  Definition nth_Fin' (ls: list A) n (pf: n = length ls) (i: Fin.t n): A :=
    nth_Fin ls (Fin.cast i pf).

  Fixpoint nth_Fin'' (ls: list A) n (pf: n <= length ls) {struct ls} : Fin.t n -> A.
  Proof.
    refine(
    match ls return (n <= length ls) -> Fin.t n -> A with
    | nil => fun pf i => Fin.case0 _ (Fin.cast i _)
    | x :: xs => fun pf i =>
       match i in Fin.t m return m <= length (x :: xs) -> A with
       | Fin.F1 _ => fun _ => x
       | Fin.FS _ z => fun pf => nth_Fin'' xs _ _ z
       end _
    end _).
    all: cbn in *; abstract omega.
  Defined.

  Lemma nth_Fin'_nth : forall n d (i: Fin.t n) (xs: list A) (len_eq: n = length xs),
    let i' := proj1_sig (Fin.to_nat i) in
    nth_Fin' xs len_eq i = nth i' xs d.
  Proof.
    induction n; cbn; intros *; try easy.
    destruct xs; cbn in *; try easy.
    inversion len_eq.
    destruct i eqn:?; cbn; auto.
    destruct (Fin.to_nat _) eqn:?; cbn.
    assert (n0 = n); subst.
    { inversion len_eq; subst; auto. }
    specialize (IHn d t xs (f_equal pred len_eq)).
    rewrite Heqs in IHn; cbn in IHn; auto.
  Qed.

  Lemma nth_Fin_nth : forall d (xs: list A) (i: Fin.t (length xs)),
    let i' := proj1_sig (Fin.to_nat i) in
    nth_Fin xs i = nth i' xs d.
  Proof.
    cbn; intros.
    rewrite <- (nth_Fin'_nth _ _ _ eq_refl).
    unfold nth_Fin'; f_equal.
    clear; induction i; cbn; auto.
    rewrite <- IHi; auto.
  Qed.
End nth_Fin.

Definition fin_case n x :
  forall (P : Fin.t (S n) -> Type),
    P Fin.F1 ->
    (forall y, P (Fin.FS y)) ->
    P x :=
  match x in Fin.t n0
     return
       forall P,
         match n0 return (Fin.t n0 -> (Fin.t n0 -> Type) -> Type) with
           | 0 => fun _ _ => False
           | S m => fun x P => P Fin.F1 -> (forall x0, P (Fin.FS x0)) -> P x
         end x P
  with
    | Fin.F1 _ => fun _ H1 _ => H1
    | Fin.FS _ _ => fun _ _ HS => HS _
  end.

Ltac fin_dep_destruct v :=
  pattern v; apply fin_case; clear v; intros.

Lemma Fin_cast_lemma : forall m n i (p q : m = n),
  Fin.cast i p = Fin.cast i q.
Proof.
  intros.
  rewrite (UIP_nat _ _ p q); reflexivity.
Defined.

Lemma fin_to_nat_cast : forall n (i: Fin.t n) m (Heq: n = m),
  proj1_sig (Fin.to_nat (Fin.cast i Heq)) = proj1_sig (Fin.to_nat i).
Proof.
  induction n; cbn; intros *; try easy.
  destruct m; try easy.
  assert (n = m) by auto.
  destruct i eqn:?; cbn; auto.
  assert (n0 = n) by (subst; auto); subst.
  specialize (IHn t m eq_refl).
  destruct (Fin.to_nat t) eqn:?; cbn in *.
  rewrite <- (Fin_cast_lemma _ eq_refl).
  destruct (Fin.to_nat (Fin.cast t eq_refl)) eqn:?; cbn in *; auto.
Qed.

Definition UIP(X : Type) := forall (x y : X)(p q : x = y), p = q.

Definition discrete(X : Type) := forall (x y : X), {x = y} + {x <> y}.

Theorem hedberg : forall X, discrete X -> UIP X.
Proof.
  intros X Xdisc x y.

  assert ( 
      lemma :
        forall proof : x = y,  
          match Xdisc x x, Xdisc x y with
          | left r, left s => proof = eq_trans (eq_sym r) s
          | _, _ => False
          end
    ).
  {
    destruct proof.
    destruct (Xdisc x x) as [pr | f].
    destruct pr; auto.
    elim f; reflexivity.
  }

  intros p q.
  assert (p_given_by_dec := lemma p).
  assert (q_given_by_dec := lemma q).
  destruct (Xdisc x x).
  destruct (Xdisc x y).
  apply (eq_trans p_given_by_dec (eq_sym q_given_by_dec)).
  contradiction.
  contradiction.
Defined.

Definition map_length_red := 
  (fun (A B : Type) (f : A -> B) (l : list A) =>
     list_ind (fun l0 : list A => Datatypes.length (map f l0) = Datatypes.length l0) eq_refl
              (fun (a : A) (l0 : list A) (IHl : Datatypes.length (map f l0) = Datatypes.length l0) =>
                 f_equal_nat nat S (Datatypes.length (map f l0)) (Datatypes.length l0) IHl) l)
  : forall (A B : Type) (f : A -> B) (l : list A), Datatypes.length (map f l) = Datatypes.length l.
  
Section nth_Fin_map2.
  Variable A B: Type.
  Variable g: A -> B.
  Variable f: B -> Type.

  Fixpoint nth_Fin_map2 (ls: list A):
    forall (p : Fin.t (length (map g ls)))
           (val: f (g (nth_Fin ls (Fin.cast p (map_length_red g ls))))),
      f (nth_Fin (map g ls) p).
    refine
      match ls return forall (p : Fin.t (length (map g ls)))
                             (val: f (g (nth_Fin ls (Fin.cast p (map_length_red g ls))))),
          f (nth_Fin (map g ls) p) with
      | nil => fun i _ => Fin.case0 (fun j => f (nth_Fin (map g nil) j)) i
      | x :: xs => fun p => _
      end.
    fin_dep_destruct p.
    + exact val.
    + apply (nth_Fin_map2 xs y).
      match goal with
      | |- f (g (nth_Fin xs (Fin.cast y ?P))) => 
        rewrite (hedberg eq_nat_dec P (f_equal Init.Nat.pred (map_length_red g (x :: xs))))
      end.
      exact val.
  Defined.
End nth_Fin_map2.

Section Fin.

Fixpoint Fin_forallb{n} : (Fin.t n -> bool) -> bool :=
  match n return (Fin.t n -> bool) -> bool with
  | 0 => fun _ => true
  | S m => fun p => p Fin.F1 && Fin_forallb (fun i => p (Fin.FS i))
  end.

Lemma Fin_forallb_correct{n} : forall p : Fin.t n -> bool,
  Fin_forallb p = true <-> forall i, p i = true.
Proof.
  induction n; intros; split; intros.
  apply (Fin.case0 (fun i => p i = true)).
  reflexivity.
  simpl in H.
  fin_dep_destruct i.
  destruct (p F1); [auto|discriminate].
  apply (IHn (fun j => p (FS j))).
  destruct (p F1); [auto|discriminate].
  simpl.
  apply andb_true_intro; split.
  apply H.
  apply IHn.
  intro; apply H.
Qed.

Definition Fin_cast : forall {m n}, Fin.t m -> m = n -> Fin.t n :=
  fun m n i pf => match pf in _ = y return Fin.t y with
                  | eq_refl => i
                  end.

End Fin.




Lemma inversionPair A B (a1 a2: A) (b1 b2: B):
  (a1, b1) = (a2, b2) ->
  a1 = a2 /\ b1 = b2.
Proof.
  intros H.
  inversion H.
  subst; auto.
Qed.

Lemma inversionExistT A (P: A -> Type) (x1 x2: A) (y1: P x1) (y2: P x2):
  existT P x1 y1 = existT P x2 y2 -> exists pf: x1 = x2, match pf in _ = Y return _ Y with
                                                         | eq_refl => y1
                                                         end = y2.
Proof.
  intros H.
  pose proof (EqdepFacts.eq_sigT_fst H) as sth.
  exists sth.
  subst.
  apply Eqdep.EqdepTheory.inj_pair2 in H; subst.
  auto.
Qed.

Lemma inversionPairExistT A B (f: B -> Type) (a1 a2: A) (b1 b2: B) (f1: f b1) (f2: f b2):
  (a1, existT f b1 f1) = (a2, existT f b2 f2) ->
  a1 = a2 /\ existT f b1 f1 = existT f b2 f2.
Proof.
  intros.
  inversion H.
  repeat split; auto.
Qed.

Lemma InSingleton_impl A (x y: A): In x [y] -> x = y.
Proof.
  intros; simpl in *.
  destruct H; auto; tauto.
Qed.

Definition fromOption (A : Type) (mx : option A) (default : A) : A
  := match mx with
       | Some x => x
       | _      => default
       end.

Definition strings_in (xs : list string) (x : string)
  :  bool
  := existsb (String.eqb x) xs.

Definition strings_any_in (xs : list string)
  :  list string -> bool
  := existsb (strings_in xs).

Definition strings_all_in (xs : list string)
  :  list string -> bool
  := forallb (strings_in xs).

Definition emptyb (A : Type) (xs : list A)
  :  bool
  := match xs with
       | nil => true
       | _   => false
       end.

Definition list_max
  :  nat -> list (option nat) -> nat
  := fold_right (fun x acc => fromOption (option_map (Nat.max acc) x) acc).

Ltac existT_destruct dec :=
  match goal with
  | H: existT _ _ _ = existT _ _ _ |- _ =>
    apply EqdepFacts.eq_sigT_eq_dep in H;
    apply (Eqdep_dec.eq_dep_eq_dec dec) in H;
    subst
  end.

Fixpoint Fin_eq_dec n a {struct a}: forall (b: Fin.t n), {a = b} + {a <> b}.
Proof.
  refine
    match a in Fin.t n return forall b: Fin.t n, {a = b} + {a <> b} with
    | Fin.F1 _ => fun b => match b with
                           | Fin.F1 _ => left eq_refl
                           | _ => right _
                           end
    | Fin.FS _ x => fun b => match b in Fin.t (S m) return forall x: Fin.t m, (forall y: Fin.t m, {x = y} + {x <> y}) -> {Fin.FS x = b} + {Fin.FS x <> b}  with
                             | Fin.F1 _ => fun _ _ => right _
                             | Fin.FS _ y => fun _ f =>
                                               match f y with
                                               | left eq1 => left (f_equal Fin.FS eq1)
                                               | right neq => right _
                                               end
                             end x (Fin_eq_dec _ x)
    end; intro; clear Fin_eq_dec; try (abstract discriminate).
  abstract (injection H; intros; existT_destruct Nat.eq_dec; tauto).
Defined.


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

Lemma seq_eq sz: forall n, seq n (S sz) = seq n sz ++ [n + sz].
Proof.
  induction sz; simpl; auto; intros; repeat f_equal.
  - rewrite Nat.add_0_r; auto.
  - specialize (IHsz (S n)).
    assert (sth: S n + sz = n + S sz) by omega.
    rewrite <- sth.
    rewrite <- IHsz.
    auto.
Qed.

Section map_fold_eq.
  Variable A: Type.
  Variable f: A -> A.

  Fixpoint zeroToN n :=
    match n with
    | 0 => nil
    | S m => zeroToN m ++ m :: nil
    end.

  Lemma zeroToN_upto n: zeroToN n = seq 0 n.
  Proof.
    induction n; simpl; auto.
    rewrite IHn.
    pose proof (seq_eq n 0) as sth.
    simpl in sth.
    auto.
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

  Lemma map_fold_left_eq ls: map f ls = fold_left transform_nth_left (seq 0 (length ls)) ls.
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

  Lemma map_fold_right_eq ls: map f ls = fold_right transform_nth_right ls (seq 0 (length ls)).
  Proof.
    rewrite <- zeroToN_upto.
    eapply map_fold_right_eq'.
  Qed.
End map_fold_eq'.


Lemma nth_error_nth A : forall (xs: list A) n d v,
  nth_error xs n = Some v ->
  nth n xs d = v.
Proof.
  induction xs; cbn; intros; destruct n; cbn in *; try easy; auto.
  inversion H; auto.
Qed.

Lemma nth_error_not_None A : forall n (xs: list A),
  nth_error xs n <> None ->
  exists x, nth_error xs n = Some x.
Proof.
  induction n; destruct xs; cbn; try easy; eauto.
Qed.

Fixpoint getFins n :=
  match n return list (Fin.t n) with
  | 0 => nil
  | S m => Fin.F1 :: map Fin.FS (getFins m)
  end.

Fixpoint getFinsBound m n: list (Fin.t n) :=
  match m return (list (Fin.t n)) with
  | 0 => nil
  | S k => match n with
           | 0 => nil
           | S n' => Fin.F1 :: map Fin.FS (getFinsBound k n')
           end
  end.

Definition mapOrFins n (x: Fin.t n) := fold_left (fun a b => x = b \/ a) (getFins n) False.

Lemma getFins_length : forall n, length (getFins n) = n.
Proof.
  induction n; cbn; auto.
  rewrite map_length; auto.
Qed.

Lemma getFins_all : forall n (i: Fin.t n), In i (getFins n).
Proof.
  induction i; cbn; auto using in_map.
Qed.

Lemma getFins_nth_error : forall n (i: Fin.t n),
  let i' := proj1_sig (Fin.to_nat i) in
  nth_error (getFins n) i' = Some i.
Proof.
  induction i; cbn in *; auto.
  destruct (Fin.to_nat i); cbn in *.
  apply map_nth_error; auto.
Qed.

Lemma getFins_nth : forall n d (i: Fin.t n),
  let i' := proj1_sig (Fin.to_nat i) in
  nth i' (getFins n) d = i.
Proof.
  intros.
  apply nth_error_nth.
  apply getFins_nth_error.
Qed.

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
    Variable Adec: forall a1 a2: A, {a1 = a2} + {a1 <> a2}.
    
    Variable l1 l2: list (A * B).

    Definition DisjKey :=
      forall k, ~ In k (map fst l1) \/ ~ In k (map fst l2).
    
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
  
  Lemma NoDup_DisjKey l1:
    forall l2,
      NoDup (map fst l1) ->
      NoDup (map fst l2) ->
      DisjKey l1 l2 ->
      NoDup (map fst (l1 ++ l2)).
  Proof.
    induction l1; simpl; auto; intros.
    inversion H; subst; clear H.
    unfold DisjKey in H1; simpl in H1.
    assert (sth: forall k, ~ In k (map fst l1) \/ ~ In k (map fst l2)) by (clear - H1; firstorder fail).
    specialize (IHl1 _ H5 H0 sth).
    constructor; auto.
    assert (~ In (fst a) (map fst l2)) by (clear - H1; firstorder fail).
    rewrite map_app; rewrite in_app_iff.
    tauto.
  Qed.

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
Defined.

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

Section DisjKey_filter.
  Variable A B: Type.
  Variable decA: forall (a1 a2: A), {a1 = a2} + {a1 <> a2}.
  
  Lemma DisjKey_filter: forall (l1 l2: list (A * B)),
      DisjKey l1 l2 <->
      filter (fun x => (getBool (in_dec decA (fst x) (map fst l1)))) l2 = [].
  Proof.
    intros.
    split; intros.
    - eapply filter_false_list; intros.
      pose proof (in_map fst _ _ H0) as sth.
      destruct (in_dec decA (fst a) (map fst l1)); simpl; auto.
      firstorder fail.
    - pose proof (filter_nil1 _ _ H) as sth.
      rewrite DisjKeyWeak_same by auto.
      unfold DisjKeyWeak; intros.
      rewrite in_map_iff in *.
      destruct H0 as [x1 [sth1 in1]].
      destruct H1 as [x2 [sth2 in2]].
      subst.
      specialize (sth _ in2); simpl in *.
      destruct (in_dec decA (fst x2) (map fst l1)); [discriminate|].
      clear sth.
      erewrite in_map_iff in n.
      firstorder auto.
  Qed.
End DisjKey_filter.  

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

(* Lemma length_upto t: *)
(*   forall b, *)
(*     (t > b \/ t = 0)%nat -> *)
(*     length (b upto t) = (t - b)%nat. *)
(* Proof. *)
(*   induction t; simpl; auto; intros. *)
(*   destruct (Nat.eq_dec b t); simpl; subst. *)
(*   - destruct t; auto. *)
(*     rewrite seq_length. *)
(*     auto. *)
(*   - specialize (IHt b ltac:(Omega.omega)). *)
(*     rewrite seq_length. *)
(*     destruct b; auto. *)
(* Qed. *)

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
  length (seq 0 n) <> 0.
Proof.
  rewrite seq_length.
  intros; congruence.
Qed.

Lemma nth_0_upto_n_0 n:
  nth 0 (seq 0 n) 0 = 0.
Proof.
  induction n; simpl; auto.
Qed.

Lemma nth_0_upto_n n:
  forall i,
    (i < n)%nat ->
    nth i (seq 0 n) 0 = i.
Proof.
  intros.
  rewrite seq_nth; auto.
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

Lemma string_rev_append : forall s1 s2,
  (string_rev (s1 ++ s2) = string_rev s2 ++ string_rev s1)%string.
Proof.
  induction s1; intros *; cbn; auto using append_nil.
  rewrite IHs1; auto using append_assoc.
Qed.

Lemma key_not_In_fst A B (ls: list (A*B)):
  forall k,
    key_not_In k ls <->
    ~ In k (map fst ls).
Proof.
  induction ls; simpl; auto; split; intros; try tauto.
  - unfold key_not_In in *; simpl; intros; auto.
  - intro.
    unfold key_not_In in H; simpl in *.
    assert (sth: key_not_In k ls) by (firstorder fail).
    pose proof (proj1 (IHls _) sth) as sth2.
    destruct H0; [subst|tauto].
    specialize (H (snd a)).
    destruct a; simpl in *.
    firstorder fail.
  - unfold key_not_In in *; simpl; intros; auto.
    intro.
    destruct a; simpl in *.
    destruct H0.
    + inversion H0; subst; clear H0.
      firstorder fail.
    + apply (in_map fst) in H0; simpl in *.
      firstorder fail.
Qed.

Lemma InFilterPair A B (dec: forall a1 a2, {a1 = a2} + {a1 <> a2}):
  forall (ls: list (A * B)),
  forall x, In x ls <->
            In x (filter (fun t => getBool (dec (fst x) (fst t))) ls).
Proof.
  induction ls; simpl; split; auto; intros.
  - destruct H; [subst|]; auto.
    + destruct (dec (fst x) (fst x)) ; simpl in *; tauto.
    + apply IHls in H.
      destruct (dec (fst x) (fst a)) ; simpl in *; auto.
  - destruct (dec (fst x) (fst a)) ; simpl in *.
    + destruct H; auto.
      apply IHls in H; auto.
    + eapply IHls in H; eauto.
Qed.

Lemma InFilter A (dec: forall a1 a2, {a1 = a2} + {a1 <> a2}):
  forall (ls: list A),
  forall x, In x ls <->
            In x (filter (fun t => getBool (dec x t)) ls).
Proof.
  induction ls; simpl; split; auto; intros.
  - destruct H; [subst|]; auto.
    + destruct (dec x x) ; simpl in *; tauto.
    + apply IHls in H.
      destruct (dec x a) ; simpl in *; auto.
  - destruct (dec x a) ; simpl in *.
    + destruct H; auto.
    + eapply IHls in H; eauto.
Qed.

Lemma InSingleton A (x: A): In x [x].
Proof.
  simpl; auto.
Qed.

(* Useful Ltacs *)
Ltac EqDep_subst :=
  repeat match goal with
         |[H : existT ?a ?b ?c1 = existT ?a ?b ?c2 |- _] => apply Eqdep.EqdepTheory.inj_pair2 in H; subst
         end.

Ltac inv H :=
  inversion H; subst; clear H.

Ltac dest :=
  repeat (match goal with
          | H: _ /\ _ |- _ => destruct H
          | H: exists _, _ |- _ => destruct H
          end).

Section NoDup.
  Variable A: Type.
  Variable decA: forall a1 a2: A, {a1 = a2} + {a1 <> a2}.
  Fixpoint NoDup_fn (ls: list A) :=
    match ls with
    | nil => true
    | x :: xs => andb (negb (getBool (in_dec decA x xs))) (NoDup_fn xs)
    end.

  Lemma NoDup_dec l:
    NoDup l <-> NoDup_fn l = true.
  Proof.
    intros.
    induction l; simpl; split; auto; intros; try solve [econstructor; eauto].
    - inv H.
      rewrite IHl in *.
      destruct (in_dec decA a l); simpl; auto.
    - rewrite andb_true_iff in *; dest.
      rewrite negb_true_iff in *.
      rewrite <- IHl in *.
      econstructor; eauto.
      destruct (in_dec decA a l); simpl; auto; discriminate.
  Qed.
End NoDup.

Section Forall.
  Variables (A B C: Type).
  Variable P: A -> Prop.
  Variable P2: A -> B -> Prop.

  Lemma Forall2_length : forall xs ys,
    Forall2 P2 xs ys ->
    length xs = length ys.
  Proof. induction 1; cbn; auto. Qed.

  Lemma Forall_map : forall (f: B -> A) xs,
    Forall P (map f xs) <-> Forall (fun x => P (f x)) xs.
  Proof.
    split; induction xs; cbn; intros * Hall; constructor; inv Hall; auto.
  Qed.

  Lemma Forall_combine : forall xs ys,
    length xs = length ys ->
    Forall (fun p => let '(x, y) := p in P2 x y) (List.combine xs ys) <->
    Forall2 (fun x y => P2 x y) xs ys.
  Proof.
    induction xs; destruct ys; cbn in *; try easy; intros Hlen; inv Hlen.
    split; intros Hall; constructor; inv Hall; auto; apply IHxs; auto.
  Qed.

  Lemma Forall2_nth_error : forall xs ys,
    Forall2 P2 xs ys ->
    forall n x y, (n < length xs)%nat ->
      nth_error xs n = Some x ->
      nth_error ys n = Some y ->
      P2 x y.
  Proof.
    induction 1; cbn; intros * Hn Hx Hy; [omega |].
    destruct n; cbn in *; [inv Hx; inv Hy; auto |].
    eapply IHForall2; eauto; omega.
  Qed.

  Lemma Forall2_nth : forall xs ys d d',
    Forall2 P2 xs ys ->
    forall n, (n < length xs)%nat ->
      P2 (nth n xs d) (nth n ys d').
  Proof.
    induction 1; cbn; intros * Hn; [omega |].
    destruct n; auto.
    apply IHForall2; omega.
  Qed.
End Forall.

Section Silly.

(*used to avoid ill-typed term error messages*)
	
Lemma silly_lemma_true : forall {Y} (b : bool) f g pf, b = true ->
  match b as b' return b = b' -> Y with
  | true => f
  | false => g
  end eq_refl = f pf.
Proof.
  intros.
  destruct b.
  rewrite (hedberg bool_dec eq_refl pf); reflexivity.
  discriminate.
Qed.

Lemma silly_lemma_false : forall {Y} (b : bool) f g pf, b = false ->
  match b as b' return b = b' -> Y with
  | true => f
  | false => g
  end eq_refl = g pf.
Proof.
  intros.
  destruct b.
  discriminate.
  rewrite (hedberg bool_dec eq_refl pf); reflexivity.
Qed.

End Silly.

Lemma boundProof sz w:
  w mod 2^sz = w -> w < 2^sz.
Proof.
  intros sth0.
  simpl.
  pose proof (Nat.mod_upper_bound w (2 ^ sz) (@Nat.pow_nonzero 2 sz ltac:(intro; discriminate))) as sth.
  rewrite sth0 in sth.
  auto.
Qed.

Lemma Z_lt_div': forall (a b c : Z), (c > 0)%Z -> (a/c < b/c)%Z -> (a < b)%Z.
Proof.
  intros.
  destruct (Z_ge_lt_dec a b); auto.
  apply (Z_div_ge _ _ _ H) in g.
  exfalso; lia.
Qed.

Lemma Z_lt_div2: forall (a b c : Z), (c > 0)%Z -> (a < b)%Z -> (b mod c = 0)%Z -> (a/c < b/c)%Z.
Proof.
  intros.
  pose proof (Z.div_le_mono a b c ltac:(lia) ltac:(lia)) as sth.
  apply Z_le_lt_eq_dec in sth.
  destruct sth; auto.
  pose proof (Z.mod_eq b c ltac:(lia)) as sth2.
  assert (sth3: (b = c * (b / c))%Z) by lia.
  rewrite sth3 in H0.
  assert (sth4: (c * (a/c) = c * (b/c))%Z) by nia.
  rewrite <- sth4 in *.
  pose proof (Z_mult_div_ge a c H).
  lia.
Qed.

Lemma Z_pow_2_gt_0: forall n, (n >= 0)%Z -> (2 ^ n > 0)%Z.
Proof.
  intros.
  apply Z.lt_gt, Z.pow_pos_nonneg;[lia|].
  lia.
Qed.

Lemma Z_of_nat_pow_2_gt_0: forall n, (2 ^ (Z.of_nat n) > 0)%Z.
Proof.
  intros.
  apply Z.lt_gt, Z.pow_pos_nonneg;[lia|].
  apply Nat2Z.is_nonneg.
Qed.

Lemma Zpow_1_0 : forall b, (Z.pow 2 b = 1)%Z -> b = 0%Z.
Proof.
  repeat intro.
  destruct (Z_lt_le_dec 0 b).
  - specialize (Z.pow_gt_1 2 b) as TMP; destruct TMP; try lia.
  - rewrite Z.le_lteq in l; destruct l; try lia.
    exfalso.
    rewrite (Z.pow_neg_r 2 _ H0) in H; lia.
Qed.

Lemma pow2_of_nat (n : nat) : (2 ^ Z.of_nat n)%Z = Z.of_nat (2 ^ n)%nat.
Proof.
  induction n.
  + simpl. auto.
  + rewrite Nat2Z.inj_succ.
    simpl.
    rewrite Z.pow_succ_r; try lia.
Qed.

Lemma Zpow_of_nat : forall n, Z.of_nat (2 ^ n) = (2 ^ Z.of_nat n)%Z.
Proof.
  induction n; auto.
  rewrite Nat2Z.inj_succ, <- Z.add_1_l.
  rewrite Z.pow_add_r; try lia.
  rewrite <-IHn.
  rewrite Nat.pow_succ_r', Nat2Z.inj_mul; auto.
Qed.

Lemma Zpow_1_le (a b : Z) :
  (1 <= a)%Z ->
  (0 <= b)%Z ->
  (1 <= a ^b)%Z.
Proof.
  intros.
  apply Zle_lt_or_eq in H.
  destruct H.
  - specialize (Z.pow_gt_lin_r _ _ H H0) as P0.
    lia.
  - rewrite <- H.
    rewrite Z.pow_1_l.
    lia.
    auto.
Qed.

Lemma Zpow_mul_le (a b : Z) :
  (0 <= a)%Z ->
  (0 <= b)%Z ->
  (2 ^ a <= 2 ^ b * 2 ^ a)%Z.
Proof.
  intros.
  rewrite <-(Z.mul_1_l (2^a)) at 1. 
  assert (1 <= 2)%Z.
  { lia. }
  specialize (Zpow_1_le H1 H0).
  intros.
  apply Zmult_lt_0_le_compat_r.
  apply Z.pow_pos_nonneg.
  lia. auto. auto.
Qed.

Lemma Zpow_add_sub (a b : Z) :
  (0 <= a)%Z ->
  (0 <= b)%Z ->
  (2 ^ (a + b) = (2 ^ a * 2 ^ b - 2 ^ b) + 2 ^ b)%Z.
Proof.
  intros.
  rewrite Z.pow_add_r; lia.
Qed.

Lemma Zmul_sub (a b c : Z) :
  (0 <= b)%Z ->
  (0 <= c)%Z ->
  (0 <= a < 2 ^ b)%Z ->
  (a * 2 ^ c <= (2 ^ b * (2 ^ c) -  1 * (2 ^ c)))%Z.
Proof.
  intros.
  rewrite <-Z.mul_sub_distr_r. apply Z.mul_le_mono_nonneg_r.
  apply Z.pow_nonneg; lia.
  lia.
Qed.

Lemma Zpow_lt_add (a b c : Z) :
  (0 <= c)%Z ->
  (0 <= b)%Z ->
  (0 <=  a < 2 ^ c)%Z ->
  (0 <= a < 2 ^ (b + c))%Z.
Proof.
  intros.
  split.
  destruct H1.
  auto.
  rewrite Z.pow_add_r; auto.
  assert (1 <= 2)%Z. {
    lia. }
  specialize (Zpow_1_le H2 H0) as P0.
  destruct H1.
  specialize (Zpow_mul_le H H0) as P1.
  lia.
Qed.

Lemma Zmul_add_0_lt (a a' b c : Z) :
  (0 <= a)%Z ->
  (0 <= b)%Z ->
  (0 <= c)%Z ->
  (0 <= a')%Z ->
  (0 <= a < 2 ^ b)%Z ->
  (0 <= a' < 2 ^ c)%Z ->
  (0 <= a' < 2 ^ (b + c))%Z ->
  (0 <= (a * 2 ^ c + a') < 2 ^ (b + c))%Z.
Proof.
  intros.
  split.
  apply Z.add_nonneg_nonneg; auto.
  specialize (Z.pow_nonneg 2 (c)) as P0.
  assert (0 <= 2)%Z; [lia|].
  specialize (P0 H6).
  apply Z.mul_nonneg_nonneg; auto.
  specialize(Zpow_lt_add H1 H0 H4); intros.
  specialize(Zmul_sub H0 H1 H3); intros.
  rewrite Z.mul_1_l in H7.
  specialize (Zmul_sub H0 H1 H3); intros.
  specialize (Zpow_add_sub H0 H1); intros.
  rewrite H9.
  lia.
Qed.

Lemma Nat_mod_factor a b c:
  b <> 0 ->
  c <> 0 ->
  (a mod (b * c)) mod b = a mod b.
Proof.
  intros.
  pose proof (Nat.mod_mul_r a _ _ H H0).
  rewrite H1.
  rewrite Nat.add_mod_idemp_l by auto.
  rewrite Nat.add_mod by auto.
  assert (sth: b * ((a/b) mod c) = (a/b) mod c * b) by (apply Nat.mul_comm).
  rewrite sth.
  rewrite Nat.mod_mul by auto.
  rewrite Nat.add_0_r.
  rewrite Nat.mod_mod by auto.
  auto.
Qed.

Lemma Nat_mod_factor' a b c d:
  b <> 0 -> c <> 0 -> d = b * c -> (a mod d) mod b = a mod b.
Proof.
  pose proof (@Nat_mod_factor a b c).
  intros.
  subst.
  eapply H; eauto.
Qed.

Lemma mod_sub a b c:
  c > 0 ->
  a >= b * c ->
  (a - b * c) mod c = a mod c.
Proof.
  intros.
  assert (sth: a - b * c + b * c = a) by lia.
  rewrite <- sth at 2.
  rewrite Nat.mod_add by lia.
  auto.
Qed.

Fixpoint mod2 (n : nat) : bool :=
  match n with
  | 0 => false
  | 1 => true
  | S (S n') => mod2 n'
  end.

Ltac rethink :=
  match goal with
  | [ H : ?f ?n = _ |- ?f ?m = _ ] => replace m with n; simpl; auto
  end.

Theorem mod2_S_double : forall n, mod2 (S (2 * n)) = true.
  induction n; simpl; intuition; rethink.
Qed.

Theorem mod2_double : forall n, mod2 (2 * n) = false.
  induction n; simpl; intuition; rewrite <- plus_n_Sm; rethink.
Qed.

Theorem div2_double : forall n, Nat.div2 (2 * n) = n.
Proof.
  induction n; simpl; intuition; rewrite <- plus_n_Sm; f_equal; rethink.
Qed.

Theorem div2_S_double : forall n, Nat.div2 (S (2 * n)) = n.
  induction n; simpl; intuition; f_equal; rethink.
Qed.

Fixpoint Npow2 (n : nat) : N :=
  match n with
  | O => 1
  | S n' => 2 * Npow2 n'
  end%N.

Theorem untimes2 : forall n, n + (n + 0) = 2 * n.
  auto.
Qed.

Section strong.
  Variable P : nat -> Prop.

  Hypothesis PH : forall n, (forall m, m < n -> P m) -> P n.

  Lemma strong' : forall n m, m <= n -> P m.
    induction n; simpl; intuition; apply PH; intuition.
    elimtype False; omega.
  Qed.

  Theorem strong : forall n, P n.
    intros; eapply strong'; eauto.
  Qed.
End strong.

Theorem div2_odd : forall n,
    mod2 n = true
    -> n = S (2 * Nat.div2 n).
  induction n as [n] using strong; simpl; intuition.

  destruct n as [|n]; simpl in *; intuition.
  discriminate.
  destruct n as [|n]; simpl in *; intuition.
  do 2 f_equal.
  replace (Nat.div2 n + S (Nat.div2 n + 0)) with (S (Nat.div2 n + (Nat.div2 n + 0))); auto.
Qed.

Theorem div2_even : forall n,
    mod2 n = false
    -> n = 2 * Nat.div2 n.
  induction n as [n] using strong; simpl; intuition.

  destruct n as [|n]; simpl in *; intuition.
  destruct n as [|n]; simpl in *; intuition.
  discriminate.
  f_equal.
  replace (Nat.div2 n + S (Nat.div2 n + 0)) with (S (Nat.div2 n + (Nat.div2 n + 0))); auto.
Qed.

Theorem drop_mod2 : forall n k,
    2 * k <= n
    -> mod2 (n - 2 * k) = mod2 n.
  induction n as [n] using strong; intros.

  do 2 (destruct n; simpl in *; repeat rewrite untimes2 in *; intuition).

  destruct k; simpl in *; intuition.

  destruct k; simpl; intuition.
  rewrite <- plus_n_Sm.
  repeat rewrite untimes2 in *.
  simpl; auto.
  apply H; omega.
Qed.

Theorem div2_minus_2 : forall n k,
    2 * k <= n
    -> Nat.div2 (n - 2 * k) = Nat.div2 n - k.
  induction n as [n] using strong; intros.

  do 2 (destruct n; simpl in *; intuition; repeat rewrite untimes2 in *).
        destruct k; simpl in *; intuition.

        destruct k; simpl in *; intuition.
        rewrite <- plus_n_Sm.
        apply H; omega.
        Qed.

Theorem div2_bound : forall k n,
  2 * k <= n
  -> k <= Nat.div2 n.
  intros ? n H; case_eq (mod2 n); intro Heq.

  rewrite (div2_odd _ Heq) in H.
  omega.

  rewrite (div2_even _ Heq) in H.
  omega.
  Qed.

Lemma two_times_div2_bound: forall n, 2 * Nat.div2 n <= n.
Proof.
  eapply strong. intros n IH.
  destruct n.
  - constructor.
  - destruct n.
    + simpl. constructor. constructor.
    + simpl (Nat.div2 (S (S n))).
      specialize (IH n). omega.
Qed.

Lemma div2_compat_lt_l: forall a b, b < 2 * a -> Nat.div2 b < a.
Proof.
  induction a; intros.
  - omega.
  - destruct b.
    + simpl. omega.
    + destruct b.
      * simpl. omega.
      * simpl. apply lt_n_S. apply IHa. omega.
Qed.

(* otherwise b is made implicit, while a isn't, which is weird *)
Arguments div2_compat_lt_l {_} {_} _.

Lemma pow2_add_mul: forall a b,
    Nat.pow 2 (a + b) = (Nat.pow 2 a) * (Nat.pow 2 b).
Proof.
  induction a; destruct b; firstorder; simpl.
  repeat rewrite Nat.add_0_r.
  rewrite Nat.mul_1_r; auto.
  repeat rewrite Nat.add_0_r.
  rewrite IHa.
  simpl.
  repeat rewrite Nat.add_0_r.
  rewrite Nat.mul_add_distr_r; auto.
Qed.

Lemma mult_pow2_bound: forall a b x y,
    x < Nat.pow 2 a -> y < Nat.pow 2 b -> x * y < Nat.pow 2 (a + b).
Proof.
  intros.
  rewrite pow2_add_mul.
  apply Nat.mul_lt_mono_nonneg; omega.
Qed.

Lemma mult_pow2_bound_ex: forall a c x y,
    x < Nat.pow 2 a -> y < Nat.pow 2 (c - a) -> c >= a -> x * y < Nat.pow 2 c.
Proof.
  intros.
  replace c with (a + (c - a)) by omega.
  apply mult_pow2_bound; auto.
Qed.

Lemma lt_mul_mono' : forall c a b,
    a < b -> a < b * (S c).
Proof.
  induction c; intros.
  rewrite Nat.mul_1_r; auto.
  rewrite Nat.mul_succ_r.
  apply lt_plus_trans.
  apply IHc; auto.
Qed.

Lemma lt_mul_mono : forall a b c,
    c <> 0 -> a < b -> a < b * c.
Proof.
  intros.
  replace c with (S (c - 1)) by omega.
  apply lt_mul_mono'; auto.
Qed.

Lemma zero_lt_pow2 : forall sz, 0 < Nat.pow 2 sz.
Proof.
  induction sz; simpl; omega.
Qed.

Lemma one_lt_pow2:
  forall n,
    1 < Nat.pow 2 (S n).
Proof.
  intros.
  induction n.
  simpl; omega.
  remember (S n); simpl.
  omega.
Qed.

Lemma one_le_pow2 : forall sz, 1 <= Nat.pow 2 sz.
Proof.
  intros. pose proof (zero_lt_pow2 sz). omega.
Qed.

Lemma pow2_ne_zero: forall n, Nat.pow 2 n <> 0.
Proof.
  intros.
  pose proof (zero_lt_pow2 n).
  omega.
Qed.

Lemma mul2_add : forall n, n * 2 = n + n.
Proof.
  induction n; firstorder.
Qed.

Lemma pow2_le_S : forall sz, (Nat.pow 2 sz) + 1 <= Nat.pow 2 (sz + 1).
Proof.
  induction sz; simpl; auto.
  repeat rewrite Nat.add_0_r.
  rewrite pow2_add_mul.
  repeat rewrite mul2_add.
  pose proof (zero_lt_pow2 sz).
  omega.
Qed.

Lemma pow2_bound_mono: forall a b x,
    x < Nat.pow 2 a -> a <= b -> x < Nat.pow 2 b.
Proof.
  intros.
  replace b with (a + (b - a)) by omega.
  rewrite pow2_add_mul.
  apply lt_mul_mono; auto.
  pose proof (zero_lt_pow2 (b - a)).
  omega.
Qed.

Lemma pow2_inc : forall n m,
    0 < n -> n < m ->
    Nat.pow 2 n < Nat.pow 2 m.
Proof.
  intros.
  generalize dependent n; intros.
  induction m; simpl.
  intros. inversion H0.
  unfold lt in H0.
  rewrite Nat.add_0_r.
  inversion H0.
  apply Nat.lt_add_pos_r.
  apply zero_lt_pow2.
  apply Nat.lt_trans with (Nat.pow 2 m).
  apply IHm.
  exact H2.
  apply Nat.lt_add_pos_r.
  apply zero_lt_pow2.
Qed.

Lemma pow2_S: forall x, Nat.pow 2 (S x) = 2 * Nat.pow 2 x.
Proof. intros. reflexivity. Qed.

Lemma mod2_S_S : forall n,
    mod2 (S (S n)) = mod2 n.
Proof.
  intros.
  destruct n; auto; destruct n; auto.
Qed.

Lemma mod2_S_not : forall n,
    mod2 (S n) = if (mod2 n) then false else true.
Proof.
  intros.
  induction n; auto.
  rewrite mod2_S_S.
  destruct (mod2 n); replace (mod2 (S n)); auto.
Qed.

Lemma mod2_S_eq : forall n k,
    mod2 n = mod2 k ->
    mod2 (S n) = mod2 (S k).
Proof.
  intros.
  do 2 rewrite mod2_S_not.
  rewrite H.
  auto.
Qed.

Theorem drop_mod2_add : forall n k,
    mod2 (n + 2 * k) = mod2 n.
Proof.
  intros.
  induction n.
  simpl.
  rewrite Nat.add_0_r.
  replace (k + k) with (2 * k) by omega.
  apply mod2_double.
  replace (S n + 2 * k) with (S (n + 2 * k)) by omega.
  apply mod2_S_eq; auto.
Qed.

Lemma mod2sub: forall a b,
    b <= a ->
    mod2 (a - b) = xorb (mod2 a) (mod2 b).
Proof.
  intros. remember (a - b) as c. revert dependent b. revert a. revert c.
  change (forall c,
             (fun c => forall a b, b <= a -> c = a - b -> mod2 c = xorb (mod2 a) (mod2 b)) c).
  apply strong.
  intros c IH a b AB N.
  destruct c.
  - assert (a=b) by omega. subst. rewrite Bool.xorb_nilpotent. reflexivity.
  - destruct c.
    + assert (a = S b) by omega. subst a. simpl (mod2 1). rewrite mod2_S_not.
      destruct (mod2 b); reflexivity.
    + destruct a; [omega|].
      destruct a; [omega|].
      simpl.
      apply IH; omega.
Qed.

Theorem mod2_pow2_twice: forall n,
    mod2 (Nat.pow 2 n + (Nat.pow 2 n + 0)) = false.
Proof.
  intros.
  replace (Nat.pow 2 n + (Nat.pow 2 n + 0)) with (2 * Nat.pow 2 n) by omega.
  apply mod2_double.
Qed.

Theorem div2_plus_2 : forall n k,
    Nat.div2 (n + 2 * k) = Nat.div2 n + k.
Proof.
  induction n; intros.
  simpl.
  rewrite Nat.add_0_r.
  replace (k + k) with (2 * k) by omega.
  apply div2_double.
  replace (S n + 2 * k) with (S (n + 2 * k)) by omega.
  destruct (Even.even_or_odd n).
  - rewrite <- even_div2.
    rewrite <- even_div2 by auto.
    apply IHn.
    apply Even.even_even_plus; auto.
    apply Even.even_mult_l; repeat constructor.

  - rewrite <- odd_div2.
    rewrite <- odd_div2 by auto.
    rewrite IHn.
    omega.
    apply Even.odd_plus_l; auto.
    apply Even.even_mult_l; repeat constructor.
Qed.

Lemma pred_add:
  forall n, n <> 0 -> pred n + 1 = n.
Proof.
  intros; rewrite pred_of_minus; omega.
Qed.

Lemma pow2_zero: forall sz, (Nat.pow 2 sz > 0)%nat.
Proof.
  induction sz; simpl; auto; omega.
Qed.

Section omega_compat.

  Ltac omega ::= lia.

  Theorem Npow2_nat : forall n, nat_of_N (Npow2 n) = Nat.pow 2 n.
    induction n as [|n IHn]; simpl; intuition.
    rewrite <- IHn; clear IHn.
    case_eq (Npow2 n); intuition.
  Qed.

End omega_compat.

Hint Rewrite Nplus_0_r nat_of_Nsucc nat_of_Nplus nat_of_Nminus
     N_of_nat_of_N nat_of_N_of_nat
     nat_of_P_o_P_of_succ_nat_eq_succ nat_of_P_succ_morphism : N.


Theorem nat_of_N_eq : forall n m,
    nat_of_N n = nat_of_N m
    -> n = m.
  intros ? ? H; apply (f_equal N_of_nat) in H;
    autorewrite with N in *; assumption.
Qed.


Theorem pow2_N : forall n, Npow2 n = N.of_nat (Nat.pow 2 n).
Proof.
  intro n. apply nat_of_N_eq. rewrite Nat2N.id. apply Npow2_nat.
Qed.

Lemma Z_of_N_Npow2: forall n, Z.of_N (Npow2 n) = (2 ^ Z.of_nat n)%Z.
Proof.
  intros.
  rewrite pow2_N.
  rewrite nat_N_Z.
  rewrite Zpow_of_nat.
  reflexivity.
Qed.

Lemma pow2_S_z:
  forall n, Z.of_nat (Nat.pow 2 (S n)) = (2 * Z.of_nat (Nat.pow 2 n))%Z.
Proof.
  intros.
  replace (2 * Z.of_nat (Nat.pow 2 n))%Z with
      (Z.of_nat (Nat.pow 2 n) + Z.of_nat (Nat.pow 2 n))%Z by omega.
  simpl.
  repeat rewrite Nat2Z.inj_add.
  ring.
Qed.

Lemma pow2_le:
  forall n m, (n <= m)%nat -> (Nat.pow 2 n <= Nat.pow 2 m)%nat.
Proof.
  intros.
  assert (exists s, n + s = m) by (exists (m - n); omega).
  destruct H0; subst.
  rewrite pow2_add_mul.
  pose proof (pow2_zero x).
  replace (Nat.pow 2 n) with (Nat.pow 2 n * 1) at 1 by omega.
  apply mult_le_compat_l.
  omega.
Qed.

Lemma Zabs_of_nat:
  forall n, Z.abs (Z.of_nat n) = Z.of_nat n.
Proof.
  unfold Z.of_nat; intros.
  destruct n; auto.
Qed.

Lemma Npow2_not_zero:
  forall n, Npow2 n <> 0%N.
Proof.
  induction n; simpl; intros; [discriminate|].
  destruct (Npow2 n); auto.
  discriminate.
Qed.

Lemma Npow2_S:
  forall n, Npow2 (S n) = (Npow2 n + Npow2 n)%N.
Proof.
  simpl; intros.
  destruct (Npow2 n); auto.
  rewrite <-Pos.add_diag.
  reflexivity.
Qed.

Lemma Npow2_pos: forall a,
    (0 < Npow2 a)%N.
Proof.
  intros.
  destruct (Npow2 a) eqn: E.
  - exfalso. apply (Npow2_not_zero a). assumption.
  - constructor.
Qed.

Lemma minus_minus: forall a b c,
    c <= b <= a ->
    a - (b - c) = a - b + c.
Proof. intros. omega. Qed.

Lemma even_odd_destruct: forall n,
    (exists a, n = 2 * a) \/ (exists a, n = 2 * a + 1).
Proof.
  induction n.
  - left. exists 0. reflexivity.
  - destruct IHn as [[a E] | [a E]].
    + right. exists a. omega.
    + left. exists (S a). omega.
Qed.

Lemma mul_div_undo: forall i c,
    c <> 0 ->
    c * i / c = i.
Proof.
  intros.
  pose proof (Nat.div_mul_cancel_l i 1 c) as P.
  rewrite Nat.div_1_r in P.
  rewrite Nat.mul_1_r in P.
  apply P; auto.
Qed.

Lemma mod_add_r: forall a b,
    b <> 0 ->
    (a + b) mod b = a mod b.
Proof.
  intros. rewrite <- Nat.add_mod_idemp_r by omega.
  rewrite Nat.mod_same by omega.
  rewrite Nat.add_0_r.
  reflexivity.
Qed.

Lemma mod2_cases: forall (n: nat), n mod 2 = 0 \/ n mod 2 = 1.
Proof.
  intros.
  assert (n mod 2 < 2). {
    apply Nat.mod_upper_bound. congruence.
  }
  omega.
Qed.

Lemma div_mul_undo: forall a b,
    b <> 0 ->
    a mod b = 0 ->
    a / b * b = a.
Proof.
  intros.
  pose proof Nat.div_mul_cancel_l as A. specialize (A a 1 b).
  replace (b * 1) with b in A by omega.
  rewrite Nat.div_1_r in A.
  rewrite mult_comm.
  rewrite <- Nat.divide_div_mul_exact; try assumption.
  - apply A; congruence.
  - apply Nat.mod_divide; assumption.
Qed.

Lemma Smod2_1: forall k, S k mod 2 = 1 -> k mod 2 = 0.
Proof.
  intros k C.
  change (S k) with (1 + k) in C.
  rewrite Nat.add_mod in C by congruence.
  pose proof (Nat.mod_upper_bound k 2).
  assert (k mod 2 = 0 \/ k mod 2 = 1) as E by omega.
  destruct E as [E | E]; [assumption|].
  rewrite E in C. simpl in C. discriminate.
Qed.

Lemma mod_0_r: forall (m: nat),
    m mod 0 = 0.
Proof.
  intros. reflexivity.
Qed.

Lemma sub_mod_0: forall (a b m: nat),
    a mod m = 0 ->
    b mod m = 0 ->
    (a - b) mod m = 0.
Proof.
  intros. assert (m = 0 \/ m <> 0) as C by omega. destruct C as [C | C].
  - subst. apply mod_0_r.
  - assert (a - b = 0 \/ b < a) as D by omega. destruct D as [D | D].
    + rewrite D. apply Nat.mod_0_l. assumption.
    + apply Nat2Z.inj. simpl.
      rewrite Zdiv.mod_Zmod by assumption.
      rewrite Nat2Z.inj_sub by omega.
      rewrite Zdiv.Zminus_mod.
      rewrite <-! Zdiv.mod_Zmod by assumption.
      rewrite H. rewrite H0.
      apply Z.mod_0_l.
      omega.
Qed.

Lemma mul_div_exact: forall (a b: nat),
    b <> 0 ->
    a mod b = 0 ->
    b * (a / b) = a.
Proof.
  intros. edestruct Nat.div_exact as [_ P]; [eassumption|].
  specialize (P H0). symmetry. exact P.
Qed.


Lemma Z_add_sub_distr : forall a b c,
    ((a - (b + c)) = a - b - c)%Z.
Proof.
  intros.
  lia.
Qed.

Lemma Zpow_successor : forall x (y : nat),
    (0 <= x < 2 ^ (Z.of_nat y))%Z ->
    (0 <= x < 2 ^ Z.of_nat(y + 1))%Z.
Proof.
  intros.
  inversion H.
  split.
  * auto.
  * rewrite Nat2Z.inj_add.
    rewrite Z.add_comm.
    apply Zpow_lt_add.
    lia.
    lia.
    lia.
Qed.

Lemma Zpow_successor_itself : forall  (y : nat),
    (0 <= 2 ^ (Z.of_nat y) < 2 ^ Z.of_nat(y + 1))%Z.
Proof.
  intros.
  split.
  * rewrite (Z.pow_nonneg 2 (Z.of_nat y)).
    lia.
    lia.
  * apply Z.pow_lt_mono_r.
    lia.
    lia.
    lia.
Qed.

Lemma pow2_gt_1 n : (n > 0)%nat -> (2 ^ n > 1)%nat.
Proof.
  induction n.
  + lia.
  + intros ?.
    apply one_lt_pow2.
Qed.

Lemma nat_mul_cancel_l :
  forall a b c, c <> 0 ->
                c * a = c * b ->
                a = b.
Proof.
  induction a; intros.
  - rewrite <- mult_n_O in H0.
    apply eq_sym, mult_is_O in H0.
    destruct H0; subst; tauto.
  - induction b.
    + exfalso; rewrite <- mult_n_O in H0.
      destruct (mult_is_O _ _ H0); lia.
    + repeat rewrite Nat.mul_succ_r in H0.
      rewrite Nat.add_cancel_r in H0.
      rewrite (IHa _ _ H H0); reflexivity.
Qed.

Lemma Zdiv_div (n m : Z) :
  (0 < m)%Z ->
  (0 <= n)%Z ->
  Z.to_nat (n / m) = (Z.to_nat n /Z.to_nat m).
Proof.
  intros.
  rewrite <- (Z2Nat.id n) at 1; auto.
  rewrite <- (Z2Nat.id m) at 1; [|lia].
  rewrite <- div_Zdiv.
  - rewrite Nat2Z.id; reflexivity.
  - rewrite <- Z2Nat.inj_0; intro.
    rewrite Z2Nat.inj_iff in H1; subst; lia.
Qed.

Lemma Zmod_mod' (n m : Z) :
  (0 < m)%Z ->
  (0 <= n)%Z ->
  (Z.to_nat (n mod m) = (Z.to_nat n) mod (Z.to_nat m)).
Proof.
  intros.
  rewrite <- (Z2Nat.id n) at 1; auto.
  rewrite <- (Z2Nat.id m) at 1; [|lia].
  rewrite <- mod_Zmod.
  - rewrite Nat2Z.id; reflexivity.
  - rewrite <- Z2Nat.inj_0; intro.
    rewrite Z2Nat.inj_iff in H1; subst; lia.
Qed.

Lemma pow_divide :
  forall sz1 sz2,
    (2 ^ Z.of_nat sz1 | 2 ^ Z.of_nat (sz1 + sz2))%Z
    /\ (2 ^ Z.of_nat sz2 | 2 ^ Z.of_nat (sz1 + sz2))%Z.
Proof.
  split; erewrite Nat2Z.inj_add, Z.pow_add_r; try apply Nat2Z.is_nonneg; eexists; [rewrite Z.mul_comm|]; reflexivity.
Qed.


Lemma diag :
  forall n, n - n = 0.
Proof. intros. lia. Qed.


Lemma Natlt_0 :
  forall n,
    n <= 0 <-> n = 0.
Proof.
  induction n; intros; try lia.
Qed.

Lemma equal_expWidth_sigWidth:
  forall s, 2^s + 4 > s + 2.
Proof.
  induction s; simpl; auto.
  rewrite Nat.add_0_r.
  pose proof (pow2_zero s).
  Omega.omega.
Qed.

Lemma one_lt_pow2' : forall n, n > 0 -> 1 < 2 ^ n.
Proof.
  intros; specialize (pow2_gt_1 H); auto.
Qed.

Lemma lt_minus' :
  forall a b c : nat, b <= a -> b < c -> a < c -> a - b < c.
Proof. intros. lia. Qed.

Lemma if_same A (x: A) (p: bool): (if p then x else x) = x.
Proof.
  destruct p; auto.
Qed.

Lemma mod_factor a b c:
  b <> 0 ->
  c <> 0 ->
  (a mod (b * c)) mod b = a mod b.
Proof.
  intros.
  pose proof (Nat.mod_mul_r a _ _ H H0).
  rewrite H1.
  rewrite Nat.add_mod_idemp_l by auto.
  rewrite Nat.add_mod by auto.
  assert (sth: b * ((a/b) mod c) = (a/b) mod c * b) by (apply Nat.mul_comm).
  rewrite sth.
  rewrite Nat.mod_mul by auto.
  rewrite Nat.add_0_r.
  rewrite Nat.mod_mod by auto.
  auto.
Qed.

Lemma mod_factor' a b c d:
  b <> 0 -> c <> 0 -> d = b * c -> (a mod d) mod b = a mod b.
Proof. 
  pose proof (@mod_factor a b c).
  intros.
  subst.
  eapply H; eauto.
Qed.

Lemma if_bool_2 A (x y: A) (p1 p2: bool):
  p1 = p2 ->
  (if p1 then x else y) = (if p2 then x else y).
Proof.
  intros sth.
  rewrite sth.
  auto.
Qed.

Lemma mod_cancel_l:
  forall a b x n,
    n <> 0 ->
    a mod n = b mod n ->
    (x + a) mod n = (x + b) mod n.
Proof.
  intros.
  rewrite <- Nat.add_mod_idemp_r; auto.
  rewrite H0.
  rewrite Nat.add_mod_idemp_r; auto.
Qed.

Lemma pow2_1_iff_0 n:
  2 ^ n = 1 <-> n = 0.
Proof.
  induction n; split; intro; try lia.
  simpl. reflexivity.
  destruct IHn.
  pose proof (one_lt_pow2 n) as sth1.
  rewrite H in sth1.
  apply False_ind.
  inversion sth1.
  inversion H3.
Qed.

Lemma pow2_lt_S n:
  n > 0 ->
  2 ^ n + 1 < 2 ^ (n + 1).
Proof.
  pose proof (pow2_le_S n) as sth.
  apply Nat.lt_eq_cases in sth.
  destruct sth; auto.
  intro sth.
  apply False_ind.
  apply Nat.add_sub_eq_l in H.
  pose proof (pow2_1_iff_0 n) as sth1.
  replace (2 ^ n) with (2 ^ n * 1) in H by lia.
  rewrite pow2_add_mul in H.
  rewrite <- Nat.mul_sub_distr_l in H.
  simpl in H.
  destruct sth1 as [sth2 sth3].
  rewrite sth2 in sth; lia.
Qed.

Lemma pow2_lt_2 n:
  1 < n -> 2 < 2 ^ n.
Proof.
  intro sth.
  induction n.
  inversion sth.
  simpl.
  assert (sth1: n = 1 \/ n > 1) by lia.
  destruct sth1.
  rewrite H.
  simpl.
  auto.
  simpl.
  apply Nat.lt_lt_add_l.
  rewrite Nat.add_0_r.
  lia.
Qed.

Lemma pow2_lt_pow2_S n : 2 ^ n < 2 ^ (n + 1).
Proof.
  rewrite Nat.add_1_r.
  simpl.
  assert (0 < 2 ^ n) by apply zero_lt_pow2.
  lia.
Qed.
