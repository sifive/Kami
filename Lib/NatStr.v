Require Import Kami.Syntax.

Section nat_string.
  Unset Implicit Arguments.

  (*
    Accepts two arguments: radix and ns; and returns: ns[0] + radix *
    ns[1] + radix^2 * ns[2] + ... radix^n * ns[n]

    Ex: nat_decomp_nat 2 [1; 0; 1; 1] = 13.
  *)
  Local Fixpoint nat_decomp_nat (radix : nat) (ns : list nat) : nat
    := match ns with
       | [] => 0
       | m :: ms => (radix * nat_decomp_nat radix ms) + m
       end.

  Local Fixpoint nat_decomp_prod (x : nat) (ns : list nat) : list nat
    := match ns with
       | [] => []
       | m :: ms => x * m :: nat_decomp_prod x ms
       end.

  (* 0 = Nat.div x y ==> x < y ==> x = x mod y *)
  Lemma div0_mod : forall x y : nat, y <> 0 -> 0 = Nat.div x y -> x = x mod y.
  Proof.
    exact
      (fun x y H H0
        => eq_sym (Nat.mod_small x y
             (proj1 (Nat.div_small_iff x y H)
               (eq_sym H0)))).
  Qed.

  Local Definition nat_decomp
    (radix : nat) (* radix minus 2 *)
    (n : nat)
    :  {ms : list nat |
         Forall (fun m => m < (S (S radix))) ms /\
         n = nat_decomp_nat (S (S radix)) ms}
    := Fix_F
         (fun n
           => {ms : list nat |
                Forall (fun m => m < (S (S radix))) ms /\
                n = nat_decomp_nat (S (S radix)) ms})
         (fun n (F : forall r, r < n -> {ms : list nat | Forall (fun m => m < (S (S radix))) ms /\ r = nat_decomp_nat (S (S radix)) ms})
           => nat_rec
                (fun q
                  => q = Nat.div n (S (S radix)) ->
                     {ms : list nat |
                       Forall (fun m => m < (S (S radix))) ms /\
                       n = nat_decomp_nat (S (S radix)) ms})
                (fun H : 0 = Nat.div n (S (S radix))
                  => let H0 : n = nat_decomp_nat (S (S radix)) [n mod (S (S radix))]
                       := ltac:(
                            lazy [nat_decomp_nat list_rec list_rect];
                            rewrite (Nat.mul_0_r (S (S radix)));
                            rewrite (Nat.add_0_l _);
                            apply (div0_mod n (S (S radix)) (Nat.neq_succ_0 (S radix)) H)) in
                     exist
                       (fun ms
                         => Forall (fun m => m < (S (S radix))) ms /\
                            n = nat_decomp_nat (S (S radix)) ms)
                       [n mod (S (S radix))]
                       (conj
                         (Forall_cons (n mod (S (S radix))) 
                           (Nat.mod_upper_bound n (S (S radix)) (Nat.neq_succ_0 (S radix)))
                           (Forall_nil (fun m => m < S (S radix))))
                         H0))
                (fun q _ (H : S q = Nat.div n (S (S radix)))
                  => let (ms, H0)
                       := F (S q)
                            (eq_ind_r
                              (fun x => x < n)
                              (Nat.div_lt n (S (S radix))
                                (or_ind
                                  (fun H0 : 0 < n => H0)
                                  (fun H0 : 0 = n
                                    => False_ind (0 < n)
                                         (let H2 : Nat.div n (S (S radix)) = 0
                                            := eq_ind
                                                 0
                                                 (fun x => Nat.div x (S (S radix)) = 0)
                                                 (Nat.div_0_l (S (S radix)) (Nat.neq_succ_0 (S radix)))
                                                 n
                                                 H0 in
                                          let H1 : S q = 0
                                            := eq_ind_r (fun x => x = 0) H2 H in
                                          Nat.neq_succ_0 q H1))
                                  ((proj1 (Nat.lt_eq_cases 0 n))
                                    (Nat.le_0_l n)))
                                (le_n_S 1 (S radix) (le_n_S 0 radix (Nat.le_0_l radix)))) 
                              H) in
                     let xs := n mod (S (S radix)) :: ms in
                     let H1 : n = nat_decomp_nat (S (S radix)) xs
                       := ltac:(
                            unfold xs;
                            lazy [nat_decomp_nat list_rec list_rect];
                            fold (nat_decomp_nat (S (S radix)));
                            rewrite <- (proj2 H0);
                            rewrite H;
                            rewrite <- (Nat.div_mod n (S (S radix)) (Nat.neq_succ_0 (S radix)));
                            reflexivity) in
                     let H2 : Forall (fun m => m < S (S radix)) xs
                       := Forall_cons (n mod S (S radix))
                           (Nat.mod_upper_bound n (S (S radix)) (Nat.neq_succ_0 (S radix)))
                           (proj1 H0) in
                     exist _ xs (conj H2 H1))
                (Nat.div n (S (S radix)))
                eq_refl)%nat
         (lt_wf n).

  (* Every function that has an inverse is injective. *)
  Local Theorem inv_inj
    : forall (A B : Type) (f : A -> B) (g : B -> A),
        (forall x : A, g (f x) = x) ->
        (forall x y : A, f x = f y -> x = y).
  Proof.
    intros A b f g Hg x y Hxy.
    rewrite <- (Hg x).
    rewrite <- (Hg y).
    rewrite Hxy.
    reflexivity.
  Qed.

  Local Theorem nat_decomp_inj
    (radix : nat) (* radix minus 2 *)
    :  forall n m : nat, proj1_sig (nat_decomp radix n) = proj1_sig (nat_decomp radix m) -> n = m.
  Proof.
    exact
      (inv_inj _ _
        (fun x => proj1_sig (nat_decomp radix x))
        (nat_decomp_nat (S (S radix)))  
        (fun x => eq_sym (proj2 (proj2_sig (nat_decomp radix x))))).
  Qed.

  Local Open Scope char_scope.

  Local Fixpoint nat_decomp_chars
    (radix : nat) (* radix minus 2 *)
    (encoding : forall n, n < S (S radix) -> ascii)
    (ns : list nat)
    :  Forall (fun n => n < S (S radix)) ns -> list ascii
    := match ns with
       | [] => fun _ => []
       | m :: ms
         => fun H : Forall (fun n => n < S (S radix)) (m :: ms)
              => nat_decomp_chars radix encoding ms (Forall_inv_tail H) ++
                 [encoding m (Forall_inv H)]
       end.

  Local Theorem nat_decomp_chars_inj
    (radix : nat)
    (encoding : forall n, n < S (S radix) -> ascii)
    (encoding_inj : forall n m (Hn : n < S (S radix)) (Hm : m < S (S radix)), encoding n Hn = encoding m Hm -> n = m)
    : forall 
         (ns : list nat)
         (ms : list nat)
         (Hns : Forall (fun n => n < S (S radix)) ns)
         (Hms : Forall (fun m => m < S (S radix)) ms),
         nat_decomp_chars radix encoding ns Hns =
         nat_decomp_chars radix encoding ms Hms ->
         ns = ms.
  Proof.
    exact
      (list_ind
        (fun ns
          => forall
               (ms : list nat)
               (Hns : Forall (fun n => n < S (S radix)) ns)
               (Hms : Forall (fun m => m < S (S radix)) ms),
               nat_decomp_chars radix encoding ns Hns =
               nat_decomp_chars radix encoding ms Hms ->
               ns = ms)
        (list_ind
          (fun ms
            => forall
                 (Hns : Forall (fun n => n < S (S radix)) [])
                 (Hms : Forall (fun m => m < S (S radix)) ms),
                 nat_decomp_chars radix encoding [] Hns =
                 nat_decomp_chars radix encoding ms Hms ->
                 [] = ms)
          (fun _ _ _ => ltac:(reflexivity))
          (fun _ _ _ _ _ H => False_ind _ (app_cons_not_nil _ _ _ H)))
        (fun n ns F
          => list_ind
               (fun ms
                 => forall
                      (Hns : Forall (fun n => n < S (S radix)) (n :: ns))
                      (Hms : Forall (fun m => m < S (S radix)) ms),
                      nat_decomp_chars radix encoding (n :: ns) Hns =
                      nat_decomp_chars radix encoding ms Hms ->
                      (n :: ns) = ms)
               (fun _ _ H => False_ind _ (app_cons_not_nil _ _ _ (eq_sym H)))
               (fun m ms G Hns Hms H
                 => let H0
                      :  ns = ms
                      := F ms
                           (Forall_inv_tail Hns)
                           (Forall_inv_tail Hms)
                           (proj1 (app_inj_tail 
                             (nat_decomp_chars radix encoding ns (Forall_inv_tail Hns))
                             (nat_decomp_chars radix encoding ms (Forall_inv_tail Hms))
                             (encoding n (Forall_inv Hns))
                             (encoding m (Forall_inv Hms))
                             H)) in
                    sumbool_ind
                      (fun _ => _)
                      (fun H1 : n = m
                        => ltac:(rewrite H0; rewrite H1; reflexivity) : (n :: ns) = (m :: ms))
                      (fun H1 : n <> m
                        => let H2
                             :  encoding n (Forall_inv Hns) = encoding m (Forall_inv Hms)
                             := proj2 (app_inj_tail
                                  (nat_decomp_chars radix encoding ns (Forall_inv_tail Hns))
                                  (nat_decomp_chars radix encoding ms (Forall_inv_tail Hms))
                                  (encoding n (Forall_inv Hns))
                                  (encoding m (Forall_inv Hms))
                                  H) in
                           False_ind _
                             (H1 (encoding_inj n m (Forall_inv Hns) (Forall_inv Hms) H2)))
                       (Nat.eq_dec n m)))).
  Qed.

  Local Definition nat_chars
    (radix : nat)
    (encoding : forall n, n < S (S radix) -> ascii)
    (n : nat)
    :  list ascii
    := nat_decomp_chars radix encoding
         (proj1_sig (nat_decomp radix n))
         (proj1 (proj2_sig (nat_decomp radix n))).

  Local Theorem nat_chars_inj
    (radix : nat)
    (encoding : forall n, n < S (S radix) -> ascii)
    (encoding_inj : forall n m (Hn : n < S (S radix)) (Hm : m < S (S radix)), encoding n Hn = encoding m Hm -> n = m)
    :  forall n m : nat, nat_chars radix encoding n = nat_chars radix encoding m -> n = m.
  Proof.
    intros n m H.
    assert ((proj1_sig (nat_decomp radix n)) = (proj1_sig (nat_decomp radix m))).
    apply (nat_decomp_chars_inj radix encoding encoding_inj 
            (proj1_sig (nat_decomp radix n))
            (proj1_sig (nat_decomp radix m))
            (proj1 (proj2_sig (nat_decomp radix n)))
            (proj1 (proj2_sig (nat_decomp radix m)))
            H).
    apply (nat_decomp_inj radix n m H0).
  Qed.
    
  Local Definition nat_string
    (radix : nat)
    (encoding : forall n, n < S (S radix) -> ascii)
    (n : nat)
    :  string
    := string_of_list_ascii (nat_chars radix encoding n).

  Local Lemma string_of_list_ascii_inj
    : forall xs ys : list ascii, string_of_list_ascii xs = string_of_list_ascii ys -> xs = ys.
  Proof.
    exact
      (inv_inj _ _
        string_of_list_ascii
        list_ascii_of_string
        list_ascii_of_string_of_list_ascii).
  Qed.

  Local Theorem nat_string_inj
    (radix : nat)
    (encoding : forall n, n < S (S radix) -> ascii)
    (encoding_inj : forall n m (Hn : n < S (S radix)) (Hm : m < S (S radix)), encoding n Hn = encoding m Hm -> n = m)
    :  forall n m : nat, nat_string radix encoding n = nat_string radix encoding m -> n = m.
  Proof.
    intros n m H.
    assert (nat_chars radix encoding n = nat_chars radix encoding m).
    apply (string_of_list_ascii_inj _ _ H).
    assert ((proj1_sig (nat_decomp radix n)) = (proj1_sig (nat_decomp radix m))).
    apply (nat_decomp_chars_inj radix encoding encoding_inj 
            (proj1_sig (nat_decomp radix n))
            (proj1_sig (nat_decomp radix m))
            (proj1 (proj2_sig (nat_decomp radix n)))
            (proj1 (proj2_sig (nat_decomp radix m)))
            H0).
    apply (nat_decomp_inj radix n m H1).
  Qed.

  Local Ltac notIn H (* In x xs *) := repeat (destruct H; repeat (discriminate; assumption)).

  Local Ltac encoding_NoDup xs
    := lazymatch xs with
       | nil => exact (NoDup_nil ascii)
       | (cons ?X ?XS)%list
         => exact
              (NoDup_cons X 
                (fun H : In X XS => ltac:(notIn H))
                (ltac:(encoding_NoDup XS)))
       end.

  Local Definition decode (encoding : list ascii) (n : nat) : ascii
    := List.nth n encoding " ".

  Local Definition decode_safe (encoding : list ascii) (n : nat) (_ : n < List.length encoding)
    := decode encoding n.

  Local Ltac digit_encoding_inj encoding
    := exact
         (proj1 (NoDup_nth encoding " ") 
            ltac:(encoding_NoDup encoding)
           : forall n m : nat,
               n < List.length encoding ->
               m < List.length encoding ->
               decode encoding n = decode encoding m ->
               n = m).

  Local Ltac encoding_inj radix encoding (* radix = encoding - 2 *)
    := exact
         (nat_string_inj
           radix
           (decode_safe encoding)
           (ltac:(digit_encoding_inj encoding))).

  Local Definition binary_encoding_list : list ascii := ["0"; "1"].

  Definition natToBinStr : nat -> string
    := nat_string 0 (decode_safe binary_encoding_list).

  Definition natToBinStr_inj
    :  forall n m, natToBinStr n = natToBinStr m -> n = m
    := ltac:(encoding_inj 0 ["0"; "1"]%list).

  Local Definition decimal_encoding_list : list ascii
    := ["0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9"].

  Definition natToDecStr : nat -> string
    := nat_string 8 (decode_safe decimal_encoding_list).

  Definition natToDecStr_inj
    :  forall n m, natToDecStr n = natToDecStr m -> n = m
    := ltac:(encoding_inj 8 ["0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9"]%list).

  Local Definition hex_encoding_list : list ascii
    := ["0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9"; "A"; "B"; "C"; "D"; "E"; "F"].

  Definition natToHexStr : nat -> string
    := nat_string 14 (decode_safe hex_encoding_list).

  Definition natToHexStr_inj
    :  forall n m, natToHexStr n = natToHexStr m -> n = m
    := ltac:(encoding_inj 14 ["0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9"; "A"; "B"; "C"; "D"; "E"; "F"]%list).

  Local Close Scope char_scope.

  Local Open Scope string_scope.

  (* Goal (natToHexStr 179 = "B3"). Proof. reflexivity. Qed. *)
  Goal (natToDecStr 179 = "179"). Proof. reflexivity. Qed.
  Goal (natToBinStr 179 = "10110011"). Proof. reflexivity. Qed.

  Local Close Scope string_scope.

  Local Close Scope list.

  Set Implicit Arguments.

End nat_string.

(* The following definitions are DEPRECATED. *)
(*
Section Positive.
  Local Open Scope positive_scope.
  Fixpoint of_pos (p : positive) (rest : string) : string :=
    match p with
    | 1 => String "1" rest
    | 2 => String "2" rest
    | 3 => String "3" rest
    | 4 => String "4" rest
    | 5 => String "5" rest
    | 6 => String "6" rest
    | 7 => String "7" rest
    | 8 => String "8" rest
    | 9 => String "9" rest
    | 10 => String "A" rest
    | 11 => String "B" rest
    | 12 => String "C" rest
    | 13 => String "D" rest
    | 14 => String "E" rest
    | 15 => String "F" rest
    | p'~0~0~0~0 => of_pos p' (String "0" rest)
    | p'~0~0~0~1 => of_pos p' (String "1" rest)
    | p'~0~0~1~0 => of_pos p' (String "2" rest)
    | p'~0~0~1~1 => of_pos p' (String "3" rest)
    | p'~0~1~0~0 => of_pos p' (String "4" rest)
    | p'~0~1~0~1 => of_pos p' (String "5" rest)
    | p'~0~1~1~0 => of_pos p' (String "6" rest)
    | p'~0~1~1~1 => of_pos p' (String "7" rest)
    | p'~1~0~0~0 => of_pos p' (String "8" rest)
    | p'~1~0~0~1 => of_pos p' (String "9" rest)
    | p'~1~0~1~0 => of_pos p' (String "A" rest)
    | p'~1~0~1~1 => of_pos p' (String "B" rest)
    | p'~1~1~0~0 => of_pos p' (String "C" rest)
    | p'~1~1~0~1 => of_pos p' (String "D" rest)
    | p'~1~1~1~0 => of_pos p' (String "E" rest)
    | p'~1~1~1~1 => of_pos p' (String "F" rest)
    end.
  Local Close Scope positive_scope.
  Definition natToHexStr (n : nat) : string :=
    match (BinNat.N.of_nat n) with
    | N0     => "0"
    | Npos p => of_pos p ""
    end.
End Positive.

Definition AddIndexToName name idx := (name ++ "_" ++ natToHexStr idx)%string.

Definition AddIndicesToNames name idxs := List.map (fun x => AddIndexToName name x) idxs.

Fixpoint pos_length(x : positive) : nat :=
  match x with
  | xH => 0
  | xI y => S (pos_length y)
  | xO y => S (pos_length y)
  end.

Lemma string_lemma1 : forall str c d, (str <> "" -> str ++ (String c EmptyString) <> String d EmptyString)%string.
Proof.
  intros.
  destruct str.
  - elim H; reflexivity.
  - destruct str; discriminate.
Qed.

Lemma string_lemma2 : forall str c str', (str ++ String c str' = (str ++ (String c "")) ++ str')%string.
Proof.
  destruct str'.
  - rewrite append_nil; auto.
  - rewrite <- append_assoc; auto.
Qed.

Lemma string_lemma3 : forall str str' c c', (str ++ String c "" = str' ++ String c' "")%string ->
  c = c'.
Proof.
  induction str; intros.
  - destruct str'.
    + inversion H; auto.
    + inversion H.
      * destruct str'; discriminate.
  - destruct str'.
    + inversion H.
      destruct str; discriminate.
    + inversion H.
      eapply IHstr.
      exact H2.
Qed.

Lemma string_lemma4 : forall str1 str2 c c' str3, (str1 ++ (String c str3) = str2 ++ (String c' str3))%string
 -> c = c'.
Proof.
  intros.
  rewrite (string_lemma2 str1) in H.
  rewrite (string_lemma2 str2) in H.
  rewrite append_remove_suffix in H.
  eapply string_lemma3.
  exact H.
Qed.

Ltac pop_bits n x :=
  match n with
  | 0 => idtac
  | S ?m => let y := fresh "y" in
            let z := fresh "z" in
  destruct x as [ y | z | ]; [ pop_bits m y | pop_bits m z | idtac ]
  end.

Lemma of_pos_suff_aux : forall n x suff, pos_length x = n -> of_pos x suff = (of_pos x "" ++ suff)%string.
Proof.
  intro n.
  induction n using (well_founded_induction lt_wf).
  intros.
  pop_bits 4 x; simpl;
  match goal with
  | |- of_pos ?p (String ?c ?suff) = (of_pos ?p (String ?c EmptyString) ++ ?suff)%string =>
      assert (pos_length p < n) as pf by (simpl in H0; lia);
      rewrite (H _ pf _ (String c suff) eq_refl);
      rewrite (H _ pf _ (String c EmptyString) eq_refl);
      apply string_lemma2
  | _ => reflexivity
  end.
Qed.

Lemma of_pos_suff : forall x suff, of_pos x suff = (of_pos x "" ++ suff)%string.
Proof.
  intros; eapply of_pos_suff_aux.
  reflexivity.
Qed.

Lemma of_pos_ne : forall x, of_pos x "" <> "".
Proof.
  pop_bits 4 x;
  try discriminate;
  try (simpl;
       rewrite of_pos_suff;
       destruct (of_pos _ "");
       discriminate).
Qed.

Lemma of_pos_nz : forall x, of_pos x "" <> "0".
Proof.
  pop_bits 4 x;
  try discriminate;
  try (simpl; rewrite of_pos_suff; apply string_lemma1; apply of_pos_ne).
Qed.

Lemma of_pos_lemma1 : forall p q str c c', of_pos p (String c str) = of_pos q (String c' str) -> c = c'.
Proof.
  intros.
  rewrite (of_pos_suff p), (of_pos_suff q) in H.
  exact (string_lemma4 _ _ _ _ _ H).
Qed.

Lemma length_append : forall str str', (String.length (str ++ str') = String.length str + String.length str')%string.
Proof.
  induction str; intros.
  - auto.
  - simpl.
    rewrite IHstr; auto.
Qed.

Lemma of_pos_lemma2 : forall p str c d, of_pos p (String c str) <> String d str.
Proof.
  intros; rewrite of_pos_suff; intro.
  apply (f_equal String.length) in H.
  rewrite length_append in H.
  simpl in H.
  destruct (of_pos p "") eqn:G.
  - exact (of_pos_ne _ G).
  - simpl in H; lia.
Qed.

Lemma of_pos_inj_aux : forall n str x y, pos_length x = n -> of_pos x str = of_pos y str -> x = y.
Proof.
  intro n.
  induction n using (well_founded_induction lt_wf); intros str x y lenx of_pos_eq.
  pop_bits 4 x; pop_bits 4 y; simpl in *;
   match goal with
   | |- ?x = ?x => reflexivity
   | [ _ : of_pos ?p (String ?c ?str) = of_pos ?q (String ?c ?str) |- _ ]
      => assert (pos_length p < n) as pf by (simpl in lenx; lia);
         rewrite (H _ pf _ _ _ eq_refl of_pos_eq); reflexivity
   | [ H : of_pos ?p (String ?c str) = of_pos ?q (String ?d str) |- _ ] => discriminate (of_pos_lemma1 _ _ _ _ _ H)
   | [ H : of_pos ?p (String ?c ?str) = String ?d ?str |- _ ] => elim (of_pos_lemma2 _ _ H)
   | [ H : String ?d ?str = of_pos ?p (String ?c ?str) |- _ ] => symmetry in H; elim (of_pos_lemma2 _ _ H)
   | _ => discriminate
   end.
Qed.

Lemma of_pos_inj : forall str x y, of_pos x str = of_pos y str -> x = y.
Proof.
  intros.
  eapply of_pos_inj_aux.
  reflexivity.
  exact H.
Qed.

Lemma natToHexStr_inj :
  forall n m,
    natToHexStr n = natToHexStr m ->
    n = m.
Proof.
  intros n m Hnm.
  unfold natToHexStr in Hnm.
  destruct n,m; simpl in Hnm.
  - reflexivity.
  - symmetry in Hnm; elim (of_pos_nz _ Hnm).
  - elim (of_pos_nz _ Hnm).
  - f_equal.
    apply SuccNat2Pos.inj.
    eapply of_pos_inj; exact Hnm.
Qed.
*)
