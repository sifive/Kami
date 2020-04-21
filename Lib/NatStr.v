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
