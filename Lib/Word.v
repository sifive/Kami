Require Import Coq.ZArith.BinIntDef Coq.ZArith.BinInt Coq.ZArith.Zdiv.


Definition minimize_eq_proof{A: Type}(eq_dec: forall (x y: A), {x = y} + {x <> y}){x y: A}    (pf: x = y): x = y :=
  match eq_dec x y with
  | left p => p
  | right n => match n pf: False with end
  end.

Section Word.
  Section fixedWidth.
    Variable width : nat.

    Let wrap_value n := Z.modulo n (Z.pow 2 (Z.of_nat width)).

    (* Word is a record with two fields wordVal and wordBound *)
    Record word := mk {wordVal : Z ;
                       wordBound : wrap_value wordVal = wordVal}.
    
    Delimit Scope word_scope with word.
    Bind Scope word_scope with word.

    Open Scope word_scope.

    Theorem Natmod_mod : forall a n, Nat.modulo (Nat.modulo a n) n = Nat.modulo a n.
    Proof.
      destruct n.
      - reflexivity.
      - rewrite Nat.mod_mod by abstract (intro; discriminate).
        reflexivity.
    Defined.
    

    Definition wordWrap (n : Z) : word :=
      mk (wrap_value n) (minimize_eq_proof Z.eq_dec (Zdiv.Zmod_mod n _)).
    

    Definition zToWord := wordWrap.

    Definition boolToZ b : Z :=
      match b with
      | false => 0
      | true => 1
      end.

    Definition boolToWord b := wordWrap (boolToZ b).

    Definition wadd x y := wordWrap (Z.add (wordVal x) (wordVal y)).

    Definition wsub x y := wordWrap (Z.sub (wordVal x) (wordVal y)).

    Definition wor x y := wordWrap (Z.lor (wordVal x) (wordVal y)).

    Definition wand x y := wordWrap (Z.land (wordVal x) (wordVal y)).

    Definition wxor x y := wordWrap (Z.lxor (wordVal x) (wordVal y)).

    Definition wnot x := wordWrap (Z.sub (Z.pow 2 (Z.of_nat width)) (Z.add (wordVal x) 1)).

    Definition wuand x := Z.eqb (wordVal (wordWrap 1)) (wordVal x).

    Definition wuor x := negb (Z.eqb (wordVal (wordWrap 0)) (wordVal x)).

    Fixpoint pos_uxor (p : positive) : bool :=
      match p with
      | xH => true
      | xI p' => negb (pos_uxor p')
      | xO p' => (pos_uxor p')
      end.

    Definition N_uxor (n : N) : bool :=
      match n with
      | N0 => false
      | Npos p => pos_uxor p
      end.

    Definition un_xor (z : Z) : bool :=
      match z with
      | Z0 => false
      | Zpos p => pos_uxor p
      | Zneg p => pos_uxor p
      end.

    Definition wuxor x := un_xor (wordVal x).

    Definition wmul x y := wordWrap (Z.mul (wordVal x) (wordVal y)).

    Definition wdiv x y := wordWrap (Z.div (wordVal x) (wordVal y)).

    Definition wmod x y := wordWrap (Z.modulo (wordVal x) (wordVal y)).

    Definition wslu x y := wordWrap (Z.mul (wordVal x) (Z.pow 2 (wordVal y))).

    Definition wsru x y := wordWrap (Z.div (wordVal x) (Z.pow 2 (wordVal y))).

    Definition weqb x y := Z.eqb (wordVal x) (wordVal y).

    Definition wltu x y := Z.ltb (wordVal x) (wordVal y).

  End fixedWidth.

  Definition truncLsb {lsb outSz} (w : @word outSz) : @word lsb := 
    zToWord lsb (wordVal outSz w).

  Definition truncMsb {msb outSz} (w : @word outSz) : @word msb :=
    zToWord msb (Z.div (wordVal outSz w) (Z.pow 2 (Z.of_nat (Nat.sub outSz msb)))).


  Definition wconcat {msb lsb outSz} (w1 : @word msb) (w2 : @word lsb) :  @word outSz :=
    zToWord outSz (Z.add (Z.mul (wordVal msb w1) (Z.of_nat (Nat.pow 2 lsb))) (wordVal lsb w2)).

  Definition get_msb {sz} (w : @word sz) : @word 1 :=
    (@truncMsb 1 sz w).

  Definition get_lsb {sz} (w : @word sz) : @word 1 :=
    (@truncLsb 1 sz w).

  Definition wordValSigned {sz} (w : @word sz) : @word sz :=
    (zToWord _ (Z.of_nat (Nat.pow 2 sz) - (wordVal _ w))).

  Definition wsraOne {sz1 sz2} (w1 : @word sz1) (w2 : @word sz2) : @word sz1 :=
    if (Z.ltb (wordVal _ w1) (Z.of_nat (Nat.pow 2 (sz1 - 1)))) then
      (zToWord _ (Z.div (wordVal _ w1) (Z.of_nat (Nat.pow 2 sz2)))) else
      (zToWord _ (Z.add (wordVal sz1 w1) (Z.div (wordVal _ (@wordValSigned sz1 w1)) (Z.of_nat (Nat.pow 2 sz2))))).


  Fixpoint wsraFix {sz1 sz2 : nat} (w1 : @word sz1) (w2 : nat) : @word sz1 :=
    match w2 with
    | O => w1
    | S n => @wsraOne sz1 1 (@wsraFix sz1 sz2 w1 n) (zToWord 1 1)
    end.

  Definition wsra {sz1 sz2 : nat} (w1 : @word sz1) (w2 : @word sz2) : @word sz1 :=
    @wsraFix _ sz2 w1 (Z.to_nat (wordVal _ w2)).

  Definition whd sz (w : word (S sz)) := @truncMsb 1 _ w.

  Definition wtail sz (w : word (S sz)) := @truncLsb ((S sz)-1) _ w.

End Word.

Module Notations.

  Notation "^~" := wnot : word_scope.
  Notation "l ^+ r" := (@wadd _ l r) (at level 50, left associativity) : word_scope.
  Notation "l ^* r" := (@wmul _ l r) (at level 40, left associativity) : word_scope.
  Notation "l ^- r" := (@wsub _ l r) (at level 50, left associativity) : word_scope.
  Notation "l ^/ r" := (@wdiv _ l r) (at level 50, left associativity) : word_scope.
  Notation "l ^% r" := (@wmod _ l r) (at level 50, left associativity) : word_scope.
  Notation "l ^| r" := (@wor _ l r) (at level 50, left associativity) : word_scope.
  Notation "l ^& r" := (@wand _ l r) (at level 40, left associativity) : word_scope.

End Notations.

(*Compute (@wadd 3 (ZToWord 3 (-2%Z)) (ZToWord 3 3)).

Compute (@truncMsb 1 5 (of_nat 5 31)).

Compute (@concat _ _ 4 (of_nat 2 2) (of_nat 2 3)).

Compute (@of_bool 1 (@wuxor _ (of_nat 2 3))).

Compute (@wsru _ (of_nat 8 167) (of_nat 8 1)).


Compute (@wsrs _ (of_nat 8 167) (of_nat 8 1)).*)

(*Compute (of_nat 2 (Nat.pow 2 2 - 2 + 1)).

Compute (@get_msb _ (of_nat 3 7)).

Compute (@get_lsb _ (of_nat 3 6)).

Compute (@wordValSigned _ (of_nat 2 3)).

Compute (@wsra 4 1 (of_nat 4 15) (of_nat 1 1)).

Compute (@wsra 2 1 (of_nat 2 3) (of_nat 1 1)).

Compute (@wsra 5 4 (of_nat 5 9) (of_nat 4 4)).*)



