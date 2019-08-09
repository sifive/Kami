Require Import Coq.ZArith.BinIntDef Coq.ZArith.BinInt Coq.ZArith.Zdiv.


Definition minimize_eq_proof{A: Type}(eq_dec: forall (x y: A), {x = y} + {x <> y}){x y: A}    (pf: x = y): x = y :=
  match eq_dec x y with
  | left p => p
  | right n => match n pf: False with end
  end.

Section Word.
  Section fixedWidth.
    Variable width : nat.

    Local Notation wrap_value n := (Z.modulo n (Z.pow 2 (Z.of_nat width))).

    (* Word is a record with two fields wordVal and wordBound *)
    Record word := mk {wordVal : Z ;
                       wordBound : wrap_value wordVal = wordVal}.
    
    Delimit Scope word_scope with word.
    Bind Scope word_scope with word.

    Open Scope word_scope.

    Definition zToWord (n : Z) : word :=
      mk (wrap_value n) (minimize_eq_proof Z.eq_dec (Zdiv.Zmod_mod n _)).    

    Definition boolToZ b : Z :=
      match b with
      | false => 0
      | true => 1
      end.

    Definition NToWord (n : N) := zToWord (Z.of_N n).

    Definition boolToWord b := zToWord (boolToZ b).

    Definition wadd x y := zToWord (Z.add (wordVal x) (wordVal y)).

    Definition wsub x y := zToWord (Z.sub (wordVal x) (wordVal y)).

    Definition wor x y := zToWord (Z.lor (wordVal x) (wordVal y)).

    Definition wand x y := zToWord (Z.land (wordVal x) (wordVal y)).

    Definition wxor x y := zToWord (Z.lxor (wordVal x) (wordVal y)).

    Definition wneg x := zToWord (Z.sub (Z.pow 2 (Z.of_nat width)) (wordVal x)).

    Definition wnot x := zToWord (Z.sub (wordVal (wneg x)) 1).

    Definition wmax := zToWord (Z.pow 2 (Z.of_nat width) - 1).

    Definition wuand x := Z.eqb (wordVal wmax) (wordVal x).

    Definition wuor x := negb (Z.eqb (wordVal (zToWord 0)) (wordVal x)).

    Fixpoint pos_uxor (p : positive) : bool :=
      match p with
      | xH => true
      | xI p' => negb (pos_uxor p')
      | xO p' => (pos_uxor p')
      end.

    Definition un_xor (z : Z) : bool :=
      match z with
      | Z0 => false
      | Zpos p => pos_uxor p
      | Zneg p => pos_uxor p
      end.

    Definition wuxor x := un_xor (wordVal x).

    Definition wmul x y := zToWord (Z.mul (wordVal x) (wordVal y)).

    Definition wdiv x y := zToWord (Z.div (wordVal x) (wordVal y)).

    Definition wmod x y := zToWord (Z.modulo (wordVal x) (wordVal y)).

    Definition wslu x y := zToWord (Z.mul (wordVal x) (Z.pow 2 (wordVal y))).

    Definition wsru x y := zToWord (Z.div (wordVal x) (Z.pow 2 (wordVal y))).

    Definition weqb x y := Z.eqb (wordVal x) (wordVal y).

    Definition wltu x y := Z.ltb (wordVal x) (wordVal y).

  End fixedWidth.

  Definition truncLsb {lsb outSz} (w : @word outSz) : @word lsb := 
    zToWord lsb (wordVal outSz w).

  Definition truncMsb {msb outSz} (w : @word outSz) : @word msb :=
    zToWord msb (Z.div (wordVal outSz w) (Z.pow 2 (Z.of_nat (Nat.sub outSz msb)))).


  Definition wconcat {msb lsb outSz} (w1 : @word msb) (w2 : @word lsb) :  @word outSz :=
    zToWord outSz (Z.add (Z.mul (wordVal msb w1) (Z.pow 2 (Z.of_nat lsb))) (wordVal lsb w2)).

  Definition get_msb {sz} (w : @word sz) : @word 1 :=
    (@truncMsb 1 sz w).

  Definition get_lsb {sz} (w : @word sz) : @word 1 :=
    (@truncLsb 1 sz w).

  Definition wnon_neg {sz} (w : @word sz) : bool :=
    (Z.ltb (wordVal _ w) (Z.pow 2 (Z.of_nat (sz - 1)))).
  
  Definition twosComplement {sz} (w: @word sz) : @word sz :=
    zToWord _ (Z.sub (Z.pow 2 (Z.of_nat sz)) (wordVal _ w)).

  Definition wordToSignedZ {sz} (w: @word sz) : Z :=
    if Z.ltb (wordVal _ w) (Z.pow 2 (Z.of_nat (sz - 1)))
    then wordVal _ w
    else Z.opp (wordVal _ (twosComplement w)).

  Definition signZ (n: Z) :=
    match n with
    | Z0 => false
    | Z.pos _ => false
    | Z.neg _ => true
    end.
  
  Definition signedZToWord {sz} (n: Z) : @word sz :=
    if signZ n
    then twosComplement (zToWord _ (Z.opp n))
    else zToWord _ n.

  Definition wsra {sz1 sz2: nat} (w1: @word sz1) (w2 : @word sz2) : @word sz1 :=
    @signedZToWord sz1 (Z.div (if wnon_neg w1
                               then wordVal _ w1
                               else wordToSignedZ w1) (Z.pow 2 (wordVal _ w2))).
  
  Definition whd sz (w : word (S sz)) := @truncMsb 1 _ w.

  Definition wtail sz (w : word (S sz)) := @truncLsb sz _ w.

End Word.

Module Notations.

  Notation "^~" := wneg : word_scope.
  Notation "l ^* r" := (@wmul _ l r) (at level 40, left associativity) : word_scope.
  Notation "l ^/ r" := (@wdiv _ l r) (at level 50, left associativity) : word_scope.
  Notation "l ^+ r" := (@wadd _ l r) (at level 50, left associativity) : word_scope.
  Notation "l ^- r" := (@wsub _ l r) (at level 50, left associativity) : word_scope.
  Notation "l ^% r" := (@wmod _ l r) (at level 50, left associativity) : word_scope.
  Notation "l ^| r" := (@wor _ l r) (at level 50, left associativity) : word_scope.
  Notation "l ^& r" := (@wand _ l r) (at level 40, left associativity) : word_scope.

End Notations.

(* Compute (@wnot 2 (zToWord 2 2)). *)

(* Compute (@wneg 2 (zToWord 2 3)). *)

(* Compute (wsra (zToWord 4 15) (zToWord 1 1)). *)

(* Compute (wsra (zToWord 4 12) (zToWord 3 3)). *)

(* Compute (wsra (zToWord 2 1) (zToWord 3 5)). *)

(* Compute (wsra (zToWord 5 9) (zToWord 4 3)). *)

(* Compute (NToWord 2 6). *)

(* Compute (@wconcat 2 2 4 (zToWord 2 2) (zToWord 2 3)). *)

(* Compute (@truncLsb 2 4 (@wconcat 2 2 4 (zToWord 2 2) (zToWord 2 3))).*)
