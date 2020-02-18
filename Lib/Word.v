Require Import Coq.ZArith.BinIntDef Coq.ZArith.BinInt Coq.ZArith.Zdiv Psatz.


Definition minimize_eq_proof{A: Type}(eq_dec: forall (x y: A), {x = y} + {x <> y}){x y: A}    (pf: x = y): x = y :=
  match eq_dec x y with
  | left p => p
  | right n => match n pf: False with end
  end.

Section Word.
  Section fixedWidth.
    Variable width : nat.

    Declare Scope word_scope.

    Local Notation wrap_value n := (Z.modulo n (Z.pow 2 (Z.of_nat width))).

    (* Word is a record with two fields wordVal and wordBound *)
    Record word := mk {wordVal : Z ;
                       wordBound : wrap_value wordVal = wordVal}.
    
    Delimit Scope word_scope with word.
    Bind Scope word_scope with word.

    Open Scope word_scope.

    Definition ZToWord (n : Z) : word :=
      mk (wrap_value n) (minimize_eq_proof Z.eq_dec (Zdiv.Zmod_mod n _)).

    Definition boolToZ b : Z :=
      match b with
      | false => 0
      | true => 1
      end.

    Definition NToWord (n : N) := ZToWord (Z.of_N n).

    Definition boolToWord b := ZToWord (boolToZ b).

    Definition natToWord (n : nat) := ZToWord (Z.of_nat n).
    
    Definition wordToNat (w : word) := Z.to_nat (wordVal w).

    Definition wones := ZToWord ((2 ^ (Z.of_nat width))%Z - 1).
      
    Definition wadd x y := ZToWord (Z.add (wordVal x) (wordVal y)).

    Definition wsub x y := ZToWord (Z.sub (wordVal x) (wordVal y)).

    Definition wor x y := ZToWord (Z.lor (wordVal x) (wordVal y)).

    Definition wand x y := ZToWord (Z.land (wordVal x) (wordVal y)).

    Definition wxor x y := ZToWord (Z.lxor (wordVal x) (wordVal y)).

    Definition wneg x := ZToWord (Z.sub (Z.pow 2 (Z.of_nat width)) (wordVal x)).

    Definition wnot x := ZToWord (Z.sub (wordVal (wneg x)) 1).

    Definition wuand x := Z.eqb (wordVal wones) (wordVal x).

    Definition wuor x := negb (Z.eqb (wordVal (ZToWord 0)) (wordVal x)).

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

    Definition wmul x y := ZToWord (Z.mul (wordVal x) (wordVal y)).

    Definition wdiv x y := ZToWord (Z.div (wordVal x) (wordVal y)).

    Definition wmod x y := ZToWord (Z.modulo (wordVal x) (wordVal y)).

    Definition wslu x y := ZToWord (Z.mul (wordVal x) (Z.pow 2 (wordVal y))).

    Definition wsru x y := ZToWord (Z.div (wordVal x) (Z.pow 2 (wordVal y))).

    Definition weqb x y := Z.eqb (wordVal x) (wordVal y).

    Definition wltu x y := Z.ltb (wordVal x) (wordVal y).

  End fixedWidth.

  Definition truncLsb {lsb outSz} (w : @word outSz) : @word lsb := 
    ZToWord lsb (wordVal outSz w).

  Definition truncMsb {msb outSz} (w : @word outSz) : @word msb :=
    ZToWord msb (Z.div (wordVal outSz w) (Z.pow 2 (Z.of_nat (Nat.sub outSz msb)))).


  Definition wconcat {msb lsb outSz} (w1 : @word msb) (w2 : @word lsb) :  @word outSz :=
    ZToWord outSz (Z.add (Z.mul (wordVal msb w1) (Z.pow 2 (Z.of_nat lsb))) (wordVal lsb w2)).

  Definition get_msb {sz} (w : @word sz) : @word 1 :=
    (@truncMsb 1 sz w).

  Definition get_lsb {sz} (w : @word sz) : @word 1 :=
    (@truncLsb 1 sz w).

  Definition wnon_neg {sz} (w : @word sz) : bool :=
    (Z.ltb (wordVal _ w) (Z.pow 2 (Z.of_nat (sz - 1)))).
  
  Definition twosComplement {sz} (w: @word sz) : @word sz :=
    ZToWord _ (Z.sub (Z.pow 2 (Z.of_nat sz)) (wordVal _ w)).

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
    then twosComplement (ZToWord _ (Z.opp n))
    else ZToWord _ n.

  Definition wsra {sz1 sz2: nat} (w1: @word sz1) (w2 : @word sz2) : @word sz1 :=
    @signedZToWord sz1 (Z.div (if wnon_neg w1
                               then wordVal _ w1
                               else wordToSignedZ w1) (Z.pow 2 (wordVal _ w2))).
  
  Definition whd sz (w : word (S sz)) := @truncMsb 1 _ w.

  Definition wtail sz (w : word (S sz)) := @truncLsb sz _ w.

  Definition wsplitl (sz1 sz2 : nat) (w : @word (sz1 + sz2)) : @word sz1 :=
    ZToWord _ (wordVal _ w / (Z.pow 2 (Z.of_nat sz2)))%Z.

  Definition wsplitr (sz1 sz2 : nat) (w : @word (sz1 + sz2)) : @word sz2 :=
    ZToWord _ ((wordVal _ w) mod (Z.pow 2 (Z.of_nat sz2)))%Z.
  
End Word.

Module Notations.

  Declare Scope word_scope.

  Notation "^~" := wneg : word_scope.
  Notation "l ^* r" := (@wmul _ l r) (at level 40, left associativity) : word_scope.
  Notation "l ^/ r" := (@wdiv _ l r) (at level 50, left associativity) : word_scope.
  Notation "l ^+ r" := (@wadd _ l r) (at level 50, left associativity) : word_scope.
  Notation "l ^- r" := (@wsub _ l r) (at level 50, left associativity) : word_scope.
  Notation "l ^% r" := (@wmod _ l r) (at level 50, left associativity) : word_scope.
  Notation "l ^| r" := (@wor _ l r) (at level 50, left associativity) : word_scope.
  Notation "l ^& r" := (@wand _ l r) (at level 40, left associativity) : word_scope.

  Notation "WO~0" := (ZToWord 1 0) : word_scope.
  Notation "WO~1" := (ZToWord 1 1) : word_scope.

  Delimit Scope word_scope with word.
End Notations.
Notation wzero sz := (ZToWord sz 0).

Export Notations.
Export ZArith.
(* Compute (@wnot 2 (ZToWord 2 2)). *)

(* Compute (@wneg 2 (ZToWord 2 3)). *)

(* Compute (wsra (ZToWord 4 15) (ZToWord 1 1)). *)

(* Compute (wsra (ZToWord 4 12) (ZToWord 3 3)). *)

(* Compute (wsra (ZToWord 2 1) (ZToWord 3 5)). *)

(* Compute (wsra (ZToWord 5 9) (ZToWord 4 3)). *)

(* Compute (@wconcat 2 2 4 (ZToWord 2 2) (ZToWord 2 3)). *)

(* Compute (@truncLsb 2 4 (@wconcat 2 2 4 (ZToWord 2 2) (ZToWord 2 3))).*)
