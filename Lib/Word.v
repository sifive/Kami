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
    
    Definition wones := ZToWord ((2 ^ (Z.of_nat width))%Z - 1).

  End fixedWidth.
  
  Section implicitWidth.
    Context {width : nat}.
    
    Definition wordToNat (w : word width) := Z.to_nat (wordVal width w).
      
    Definition wadd x y := ZToWord width (Z.add (wordVal width x) (wordVal width y)).

    Definition wsub x y := ZToWord width (Z.sub (wordVal width x) (wordVal width y)).

    Definition wor x y := ZToWord width (Z.lor (wordVal width x) (wordVal width y)).

    Definition wand x y := ZToWord width (Z.land (wordVal width x) (wordVal width y)).

    Definition wxor x y := ZToWord width (Z.lxor (wordVal width x) (wordVal width y)).

    Definition wneg x := ZToWord width (Z.sub (Z.pow 2 (Z.of_nat width)) (wordVal width x)).

    Definition wnot x := ZToWord width (Z.sub (wordVal width (wneg x)) 1).

    Definition wuand x := Z.eqb (wordVal width (wones width)) (wordVal width x).

    Definition wuor x := negb (Z.eqb (wordVal width (ZToWord width 0)) (wordVal width x)).

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

    Definition wuxor x := un_xor (wordVal width x).

    Definition wmul x y := ZToWord width (Z.mul (wordVal width x) (wordVal width y)).

    Definition wdiv x y := ZToWord width (Z.div (wordVal width x) (wordVal width y)).

    Definition wmod x y := ZToWord width (Z.modulo (wordVal width x) (wordVal width y)).

    Definition wslu x y := ZToWord width (Z.mul (wordVal width x) (Z.pow 2 (wordVal width y))).

    Definition wsru x y := ZToWord width (Z.div (wordVal width x) (Z.pow 2 (wordVal width y))).

    Definition weqb x y := Z.eqb (wordVal width x) (wordVal width y).

    Definition wltu x y := Z.ltb (wordVal width x) (wordVal width y).

  End implicitWidth.
  
  Definition truncLsb {lsb outSz} (w : @word outSz) : @word lsb := 
    ZToWord lsb (wordVal outSz w).

  Definition truncMsb {msb outSz} (w : @word outSz) : @word msb :=
    ZToWord msb (Z.div (wordVal outSz w) (Z.pow 2 (Z.of_nat (Nat.sub outSz msb)))).


  Definition wconcat {msb lsb outSz} (w1 : @word msb) (w2 : @word lsb) :  @word outSz :=
    ZToWord outSz (Z.add (Z.mul (wordVal msb w1) (Z.pow 2 (Z.of_nat lsb))) (wordVal lsb w2)).

  Definition wcombine {msb lsb} (w1 : @word msb) (w2 : @word lsb) : @word (msb + lsb) :=
    @wconcat msb lsb (msb + lsb) w1 w2.
  
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

  Fixpoint nat_cast (P : nat -> Type) {n m} : n = m -> P n -> P m.
    refine match n, m return n = m -> P n -> P m with
           | O, O => fun _ => id
           | S n, S m => fun pf => @nat_cast (fun n => P (S n)) n m (f_equal pred pf)
           | _, _ => fun pf => match _ pf : False with end
           end;
      clear; abstract congruence.
  Defined.

  Definition wmsb sz (w : word sz) (b : bool) :=
    if (sz =? 0)%nat then b else (0 <? wordToNat w / 2 ^ (sz - 1)).

  Definition wleu {sz} (x y : word sz) :=
    (wordVal _ x <=? wordVal _ y)%Z.


  Definition wlt_dec : forall {sz} (l r : word sz), {(wltu l r) = true} +  {(wltu l r) = false}.
  Proof.
    intros.
    destruct (wltu l r).
    left. reflexivity.
    right.
    reflexivity.
  Defined.

  Lemma eq_wordVal {sz} {x y : word sz} : wordVal _ x = wordVal _ y -> x = y.
  Proof.
    intros.
    destruct x as [x px].
    destruct y as [y py].
    intros.
    simpl in *; subst; auto.
    apply f_equal, Eqdep_dec.UIP_dec. eapply Z.eq_dec.
  Qed.

  Lemma weqb_true: forall {sz} (a b: word sz), weqb a b = true -> a = b.
  Proof.
    intros.
    unfold weqb in H.
    rewrite Z.eqb_eq in H.
    apply eq_wordVal.
    assumption.
  Qed.

  Lemma weqb_false: forall {sz} (a b: word sz), weqb a b = false -> a <> b.
  Proof.
    intros.
    unfold weqb in H.
    rewrite Z.eqb_neq in H. congruence.
  Qed.

  Definition weq {sz} (x y: word sz): {x = y} + {x <> y} :=
    match weqb x y as sth return weqb x y = sth -> {x = y} + {x <> y} with
    | true => fun s => left (weqb_true _ _ s)
    | false => fun s => right (weqb_false _ _ s)
    end eq_refl.

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

  Notation "$ n" := (@natToWord _ n) (at level 0, no associativity): word_scope.
  (* Notation "$ m" := (@ZToWord _ m) (at level 0, no associativity): word_scope. *)
  
  Notation "WO~0" := (ZToWord 1 0) : word_scope.
  Notation "WO~1" := (ZToWord 1 1) : word_scope.
  Notation WO := (ZToWord 0 0).

  (* Start of deprecated notations ported from bbv *)
  Notation pow2 := (Nat.pow 2).
  
  (* End of deprecated notations ported from bbv *)
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
