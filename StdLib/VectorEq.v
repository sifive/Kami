Require Import Kami.StdLib.VectorDef.
Require Import Kami.StdLib.VectorSpec.
Import Kami.StdLib.VectorDef.VectorNotations.

Section BEQ.

 Variables (A: Type) (A_beq: A -> A -> bool).
 Hypothesis A_eqb_eq: forall x y, A_beq x y = true <-> x = y.

 Definition eqb:
   forall {m n} (v1: Vec A m) (v2: Vec A n), bool :=
   fix fix_beq {m n} v1 v2 :=
     match m as m0 return (Vec A m0 -> bool) with
     | O => (fun _ => match n with
                    | O => true
                    | S n' => false
                     end)
     | S m' => (fun v1' =>
                  match n as n0 return (Vec A n0 -> bool) with
                  | O => fun _ => false
                  | S n' => (fun v2' => (A_beq (fst v1') (fst v2') &&
                                        fix_beq (snd v1') (snd v2'))%bool)
                  end v2)
     end v1.

 Lemma eqb_nat_eq: forall m n (v1: Vec A m) (v2: Vec A n)
  (Hbeq: eqb v1 v2 = true), m = n.
 Proof.
   intros m n v1; revert n.
   induction m; destruct n; auto; try discriminate; intros.
   destruct v1, v2; simpl in *.
   apply andb_prop in Hbeq; destruct Hbeq.
   f_equal; eauto.
 Qed.

 Lemma eqb_eq: forall n (v1: Vec A n) (v2: Vec A n),
  eqb v1 v2 = true <-> v1 = v2.
 Proof.
   refine (@rect2 _ _ _ _ _); [now constructor | simpl].
   intros ? ? ? Hrec h1 h2; destruct Hrec; destruct (A_eqb_eq h1 h2); split.
   + intros Hbeq. apply andb_prop in Hbeq; destruct Hbeq.
     f_equal; now auto.
   + intros Heq. destruct (cons_inj Heq). apply andb_true_intro.
     split; now auto.
 Qed.

 Definition eq_dec n (v1 v2: Vec A n): {v1 = v2} + {v1 <> v2}.
 Proof.
 case_eq (eqb v1 v2); intros.
  + left; now apply eqb_eq.
  + right. intros Heq. apply <- eqb_eq in Heq. congruence.
 Defined.

End BEQ.

Section CAST.

 Definition cast: forall {A m} (v: Vec A m) {n}, m = n -> Vec A n.
 Proof.
   intros; subst; auto.
 Defined.

End CAST.
