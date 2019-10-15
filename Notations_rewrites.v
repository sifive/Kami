(*
 * Notations_rewrites.v
 *
 * Rewriting rules useful for Notation definitions
 *)
Require Import Kami.AllNotations.
Require Import List.
Require Import Vector.
Import VectorNotations.
Import ListNotations.
Require Import Kami.Notations.

Lemma makeModule_rules'_Registers: forall l, makeModule_rules' (Registers l)=[].
Proof.
  intros.
  induction l.
  + simpl.
    reflexivity.
  + simpl.
    rewrite IHl.
    simpl.
    reflexivity.
Qed.
 
Lemma makeModule_rules'_append: forall l1 l2, (makeModule_rules' (l1++l2))=(makeModule_rules' l1)++(makeModule_rules' l2).
(*Proof.
  intros.
  induction l1.
  + simpl.
    reflexivity.
  + simpl.
    rewrite IHl1.*) Admitted.

Lemma makeModule_rules'_MERegister: forall a b, makeModule_rules' ((MERegister a)::b)=makeModule_rules' b.
Proof.
  simpl.
  reflexivity.
Qed.

Lemma makeModule_rules'_MERule: forall a b, makeModule_rules' ((MERule a)::b)=a::(makeModule_rules' b).
Proof.
  simpl.
  reflexivity.
Qed.

Lemma makeModule_rules'_nil: makeModule_rules' []=[].
Proof.
  simpl.
  reflexivity.
Qed.

Hint Rewrite makeModule_rules'_Registers makeModule_rules'_append makeModule_rules'_MERegister makeModule_rules'_MERule makeModule_rules'_nil : makeModule_rules'_db.
 
Lemma makeModule_meths'_Registers: forall l, makeModule_meths' (Registers l)=[].
Proof.
  intros.
  induction l.
  simpl.
  reflexivity.
  simpl.
  rewrite IHl.
  simpl.
  reflexivity.
Qed.
 
Lemma makeModule_meths'_append: forall l1 l2, makeModule_meths' (l1++l2)=(makeModule_meths' l1)++(makeModule_meths' l2).
(*Proof.
  intros.
  induction l1.
  + simpl.
    reflexivity.
  + simpl.
    rewrite IHl1.*) Admitted.

Lemma makeModule_meths'_MERegister: forall a b, makeModule_meths' ((MERegister a)::b)=makeModule_meths' b.
Proof.
  simpl.
  reflexivity.
Qed.

Lemma makeModule_meths'_MERule: forall a b, makeModule_meths' ((MERule a)::b)=(makeModule_meths' b).
Proof.
  simpl.
  reflexivity.
Qed.

Lemma makeModule_meths'_nil: makeModule_meths' []=[].
Proof.
  simpl.
  reflexivity.
Qed.

Hint Rewrite makeModule_meths'_Registers makeModule_meths'_append makeModule_meths'_MERegister makeModule_meths'_MERule makeModule_meths'_nil : makeModule_meths'_db.

 
Lemma makeModule_regs'_Registers: forall l, makeModule_regs' (Registers l)=l.
Proof.
  intros.
  induction l.
  + simpl.
    reflexivity.
  + simpl.
    rewrite IHl.
    simpl.
    reflexivity.
Qed.
 
Lemma makeModule_regs'_append: forall l1 l2, makeModule_regs' (l1++l2)=(makeModule_regs' l1)++(makeModule_regs' l2).
(*Proof.
  intros.
  induction l1.
  + simpl.
    reflexivity.
  + simpl.
    rewrite IHl1.*) Admitted.

Lemma makeModule_regs'_MERegister: forall a b, makeModule_regs' ((MERegister a)::b)=a::(makeModule_regs' b).
Proof.
  simpl.
  reflexivity.
Qed.

Lemma makeModule_regs'_MERule: forall a b, makeModule_regs' ((MERule a)::b)=makeModule_regs' b.
Proof.
  simpl.
  reflexivity.
Qed.

Lemma makeModule_regs'_nil: makeModule_regs' []=[].
Proof.
  simpl.
  reflexivity.
Qed.

Hint Rewrite makeModule_regs'_Registers makeModule_regs'_append makeModule_regs'_MERegister makeModule_regs'_MERule makeModule_regs'_nil : makeModule_regs'_db.

