Require Import Kami.Notations.
Require Import Kami.Syntax.
Require Import List.
Require Import Kami.Notations_rewrites.
Require Import Program.Equality.
Require Import Kami.Rewrites.ReflectionPre.
Require Import Kami.Rewrites.ReflectionSoundTopTheorems.


Theorem KRSimplifySound_RegFileBase: forall e,
    KRExprDenote_RegFileBase e = KRExprDenote_RegFileBase (KRSimplify_RegFileBase e).
Proof.
  intros.
  destruct e. reflexivity.
Qed.

