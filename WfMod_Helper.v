(*
 * Helper theorems and tactics for verifying WfMod properties
 *)
Require Import Kami.AllNotations.
Require Import Kami.Notations.
Require Import Kami.Notations_rewrites.
Require Import Kami.Properties.
Require Import Kami.PProperties.
Require Import Vector.
Require Import List.
Require Import Coq.Logic.Classical_Prop.
Require Import Classical.

Theorem string_equal_prefix: forall (a: string) (b: string) (c: string), (a++b=a++c)%string->(b=c)%string.
Proof.
  intros.
  induction a.
  + simpl in H.
    apply H.
  + inversion H; subst; clear H.
    apply IHa.
    apply H1.
Qed.

Theorem DisjKey_nil2: forall A B (l: list (A*B)), DisjKey l List.nil.
Proof.
  intros.
  unfold DisjKey.
  intros.
  right.
  simpl.
  intro X.
  elim X.
Qed.

Theorem DisjKey_nil1: forall A B (l: list (A*B)), DisjKey List.nil l.
Proof.
  intros.
  unfold DisjKey.
  intros.
  left.
  simpl.
  intro X.
  elim X.
Qed.

Ltac trivialSolve :=
    match goal with
    | |- forall _, In _ (getAllRules (Base (BaseRegFile _))) -> _ => simpl;intros;trivialSolve
    | H: False |- _ => elim H
    | |- DisjKey _ List.nil => apply DisjKey_nil2 
    | |- DisjKey List.nil _ => apply DisjKey_nil1
    | |- ~ (List.In _ _) => simpl;trivialSolve
    | |- ~ (_ \/ _) => apply and_not_or;trivialSolve
    | |- _ /\ _ => split;trivialSolve
    | |- ~False => let X := fresh in intro X;inversion X
    | |- (_++_)%string <> (_++_)%string => let X := fresh in try (intro X;apply string_equal_prefix in X; inversion X)
    | _ => idtac
    end.

Ltac ltac_wfMod_ConcatMod :=
  apply ConcatModWf;autorewrite with kami_rewrite_db;repeat split;try assumption;auto with wfMod_ConcatMod_Helper;trivialSolve.

