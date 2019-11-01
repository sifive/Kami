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
Require Import Coq.Strings.String.

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


Theorem or_diff: forall p a b, a<> b -> forall k : string,
    ~ ((p ++ a)%string = k \/ False) \/
    ~ ((p ++ b)%string = k \/ False).
Proof.
  intros.
  classical_left.
  apply NNPP in H0.
  inversion H0;subst;clear H0.
  + intro X.
    inversion X;subst;clear X.
    - apply string_equal_prefix in H0.
      apply H in H0.
      elim H0.
    - elim H0.
  + elim H1.
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
    (*| |- ~((?P++_)%string = _ \/ False) \/ ~((?P++_)%string = _ \/ False) => let X := fresh in try (apply or_diff;intro X;inversion X)*)
    | _ => idtac
    end.

Theorem ne_disjunction_break: forall a b c, (~(a \/ False) \/ ~(b \/ False)) /\
                                       (~(a \/ False) \/ ~c) ->
                                        ~(a \/ False) \/ ~(b \/ c).
Proof.
    intros.
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    + left.
      apply H.
    + inversion H1; subst; clear H1.
      - apply not_or_and in H.
        inversion H; subst; clear H.
        apply not_or_and in H0.
        inversion H0; subst; clear H0.
        left.
        apply and_not_or.
        split.
        ++ apply H.
        ++ intro X.
           elim X.
      - right.
        apply not_or_and in H.
        inversion H; subst; clear H.
        apply and_not_or.
        split.
        ++ apply H1.
        ++ apply H0.
Qed.

Ltac DisjKey_solve :=
  match goal with
  | |- ~((?P++_)%string = _ \/ False) \/ ~((?P++_)%string = _ \/ False) => let X := fresh in try (apply or_diff;intro X;inversion X)
  | |- ~(_ \/ False) \/ ~(_ \/ _) => apply ne_disjunction_break;split;DisjKey_solve
  | |- DisjKey _ _ => unfold DisjKey; simpl; intros;DisjKey_solve
  | |- _ => trivialSolve
  end.

Theorem DisjKey_NubBy1: forall T (x: list (string * T)) (y: list (string * T)), DisjKey x y -> DisjKey (nubBy (fun '(a,_) '(b,_) => String.eqb a b) x) y.
Proof.
    intros  T x y.
    generalize y.
    induction x.
    + simpl.
      intros.
      apply H.
    + simpl.
      remember (
        existsb (let '(a0, _) := a in fun '(b, _) => a0 =? b)
         (nubBy (fun '(a0, _) '(b, _) => a0 =? b) x)).
      destruct b.
      - simpl.
        intros.
        apply IHx.
        unfold DisjKey in H.
        simpl in H.
        unfold DisjKey.
        intros.
        assert(
          ~ (fst a = k \/ In k (map fst x)) \/ ~ In k (map fst y0)
        ).
        ++ apply H.
        ++ inversion H0;subst;clear H0.
           -- apply not_or_and in H1.
              inversion H1; subst; clear H1.
              left.
              apply H2.
           -- right.
              apply H1.
      - intros.
        rewrite DisjKey_Cons1.
        rewrite DisjKey_Cons1 in H.
        inversion H;subst;clear H.
        split.
        ++ apply H0.
        ++ apply IHx.
           apply H1.
Qed.

Theorem DisjKey_NubBy2: forall T (x: list (string * T)) (y: list (string * T)), DisjKey x y -> DisjKey x (nubBy (fun '(a,_) '(b,_) => String.eqb a b) y).
Proof.
    intros T x y.
    generalize x.
    induction y.
    + simpl.
      intros.
      apply H.
    + simpl.
      remember (
        existsb (let '(a0, _) := a in fun '(b, _) => a0 =? b)
          (nubBy (fun '(a0, _) '(b, _) => a0 =? b) y)).
      destruct b.
      - simpl.
        intros.
        apply IHy.
        unfold DisjKey in H.
        simpl in H.
        unfold DisjKey.
        intros.
        assert(
          ~ In k (map fst x0) \/ ~ (fst a = k \/ In k (map fst y))
        ).
        ++ apply H.
        ++ inversion H0; subst; clear H0.
           -- left.
              apply H1.
           -- apply not_or_and in H1.
              inversion H1; subst; clear H1.
              right.
              apply H2.
      - intros.
        rewrite DisjKey_Cons2.
        rewrite DisjKey_Cons2 in H.
        inversion H;subst;clear H.
        split.
        ++ apply H0.
        ++ apply IHy.
           apply H1.
Qed.

Theorem NoDup_NubBy_helper: forall T (a:(string * T)) (l:list (string *T)),
    false = existsb (let '(a0, _) := a in fun '(b, _) => a0 =? b) l ->
    ~ In (fst a) (map fst l).
Proof.
    induction l.
    + simpl.
      intros.
      intro X.
      elim X.
    + simpl.
      intros.
      apply and_not_or.
      remember (
        (let '(a0, _) := a in fun '(b, _) => a0 =? b) a0).
      destruct b.
      - simpl in H.
        inversion H.
      - simpl in H.
        split.
        ++ destruct a0.
           destruct a.
           simpl.
           simpl in Heqb.
           intro X.
           subst.
           rewrite eqb_refl in Heqb.
           inversion Heqb.
        ++ apply IHl.
           rewrite <- H.
           reflexivity.
Qed.

       
Theorem NoDup_NubBy: forall T (x: list (string * T)), NoDup (map fst (nubBy (fun '(a,_) '(b,_) => String.eqb a b) x)).
Proof.
  intros.
  induction x.
  + simpl.
    apply NoDup_nil.
  + simpl.
    remember (
       existsb (let '(a0, _) := a in fun '(b, _) => a0 =? b)
         (nubBy (fun '(a0, _) '(b, _) => a0 =? b) x)
    ).
    destruct b.
    - apply IHx.
    - simpl.
      apply NoDup_cons.
      apply NoDup_NubBy_helper.
      apply Heqb.
      apply IHx.
Qed.

Ltac ltac_wfMod_ConcatMod :=
  apply ConcatModWf;autorewrite with kami_rewrite_db;repeat split;try assumption;auto with wfMod_ConcatMod_Helper;trivialSolve.

