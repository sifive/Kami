(*
 * Helper theorems and tactics for verifying WfMod properties
 *)
Require Import Kami.AllNotations.
Require Import Kami.Notations.
Require Import Kami.Rewrites.Notations_rewrites.
Require Import Kami.Properties.
Require Import Kami.PProperties.
Require Import Kami.Syntax.
Require Import Vector.
Require Import List.
Require Import Coq.Strings.String.

Local Open Scope kami_action.
Local Open Scope kami_expr.

Theorem string_equal_prefix: forall (a: string) (b: string) (c: string), (a++b=a++c)%string<->(b=c)%string.
Proof.
  split.
  - intros.
    induction a.
    + simpl in H.
      apply H.
    + inversion H; subst; clear H.
      apply IHa.
      apply H1.
  - intros.
    subst.
    reflexivity.
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


(*Theorem or_diff: forall p a b, a<> b -> forall k : string,
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
Qed.*)

Ltac trivialSolve :=
    match goal with
    | |- forall _, In _ (getAllRules (Base (BaseRegFile _))) -> _ => simpl;intros;trivialSolve
    | H: False |- _ => elim H
    | |- DisjKey _ List.nil => apply DisjKey_nil2 
    | |- DisjKey List.nil _ => apply DisjKey_nil1
    | |- DisjKeyWeak _ List.nil => rewrite <- DisjKeyWeak_same;[apply DisjKey_nil2 | repeat (decide equality)]
    | |- DisjKeyWeak List.nil _ => rewrite <- DisjKeyWeak_same;[apply DisjKey_nil1 | repeat (decide equality)]
    | |- ~ (List.In _ _) => simpl;trivialSolve
    | |- ~ (_ \/ _) => let X := fresh in intro X;inversion X;subst;clear X;trivialSolve
    | |- _ /\ _ => split;trivialSolve
    | |- ~False => let X := fresh in intro X;inversion X
    | |- (_++_)%string <> (_++_)%string => let X := fresh in try (intro X;apply string_equal_prefix in X; inversion X)
    (*| |- ~((?P++_)%string = _ \/ False) \/ ~((?P++_)%string = _ \/ False) => let X := fresh in try (apply or_diff;intro X;inversion X)*)
    | |- NoDup (_::_) => econstructor; simpl; trivialSolve
    | |- NoDup [] => econstructor
    | H: _ \/ _ |- _ => inversion H;subst;clear H;trivialSolve
    | H: (?P++_)%string=(?P++_)%string |- _ => apply string_equal_prefix in H;inversion H;subst;clear H;trivialSolve
    | H: In _ (map fst _) |- _ => simpl in H;trivialSolve
    | |- (?P = ?P) => reflexivity
    | _ => idtac
    end.

Theorem ne_disjunction_break1: forall a b c, (~(a \/ False) \/ ~(b \/ False)) /\
                                       (~(a \/ False) \/ ~c) ->
                                        ~(a \/ False) \/ ~(b \/ c).
Proof.
    tauto.
Qed.

Theorem ne_disjunction_break2: forall a b c, (~(a \/ False) \/ ~c) /\
                                        (~b \/ ~c) ->
                                        ~(a \/ b) \/ ~ c.
Proof.
    tauto.
Qed.

(*Ltac DisjKey_solve :=
  match goal with
  (*| |- ~((?P++_)%string = _ \/ False) \/ ~((?P++_)%string = _ \/ False) => let X := fresh in try (apply or_diff;intro X;inversion X)*)
  | |- ~(_ \/ False) \/ ~(_ \/ _) => apply ne_disjunction_break1;split;DisjKey_solve
  | |- ~(_ \/ _ \/ _) \/ ~_ => apply ne_disjunction_break2;split;DisjKey_solve
  (*| |- DisjKey _ _ => unfold DisjKey; simpl; intros;DisjKey_solve*)
  | |- DisjKey _ _ => rewrite DisjKeyWeak_same;[ DisjKey_solve | repeat (decide equality) ]
  | |- DisjKeyWeak _ _ => unfold DisjKeyWeak;intros;DisjKey_solve
  | H: In _ (map fst ((_,_)::_)) |- _ => simpl in H;DisjKey_solve
  | |- _ => trivialSolve
  end.*)

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
           -- left.
              intro X. 
              apply H1.
              right.
              apply X.
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
        ++ repeat (decide equality).
        ++ repeat (decide equality).
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
           -- right.
              intro X.
              apply H1.
              right.
              apply X.
      - intros.
        rewrite DisjKey_Cons2.
        rewrite DisjKey_Cons2 in H.
        inversion H;subst;clear H.
        split.
        ++ apply H0.
        ++ apply IHy.
           apply H1.
        ++ repeat (decide equality).
        ++ repeat (decide equality).
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
      intro X.
      inversion X;subst;clear X.
      destruct a0.
      destruct a.
      simpl in H0.
      subst.
      remember (s0=?s0).
      destruct b.
      - simpl in H.
        inversion H.
      - rewrite eqb_refl in Heqb.
        inversion Heqb.
      - destruct a.
        destruct a0.
        simpl in H0.
        simpl in IHl.
        remember (s =? s0).
        destruct b.
        *  simpl in H.
           inversion H.
        *  simpl in H.
           apply IHl.
           ** apply H.
           ** apply H0.
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

(*Ltac WfMod_Solve :=
    match goal with
    | |- _ => (progress discharge_wf);WfMod_Solve
    | |- forall _, _ => intros;WfMod_Solve
    | |- _ -> _ => intros;WfMod_Solve
    | |- _ /\ _ => split;WfMod_Solve
    | |- In _ _ => simpl;WfMod_Solve
    | |- (_ \/ False) => left;WfMod_Solve
    | |- _ => trivialSolve
    end.

Ltac WfConcatAction_Solve :=
    match goal with
    | |- _ => progress discharge_wf;WfConcatAction_Solve
    | |- forall _, _ => intros;simpl;WfConcatAction_Solve
    | H: In _ (getAllMethods _) |- _ => simpl in H;inversion H;subst;clear H;simpl;WfConcatAction_Solve
    | H: _ \/ _ |- _ => simpl in H;inversion H;subst;clear H;simpl;WfConcatAction_Solve
    | H: False |- _ => inversion H
    | |- _ => idtac
    end.*)

