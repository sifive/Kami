(*
 * Helper theorems and tactics for verifying WfMod properties
 *)
Require Import Kami.AllNotations.
Require Import Kami.Notations.
Require Import Kami.Notations_rewrites.
Require Import Kami.Properties.
Require Import Kami.PProperties.
Require Import Kami.Syntax.
Require Import Vector.
Require Import List.
Require Import Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.

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

Ltac ltac_wfMod_ConcatMod helper_db :=
     repeat (apply ConcatModWf;autorewrite with kami_rewrite_db;repeat split;try (auto with helper_db);trivialSolve;try (apply string_dec)).

Theorem WfConcatActionT_fold_left_stuff1:
    forall A B f n r (rest:ActionT type A),
    WfConcatActionT rest r ->
    (forall (a:B) (rest:ActionT type A) r, WfConcatActionT rest r -> WfConcatActionT (f rest a) r) ->
    WfConcatActionT
      (@fold_left (ActionT type A) B f n rest) r.
Proof.
    intros A B f n r.
    induction n.
    + simpl.
      intros.
      apply H.
    + simpl.
      intros.
      apply IHn.
      - apply H0.
        apply H.
      - intros.
        apply H0.
        apply H1.
Qed.

Theorem WfConcatActionT_GatherActions1_Helper:
    forall (k_out:Kind) (k_in:Kind) (al:list (ActionT _ k_in)) (cont: list (Expr _ (SyntaxKind k_in)) -> ActionT _ k_out) r pre,
    (forall a c, In a al -> WfConcatActionT a c) ->
    (forall x, WfConcatActionT (cont x) r) ->
    WfConcatActionT (gatherActions al (fun vals => cont (pre++vals))) r.
Proof.
    intros.
    generalize pre.
    induction al.
    + simpl.
      intros.
      rewrite app_nil_r.
      apply H0.
    + simpl.
      discharge_wf.
      - apply H.
        simpl.
        left.
        reflexivity.
      - assert(
         (fun vals : list (Expr type (SyntaxKind k_in)) =>
          cont (pre0 ++ Var type (SyntaxKind k_in) v :: vals))=
         (fun vals : list (Expr type (SyntaxKind k_in)) =>
          cont ((pre0 ++ [Var type (SyntaxKind k_in) v])++vals))).
            eapply functional_extensionality.
            assert (forall A (a:A) b, a::b=[a]++b).
              simpl.
              reflexivity.
           intros.
           rewrite H1.
           rewrite app_assoc.
          reflexivity.
        rewrite H1.
        eapply IHal.
        intros.
        apply H.
        simpl.
        right.
        apply H2.
Qed.

Theorem WfConcatActionT_GatherActions1:
    forall (k_out:Kind) (k_in:Kind) (al:list (ActionT _ k_in)) (cont: list (Expr _ (SyntaxKind k_in)) -> ActionT _ k_out) r,
    (forall a c, In a al -> WfConcatActionT a c) ->
    (forall x, WfConcatActionT (cont x) r) ->
    WfConcatActionT (gatherActions al cont) r.
Proof.
    intros.
    assert (cont = (fun x => cont ([]++x))).
        simpl.
        eapply functional_extensionality.
        simpl.
        reflexivity.
    rewrite H1.
    eapply WfConcatActionT_GatherActions1_Helper.
    + apply H.
    + apply H0.
Qed.

Theorem forall_implies_in: forall T T' T'' (f:T->T') (c:T'->T''->Prop) l x (y:T''),
      (forall fx, c (f fx) y) ->
      In x (List.map f l) -> c x y.
Proof.
    intros.
    induction l.
    + simpl in H0.
      inversion H0.
    + simpl in H0.
      inversion H0;subst;clear H0.
      - apply H.
      - apply IHl.
        apply H1.
Qed.

Theorem forall_implies_in2: forall T T' (f:T->T') l x,
      In x (List.map f l) -> (exists xx, (x=(f xx) /\ In xx l)).
Proof.
    induction l.
    intros.
    + inversion H.
    + simpl.
      intros.
      inversion H;subst;clear H.
      eapply ex_intro.
      - split.
        * reflexivity.
        * left.
          reflexivity.
      - apply IHl in H0.
        inversion H0;subst;clear H0.
        inversion H;subst;clear H.
        eapply ex_intro.
        split.
        * reflexivity.
        * right.
          apply H1.
Qed.

Theorem in_tag: forall A (x:nat*A) (l:list A), In x (tag l) -> In (snd x) l.
Proof.
  unfold tag.
  assert (forall A (x: nat * A) (l : list A) n, In x (tagFrom n l) -> In (snd x) l).
  + intros A x l.
    induction l.
    - intros.
      inversion H.
    - intros.
      simpl in H.
      inversion H;subst;clear H.
      * simpl.
        left.
        reflexivity.
      * simpl.
        right.
        eapply IHl.
        apply H0.
  + intros.
    eapply H.
    apply H0.
Qed.

Lemma WfConcatActionT_convertLetExprSyntax_ActionT:
  forall (k:Kind) x r,
      @WfConcatActionT k (convertLetExprSyntax_ActionT x) r.
Proof.
    intros.
    induction x.
    + discharge_wf.
    + discharge_wf.
    + discharge_wf.
    + discharge_wf.
Qed.

Ltac Solve_WfConcatActionT db :=
  match goal with
  | |- forall _, _ => intros;Solve_WfConcatActionT db
  | |- WfConcatActionT (LETA _ : _ <- _ ; _) _ => apply WfConcatLetAction;Solve_WfConcatActionT db
  | |- WfConcatActionT (IfElse _ _ _ _) _ => apply  WfConcatIfElse;Solve_WfConcatActionT db
  | |- WfConcatActionT (Return _) _ => apply  WfConcatReturn;Solve_WfConcatActionT db
  | |- WfConcatActionT (Sys _ _) _ => apply  WfConcatSys;Solve_WfConcatActionT db
  | |- WfConcatActionT (LetExpr _ _) _ => apply  WfConcatLetExpr;Solve_WfConcatActionT db
  | |- WfConcatActionT (ReadReg _ _ _) _ => apply  WfConcatReadReg;Solve_WfConcatActionT db
  | |- WfConcatActionT (WriteReg _ _ _) _ => apply  WfConcatWriteReg;Solve_WfConcatActionT db
  | |- WfConcatActionT (MCall _ _ _ _) _ => apply  WfConcatMCall;Solve_WfConcatActionT db
  | |- WfConcatActionT (convertLetExprSyntax_ActionT _) _ => apply WfConcatActionT_convertLetExprSyntax_ActionT
  | |- WfConcatActionT (gatherActions _ _) _ => solve [
             apply WfConcatActionT_GatherActions1;[
                       let a := fresh in let c := fresh in let H := fresh in
                           intros a c H;
                           eapply forall_implies_in in H;[
                               apply H |
                               (try Solve_WfConcatActionT db)] |
                       (try Solve_WfConcatActionT db)]]
  | |- ~ False => let X := fresh in intro X;inversion X
  | |- _ => progress (autounfold with db);Solve_WfConcatActionT db
  | |- _ => idtac
  end.

