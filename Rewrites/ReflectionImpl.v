Require Import Kami.Notations.
Require Import Kami.Syntax.
Require Import List.
Require Import Kami.Rewrites.Notations_rewrites.
Require Import Program.Equality.
Require Import Kami.Rewrites.ReflectionPre.
Require Import Kami.Rewrites.ReflectionSoundTopTheorems.
Require Import Kami.Rewrites.ReflectionSoundTheorems1.
Require Import Kami.Rewrites.ReflectionSoundTheorems2.
Require Import Kami.WfMod_Helper.

Definition KRSimplifyTop_ImplProp (e: KRExpr_Prop) : KRExpr_Prop :=
  match e with
  | KRDisjKey_RegInitT a b => match a with
                              | KRApp_list_RegInitT x y => KRAnd_Prop (KRDisjKey_RegInitT x b) (KRDisjKey_RegInitT y b)
                              | KRCons_list_RegInitT x y => KRAnd_Prop (KRNot_Prop (KRIn_string_Prop (KRfst_RegInitT_string x) (KRmap_RegInitT_string KRfst_RegInitT_string_Func b))) (KRDisjKey_RegInitT y b)
                              | KRNil_list_RegInitT => KRTrue_Prop
                              | _ => match b with
                                     | KRApp_list_RegInitT x y => KRAnd_Prop (KRDisjKey_RegInitT a x) (KRDisjKey_RegInitT a y)
                                     | KRCons_list_RegInitT x y => KRAnd_Prop (KRNot_Prop (KRIn_string_Prop (KRfst_RegInitT_string x) (KRmap_RegInitT_string KRfst_RegInitT_string_Func a))) (KRDisjKey_RegInitT a y)
                                     | KRNil_list_RegInitT => KRTrue_Prop
                                     | _ => KRDisjKey_RegInitT a b
                                     end
                              end
  | KRDisjKey_DefMethT a b => match a with
                              | KRApp_list_DefMethT x y => KRAnd_Prop (KRDisjKey_DefMethT x b) (KRDisjKey_DefMethT y b)
                              | KRCons_list_DefMethT x y => KRAnd_Prop (KRNot_Prop (KRIn_string_Prop (KRfst_DefMethT_string x) (KRmap_DefMethT_string KRfst_DefMethT_string_Func b))) (KRDisjKey_DefMethT y b)
                              | KRNil_list_DefMethT => KRTrue_Prop
                              | _ => match b with
                                     | KRApp_list_DefMethT x y => KRAnd_Prop (KRDisjKey_DefMethT a x) (KRDisjKey_DefMethT a y)
                                     | KRCons_list_DefMethT x y => KRAnd_Prop (KRNot_Prop (KRIn_string_Prop (KRfst_DefMethT_string x) (KRmap_DefMethT_string KRfst_DefMethT_string_Func a))) (KRDisjKey_DefMethT a y)
                                     | KRNil_list_DefMethT => KRTrue_Prop
                                     | _ => KRDisjKey_DefMethT a b
                                     end
                              end
  | KRDisjKey_Rule a b => match a with
                          | KRApp_list_Rule x y => KRAnd_Prop (KRDisjKey_Rule x b) (KRDisjKey_Rule y b)
                          | KRCons_list_Rule x y => KRAnd_Prop (KRNot_Prop (KRIn_string_Prop (KRfst_Rule_string x) (KRmap_Rule_string KRfst_Rule_string_Func b))) (KRDisjKey_Rule y b)
                          | KRNil_list_Rule => KRTrue_Prop
                          | _ => match b with
                                 | KRApp_list_Rule x y => KRAnd_Prop (KRDisjKey_Rule a x) (KRDisjKey_Rule a y)
                                 | KRCons_list_Rule x y => KRAnd_Prop (KRNot_Prop (KRIn_string_Prop (KRfst_Rule_string x) (KRmap_Rule_string KRfst_Rule_string_Func a))) (KRDisjKey_Rule a y)
                                 | KRNil_list_Rule => KRTrue_Prop
                                 | _ => KRDisjKey_Rule a b
                                 end
                          end
  | KRAnd_Prop a KRTrue_Prop => a
  | KRAnd_Prop a KRFalse_Prop => KRFalse_Prop
  | KRAnd_Prop KRTrue_Prop a => a
  | KRAnd_Prop KRFalse_Prop a => KRFalse_Prop
  | KROr_Prop a KRTrue_Prop => KRTrue_Prop
  | KROr_Prop a KRFalse_Prop => a
  | KROr_Prop KRTrue_Prop a => KRTrue_Prop
  | KROr_Prop KRFalse_Prop a => a
  | KRNot_Prop (KRTrue_Prop) => KRFalse_Prop
  | KRNot_Prop (KRFalse_Prop) => KRTrue_Prop
  | KRNot_Prop (KRNot_Prop a) => a
  (*| KRNot_Prop (KRAnd_Prop a b) => (KROr_Prop (KRNot_Prop a) (KRNot_Prop b))
  | KRNot_Prop (KROr_Prop a b) => (KRAnd_Prop (KRNot_Prop a) (KRNot_Prop b))*)
  | KRIn_string_Prop x (KRApp_list_string a b) => (KROr_Prop (KRIn_string_Prop x a) (KRIn_string_Prop x b))
  | KRIn_string_Prop x (KRCons_list_string a b) => (KROr_Prop (KREq_string_Prop x a) (KRIn_string_Prop x b))
  | KRIn_string_Prop x (KRNil_list_string) => KRFalse_Prop
  | KRIn_RegInitT_Prop x (KRApp_list_RegInitT a b) => (KROr_Prop (KRIn_RegInitT_Prop x a) (KRIn_RegInitT_Prop x b))
  | KRIn_RegInitT_Prop x (KRCons_list_RegInitT a b) => (KROr_Prop (KREq_RegInitT_Prop x a) (KRIn_RegInitT_Prop x b))
  | KRIn_RegInitT_Prop x (KRNil_list_RegInitT) => KRFalse_Prop
  | KRIn_Rule_Prop x (KRApp_list_Rule a b) => (KROr_Prop (KRIn_Rule_Prop x a) (KRIn_Rule_Prop x b))
  | KRIn_Rule_Prop x (KRCons_list_Rule a b) => (KROr_Prop (KREq_Rule_Prop x a) (KRIn_Rule_Prop x b))
  | KRIn_Rule_Prop x (KRNil_list_Rule) => KRFalse_Prop
  | KRIn_DefMethT_Prop x (KRApp_list_DefMethT a b) => (KROr_Prop (KRIn_DefMethT_Prop x a) (KRIn_DefMethT_Prop x b))
  | KRIn_DefMethT_Prop x (KRCons_list_DefMethT a b) => (KROr_Prop (KREq_DefMethT_Prop x a) (KRIn_DefMethT_Prop x b))
  | KRIn_DefMethT_Prop x (KRNil_list_DefMethT) => KRFalse_Prop
  | KREq_string_Prop (KRstring_append p (KRConst_string a)) (KRstring_append q (KRConst_string b)) => if sdisjPrefix (srev a) (srev b) then KRFalse_Prop else e
  (*| KREq_string_Prop (KRstring_append (KRVar_string p) a) (KRstring_append (KRVar_string q) b) => if String.eqb p q then (KREq_string_Prop a b) else KREq_string_Prop (KRstring_append (KRVar_string p) a) (KRstring_append (KRVar_string q) b)
  | KREq_string_Prop (KRVar_string a) (KRVar_string b) => if String.eqb a b then KRTrue_Prop else
                                                            (KREq_string_Prop (KRVar_string a) (KRVar_string b))*)
  | e => e
  end.

Fixpoint KRSimplify_ImplProp(p:KRExpr_Prop) :=
       KRSimplifyTop_ImplProp (match p with
                           | KRAnd_Prop a b => KRAnd_Prop (KRSimplify_ImplProp a) (KRSimplify_ImplProp b)
                           | KROr_Prop a b => KROr_Prop (KRSimplify_ImplProp a) (KRSimplify_ImplProp b)
                           | KRNot_Prop a => KRNot_Prop (KRSimplify_ImplProp a)
                           | KRIn_string_Prop a b => KRIn_string_Prop (KRSimplify_string a) (KRSimplify_list_string b)
                           | KRIn_RegInitT_Prop a b => KRIn_RegInitT_Prop (KRSimplify_RegInitT a) (KRSimplify_list_RegInitT b)
                           | KRIn_DefMethT_Prop a b => KRIn_DefMethT_Prop (KRSimplify_DefMethT a) (KRSimplify_list_DefMethT b)
                           | KRIn_Rule_Prop a b => KRIn_Rule_Prop (KRSimplify_Rule a) (KRSimplify_list_Rule b)
                           | KRDisjKey_RegInitT a b => KRDisjKey_RegInitT (KRSimplify_list_RegInitT a) (KRSimplify_list_RegInitT b)
                           | KRDisjKey_DefMethT a b => KRDisjKey_DefMethT (KRSimplify_list_DefMethT a) (KRSimplify_list_DefMethT b)
                           | KRDisjKey_Rule a b => KRDisjKey_Rule (KRSimplify_list_Rule a) (KRSimplify_list_Rule b)
                           | KREq_string_Prop a b => KREq_string_Prop (KRSimplify_string a) (KRSimplify_string b)
                           | KREq_RegInitT_Prop a b => KREq_RegInitT_Prop (KRSimplify_RegInitT a) (KRSimplify_RegInitT b)
                           | KREq_Rule_Prop a b => KREq_Rule_Prop (KRSimplify_Rule a) (KRSimplify_Rule b)
                           | KREq_DefMethT_Prop a b => KREq_DefMethT_Prop (KRSimplify_DefMethT a) (KRSimplify_DefMethT b)
                           | p => p
                           end).

Theorem KRSimplify_ImplProp_KRAnd_Prop: forall a b,
     KRSimplify_ImplProp (KRAnd_Prop a b)= KRSimplifyTop_ImplProp (KRAnd_Prop (KRSimplify_ImplProp a) (KRSimplify_ImplProp b)).
Proof.
  reflexivity.
Qed.

Hint Rewrite KRSimplify_ImplProp_KRAnd_Prop : KRSimplify.

Theorem KRSimplify_ImplProp_KROr_Prop: forall a b,
     KRSimplify_ImplProp (KROr_Prop a b)= KRSimplifyTop_ImplProp (KROr_Prop (KRSimplify_ImplProp a) (KRSimplify_ImplProp b)).
Proof.
  reflexivity.
Qed.

Hint Rewrite KRSimplify_ImplProp_KROr_Prop : KRSimplify.

Theorem KRSimplify_ImplProp_KRNot_Prop: forall a,
     KRSimplify_ImplProp (KRNot_Prop a)= KRSimplifyTop_ImplProp (KRNot_Prop (KRSimplify_ImplProp a)).
Proof.
  reflexivity.
Qed.

Hint Rewrite KRSimplify_ImplProp_KRNot_Prop : KRSimplify.

Theorem KRSimplify_ImplProp_KRIn_string_Prop: forall a b,
     KRSimplify_ImplProp (KRIn_string_Prop a b)= KRSimplifyTop_ImplProp (KRIn_string_Prop (KRSimplify_string a) (KRSimplify_list_string b)).
Proof.
  reflexivity.
Qed.

Hint Rewrite KRSimplify_ImplProp_KRIn_string_Prop : KRSimplify.

Theorem KRSimplify_ImplProp_KRIn_RegInitT_Prop: forall a b,
     KRSimplify_ImplProp (KRIn_RegInitT_Prop a b)= KRSimplifyTop_ImplProp (KRIn_RegInitT_Prop (KRSimplify_RegInitT a) (KRSimplify_list_RegInitT b)).
Proof.
  reflexivity.
Qed.

Hint Rewrite KRSimplify_ImplProp_KRIn_RegInitT_Prop : KRSimplify.

Theorem KRSimplify_ImplProp_KRIn_DefMethT_Prop: forall a b,
     KRSimplify_ImplProp (KRIn_DefMethT_Prop a b)= KRSimplifyTop_ImplProp (KRIn_DefMethT_Prop (KRSimplify_DefMethT a) (KRSimplify_list_DefMethT b)).
Proof.
  reflexivity.
Qed.

Hint Rewrite KRSimplify_ImplProp_KRIn_DefMethT_Prop : KRSimplify.

Theorem KRSimplify_ImplProp_KRIn_Rule_Prop: forall a b,
     KRSimplify_ImplProp (KRIn_Rule_Prop a b)= KRSimplifyTop_ImplProp (KRIn_Rule_Prop (KRSimplify_Rule a) (KRSimplify_list_Rule b)).
Proof.
  reflexivity.
Qed.

Hint Rewrite KRSimplify_ImplProp_KRIn_Rule_Prop : KRSimplify.

Theorem KRSimplify_ImplProp_KRDisjKey_RegInitT_Prop: forall a b,
     KRSimplify_ImplProp (KRDisjKey_RegInitT a b)= KRSimplifyTop_ImplProp (KRDisjKey_RegInitT (KRSimplify_list_RegInitT a) (KRSimplify_list_RegInitT b)).
Proof.
  reflexivity.
Qed.

Hint Rewrite KRSimplify_ImplProp_KRDisjKey_RegInitT_Prop : KRSimplify.

Theorem KRSimplify_ImplProp_KRDisjKey_DefMethT_Prop: forall a b,
     KRSimplify_ImplProp (KRDisjKey_DefMethT a b)= KRSimplifyTop_ImplProp (KRDisjKey_DefMethT (KRSimplify_list_DefMethT a) (KRSimplify_list_DefMethT b)).
Proof.
  reflexivity.
Qed.

Hint Rewrite KRSimplify_ImplProp_KRDisjKey_DefMethT_Prop : KRSimplify.

Theorem KRSimplify_ImplProp_KRDisjKey_Rule_Prop: forall a b,
     KRSimplify_ImplProp (KRDisjKey_Rule a b)= KRSimplifyTop_ImplProp (KRDisjKey_Rule (KRSimplify_list_Rule a) (KRSimplify_list_Rule b)).
Proof.
  reflexivity.
Qed.

Hint Rewrite KRSimplify_ImplProp_KRDisjKey_Rule_Prop : KRSimplify.

Theorem KRSimplify_ImplProp_KREq_string_Prop: forall a b,
     KRSimplify_ImplProp (KREq_string_Prop a b)= KRSimplifyTop_ImplProp (KREq_string_Prop (KRSimplify_string a) (KRSimplify_string b)).
Proof.
  reflexivity.
Qed.

Hint Rewrite KRSimplify_ImplProp_KREq_string_Prop : KRSimplify.

Theorem KRSimplify_ImplProp_KREq_RegInitT_Prop: forall a b,
     KRSimplify_ImplProp (KREq_RegInitT_Prop a b)= KRSimplifyTop_ImplProp (KREq_RegInitT_Prop (KRSimplify_RegInitT a) (KRSimplify_RegInitT b)).
Proof.
  reflexivity.
Qed.

Hint Rewrite KRSimplify_ImplProp_KREq_RegInitT_Prop : KRSimplify.

Theorem KRSimplify_ImplProp_KREq_DefMethT_Prop: forall a b,
     KRSimplify_ImplProp (KREq_DefMethT_Prop a b)= KRSimplifyTop_ImplProp (KREq_DefMethT_Prop (KRSimplify_DefMethT a) (KRSimplify_DefMethT b)).
Proof.
  reflexivity.
Qed.

Hint Rewrite KRSimplify_ImplProp_KREq_DefMethT_Prop : KRSimplify.

Theorem KRSimplify_ImplProp_KREq_Rule_Prop: forall a b,
     KRSimplify_ImplProp (KREq_Rule_Prop a b)= KRSimplifyTop_ImplProp (KREq_Rule_Prop (KRSimplify_Rule a) (KRSimplify_Rule b)).
Proof.
  reflexivity.
Qed.

Hint Rewrite KRSimplify_ImplProp_KREq_Rule_Prop : KRSimplify.

Theorem sdisjPrefix_false': forall p1 p2 s1 s2,
    sdisjPrefix (srev s1) (srev s2)=true -> (p1++s1=p2++s2)%string -> False.
Proof.
  intros p1 p2 s1 s2.
  repeat (rewrite <- sappend_append).
  assert ((p2++s2)%string=sappend p2 s2).
  - rewrite <- sappend_append.
    reflexivity.
  - rewrite H.
    intros.
    eapply sdisjPrefix_sappend_false.
    + apply H0.
    + apply H1.
Qed.

Ltac unitSolve :=
  simpl in *; simpl;
  match goal with
  | H: ?X |- ?X => apply H
  | |- True => apply I
  | H: False |- _ => inversion H
  | H: _ /\ _ |- _ => inversion H; subst; clear H; unitSolve
  | H: _ \/ _ |- _ => inversion H; subst; clear H; unitSolve
  | |- _ \/ _ => left; solve [unitSolve]
  | |- _ \/ _ => right; solve [unitSolve]
  | |- _ /\ _ => split; unitSolve
  | |- DisjKey _ [] => apply DisjKey_nil2
  | |- DisjKey [] _ => apply DisjKey_nil1
  | |- DisjKey (_::_) _ => apply DisjKey_Cons1; unitSolve
  | |- DisjKey _ (_::_) => apply DisjKey_Cons2; unitSolve
  | |- DisjKey (_++_) _ => apply DisjKey_Append1; unitSolve
  | |- DisjKey _ (_++_) => apply DisjKey_Append2; unitSolve
  | |- { _=_ }+{ _<>_ } => repeat (decide equality)
  | |- forall _,_ => intros; unitSolve
  end.

Theorem KRSimplifyTopSound_ImplProp: forall e,
    KRExprDenote_Prop (KRSimplifyTop_ImplProp e) -> KRExprDenote_Prop e.
Proof.
  intros.
  destruct e; try unitSolve.
  - destruct e1; destruct e2; split; try (unitSolve).
  - destruct e1; destruct e2; try (unitSolve).
  - destruct e; try (unitSolve).
    + simpl.
      intro X.
      apply X.
    + simpl.
      intro X.
      simpl in H.
      apply X in H.
      inversion H.
  - destruct k0; try unitSolve.
    + simpl in H.
      simpl.
      inversion H; subst; clear H.
      * left.
        rewrite H0.
        reflexivity.
      * right.
        apply H0.
    + simpl in H.
      simpl.
      rewrite in_app.
      try unitSolve.
  - destruct k; destruct k0; try unitSolve; try (destruct k2; unitSolve).
    destruct k2; try unitSolve.
    destruct k0_2; try unitSolve.
    simpl in H.
    simpl.
    remember (sdisjPrefix (srev s) (srev s0)).
    destruct b.
    * simpl in H.
      inversion H.
    * simpl in H.
      apply H.
  - destruct k0; try unitSolve.
    + simpl in H.
      simpl.
      inversion H; subst; clear H.
      * left.
        rewrite H0.
        reflexivity.
      * right.
        apply H0.
    + simpl in H.
      simpl.
      rewrite in_app.
      try unitSolve.
  - destruct k0; try unitSolve.
    + simpl in H.
      simpl.
      inversion H; subst; clear H.
      * left.
        rewrite H0.
        reflexivity.
      * right.
        apply H0.
    + simpl in H.
      simpl.
      rewrite in_app.
      try unitSolve.
  - destruct k0; try unitSolve.
    + simpl in H.
      simpl.
      inversion H; subst; clear H.
      * left.
        rewrite H0.
        reflexivity.
      * right.
        apply H0.
    + simpl in H.
      simpl.
      rewrite in_app.
      try unitSolve.
  - destruct k; destruct k0; try unitSolve.
  - destruct k; destruct k0; try unitSolve.
  - destruct k; destruct k0; try unitSolve.
Qed.

Hint Rewrite KRSimplifyTopSound_Prop : KRSimplify.

Theorem KRSimplifySound_ImplProp: forall e,
    KRExprDenote_Prop (KRSimplify_ImplProp e) -> KRExprDenote_Prop e.
Proof.
    induction e; try (autorewrite with KRSimplify); try (simpl); try (rewrite IHe1); try (rewrite IHe2); try (rewrite IHe); try (autorewrite with KRSimplify); try (reflexivity).
Qed.

Hint Rewrite KRSimplifySound_Prop : KRSimplify.

(*Goal forall (a:ModuleElt) (b:list ModuleElt) c, app (cons a b) c=cons a (app b c).
  intros.
  match goal with
  | |- ?A = ?B => let x := (ltac:(KRExprReify A (KRTypeList (KRTypeElem KRElemModuleElt)))) in
                  change A with (KRExprDenote_list_ModuleElt x);
                    rewrite KRSimplifySound_list_ModuleElt;
                    cbv [KRSimplify_list_ModuleElt KRSimplifyTop_list_ModuleElt KRExprDenote_list_ModuleElt KRExprDenote_ModuleElt KRSimplifyTop_ModuleElt KRSimplify_ModuleElt]
  end.
Abort.*)

Ltac KRSimplifyTac e tp :=
  let x := (ltac:(KRExprReify e tp)) in
  let denote := match tp with
                | (KRTypeElem KRElemRegInitT) => KRExprDenote_RegInitT
                | (KRTypeElem KRElemRule) => KRExprDenote_Rule
                | (KRTypeElem KRElemDefMethT) => KRExprDenote_DefMethT
                | (KRTypeElem KRElemModuleElt) => KRExprDenote_ModuleElt
                | (KRTypeList (KRTypeElem KRElemRegInitT)) => KRExprDenote_list_RegInitT
                | (KRTypeList (KRTypeElem KRElemRule)) => KRExprDenote_list_Rule
                | (KRTypeList (KRTypeElem KRElemDefMethT)) => KRExprDenote_list_DefMethT
                | (KRTypeList (KRTypeElem KRElemModuleElt)) => KRExprDenote_list_ModuleElt
                | (KRTypeList (KRTypeList (KRTypeElem KRElemRegInitT))) => KRExprDenote_list_list_RegInitT
                | (KRTypeList (KRTypeList (KRTypeElem KRElemRule))) => KRExprDenote_list_list_Rule
                | (KRTypeList (KRTypeList (KRTypeElem KRElemDefMethT))) => KRExprDenote_list_list_DefMethT
                | (KRTypeList (KRTypeList (KRTypeElem KRElemModuleElt))) => KRExprDenote_list_list_ModuleElt
                | (KRTypeElem KRElemBaseModule) => KRExprDenote_BaseModule
                | (KRTypeElem KRElemMod) => KRExprDenote_Mod
                | (KRTypeList (KRTypeElem KRElemMod)) => KRExprDenote_list_Mod
                | (KRTypeElem KRElemString) => KRExprDenote_string
                | (KRTypeList (KRTypeElem KRElemString)) => KRExprDenote_list_string
                | (KRTypeList (KRTypeList (KRTypeElem KRElemString))) => KRExprDenote_list_list_string
                | (KRTypeElem KRElemRegFileBase) => KRExprDenote_RegFileBase
                | (KRTypeList (KRTypeElem KRElemRegFileBase)) => KRExprDenote_list_RegFileBase
                | (KRTypeElem KRElemCallWithSign) => KRExprDenote_CallWithSign
                | (KRTypeList (KRTypeElem KRElemCallWithSign)) => KRExprDenote_list_CallWithSign
                | (KRTypeList (KRTypeList (KRTypeElem KRElemCallWithSign))) => KRExprDenote_list_list_CallWithSign
                | (KRTypeElem KRElemProp) => KRExprDenote_Prop
                end in
  let simplifySound := match tp with
                | (KRTypeElem KRElemRegInitT) => KRSimplifySound_RegInitT
                | (KRTypeElem KRElemRule) => KRSimplifySound_Rule
                | (KRTypeElem KRElemDefMethT) => KRSimplifySound_DefMethT
                | (KRTypeElem KRElemModuleElt) => KRSimplifySound_ModuleElt
                | (KRTypeList (KRTypeElem KRElemRegInitT)) => KRSimplifySound_list_RegInitT
                | (KRTypeList (KRTypeElem KRElemRule)) => KRSimplifySound_list_Rule
                | (KRTypeList (KRTypeElem KRElemDefMethT)) => KRSimplifySound_list_DefMethT
                | (KRTypeList (KRTypeElem KRElemModuleElt)) => KRSimplifySound_list_ModuleElt
                | (KRTypeList (KRTypeList (KRTypeElem KRElemRegInitT))) => KRSimplifySound_list_RegInitT
                | (KRTypeList (KRTypeList (KRTypeElem KRElemRule))) => KRSimplifySound_list_Rule
                | (KRTypeList (KRTypeList (KRTypeElem KRElemDefMethT))) => KRSimplifySound_list_DefMethT
                | (KRTypeList (KRTypeList (KRTypeElem KRElemModuleElt))) => KRSimplifySound_list_list_ModuleElt
                | (KRTypeElem KRElemString) => KRSimplifySound_string
                | (KRTypeList (KRTypeElem KRElemString)) => KRSimplifySound_list_string
                | (KRTypeList (KRTypeList (KRTypeElem KRElemString))) => KRSimplifySound_list_list_string
                | (KRTypeElem KRElemRegFileBase) => KRSimplifySound_RegFileBase
                | (KRTypeList (KRTypeElem KRElemRegFileBase)) => KRSimplify_list_RegFileBase
                | (KRTypeElem KRElemCallWithSign) => KRSimplifySound_CallWithSign
                | (KRTypeList (KRTypeElem KRElemCallWithSign)) => KRSimplify_list_CallWithSign
                | (KRTypeElem KRElemBaseModule) => KRSimplifySound_BaseModule
                | (KRTypeElem KRElemMod) => KRSimplifySound_Mod
                | (KRTypeList (KRTypeElem KRElemMod)) => KRSimplifySound_list_Mod
                | (KRTypeElem KRElemProp) => KRSimplifySound_Prop
                end in
  change e with (denote x);repeat (rewrite <- simplifySound;cbv [
                sappend srev sdisjPrefix String.eqb Ascii.eqb Bool.eqb
                KRSimplify_RegInitT KRSimplifyTop_RegInitT
                KRSimplify_RegInitValT KRSimplifyTop_RegInitValT
                KRSimplify_Rule KRSimplifyTop_Rule
                KRSimplify_DefMethT KRSimplifyTop_DefMethT
                KRSimplify_ModuleElt KRSimplifyTop_ModuleElt
                KRSimplify_list_RegInitT KRSimplifyTop_list_RegInitT
                KRSimplify_list_Rule KRSimplifyTop_list_Rule
                KRSimplify_list_DefMethT KRSimplifyTop_list_DefMethT
                KRSimplify_list_ModuleElt KRSimplifyTop_list_ModuleElt
                KRSimplify_list_list_RegInitT KRSimplifyTop_list_list_RegInitT
                KRSimplify_list_list_Rule KRSimplifyTop_list_list_Rule
                KRSimplify_list_list_DefMethT KRSimplifyTop_list_list_DefMethT
                KRSimplify_list_list_ModuleElt KRSimplifyTop_list_list_ModuleElt
                KRSimplify_BaseModule KRSimplifyTop_BaseModule
                KRSimplify_RegFileBase KRSimplifyTop_RegFileBase
                KRSimplify_list_RegFileBase KRSimplifyTop_list_RegFileBase
                KRSimplify_string KRSimplifyTop_string
                KRSimplify_list_string KRSimplifyTop_list_string
                KRSimplify_list_list_string KRSimplifyTop_list_list_string
                KRSimplify_Mod KRSimplifyTop_Mod
                KRSimplify_Mod KRSimplifyTop_list_Mod
                KRSimplify_ImplProp KRSimplifyTop_ImplProp
                                  ]);
  cbv [
      sappend srev sdisjPrefix String.eqb Ascii.eqb Bool.eqb
                KRExprDenote_RegInitT
                KRExprDenote_RegInitValT
                KRExprDenote_Rule
                KRExprDenote_DefMethT
                KRExprDenote_ModuleElt
                KRExprDenote_list_RegInitT
                KRExprDenote_list_Rule
                KRExprDenote_list_DefMethT
                KRExprDenote_ActionVoid
                KRExprDenote_MethodT
                KRExprDenote_list_ModuleElt
                KRExprDenote_list_list_RegInitT
                KRExprDenote_list_list_Rule
                KRExprDenote_list_list_DefMethT
                KRExprDenote_list_list_ModuleElt
                KRExprDenote_BaseModule
                KRExprDenote_Mod
                KRExprDenote_list_Mod
                KRExprDenote_RegFileBase
                KRExprDenote_list_RegFileBase
                KRExprDenote_string
                KRExprDenote_list_string
                KRExprDenote_list_list_string
                KRExprDenote_Prop].


(*Ltac KRPrintReify e :=
  let x := (ltac:(KRExprReify e t)) in
  let t := eval compute in (KRTypeDenote x) in
  let xx := (ltac:(KRExprReify e t)) in
      idtac t;idtac x.
 *)

Goal forall a b c d e, Registers ([a;b]++[c;d])=e.
  intros.
  match goal with
  | |- ?A = ?B => KRSimplifyTac A (KRTypeList (KRTypeElem KRElemModuleElt))
  end.
Abort.
Goal forall a b c d e, makeModule_regs [MERegister a;MERule b;MEMeth c;MERegister d]=e.
  intros.
  match goal with
  | |- ?A = ?B => 
    (*let x := (ltac:(KRExprReify A (KRTypeList (KRTypeElem KRElemRegInitT)))) in
    idtac x*)
    KRSimplifyTac A (KRTypeList (KRTypeElem KRElemRegInitT))
  end.
Abort.
Goal forall a b c d e, makeModule_rules [MERegister a;MERule b;MEMeth c;MERegister d]=e.
  intros.
  match goal with
  | |- ?A = ?B =>
      KRSimplifyTac A (KRTypeList (KRTypeElem KRElemRule))
  end.
Abort.
Goal forall a b c d e, makeModule_meths [MEMeth a;MERule b;MERegister c;MERegister d]=e.
  intros.
  match goal with
  | |- ?A = ?B => 
      KRSimplifyTac A (KRTypeList (KRTypeElem KRElemDefMethT))
  end.
Abort.
Goal forall e, makeModule_regs []=e.
  intros.
  match goal with
  | |- ?A = ?B => 
      KRSimplifyTac A (KRTypeList (KRTypeElem KRElemRegInitT))
  end.
Abort.
Goal forall proc_name, ~(( proc_name ++ "_" ++ "a")%string = (proc_name ++ "_" ++  "b")%string).
  intros.
  match goal with
  | |- ~ ?A => 
    let x := (ltac:(KRExprReify (~A) (KRTypeElem KRElemProp))) in change (~A) with (KRExprDenote_Prop x)
  end.
  rewrite <- KRSimplifySound_Prop.
  cbv [
                KRSimplify_RegInitT KRSimplifyTop_RegInitT
                KRSimplify_RegInitValT KRSimplifyTop_RegInitValT
                KRSimplify_Rule KRSimplifyTop_Rule
                KRSimplify_DefMethT KRSimplifyTop_DefMethT
                KRSimplify_ModuleElt KRSimplifyTop_ModuleElt
                KRSimplify_list_RegInitT KRSimplifyTop_list_RegInitT
                KRSimplify_list_Rule KRSimplifyTop_list_Rule
                KRSimplify_list_DefMethT KRSimplifyTop_list_DefMethT
                KRSimplify_list_ModuleElt KRSimplifyTop_list_ModuleElt
                KRSimplify_list_list_RegInitT KRSimplifyTop_list_list_RegInitT
                KRSimplify_list_list_Rule KRSimplifyTop_list_list_Rule
                KRSimplify_list_list_DefMethT KRSimplifyTop_list_list_DefMethT
                KRSimplify_list_list_ModuleElt KRSimplifyTop_list_list_ModuleElt
                KRSimplify_BaseModule KRSimplifyTop_BaseModule
                KRSimplify_RegFileBase KRSimplifyTop_RegFileBase
                KRSimplify_list_RegFileBase KRSimplifyTop_list_RegFileBase
                KRSimplify_string KRSimplifyTop_string
                KRSimplify_list_string KRSimplifyTop_list_string
                KRSimplify_list_list_string KRSimplifyTop_list_list_string
                KRSimplify_Mod KRSimplifyTop_Mod
                KRSimplify_Mod KRSimplifyTop_list_Mod
                KRSimplify_ImplProp KRSimplifyTop_ImplProp
    ].
  cbv [         sappend srev sdisjPrefix
                KRExprDenote_RegInitT
                KRExprDenote_Rule
                KRExprDenote_DefMethT
                KRExprDenote_ModuleElt
                KRExprDenote_list_RegInitT
                KRExprDenote_list_Rule
                KRExprDenote_list_DefMethT
                KRExprDenote_list_ModuleElt
                KRExprDenote_list_list_RegInitT
                KRExprDenote_list_list_Rule
                KRExprDenote_list_list_DefMethT
                KRExprDenote_list_list_ModuleElt
                KRExprDenote_BaseModule
                KRExprDenote_Mod
                KRExprDenote_list_Mod
                KRExprDenote_RegFileBase
                KRExprDenote_list_RegFileBase
                KRExprDenote_string
                KRExprDenote_list_string
                KRExprDenote_list_list_string
                KRExprDenote_Prop].
Abort.

