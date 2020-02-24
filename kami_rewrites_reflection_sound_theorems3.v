Require Import Kami.Notations.
Require Import Kami.Syntax.
Require Import List.
Require Import Kami.Notations_rewrites.
Require Import Program.Equality.
Require Import Kami.kami_rewrites_reflection_pre.
Require Import Kami.kami_rewrites_reflection_soundTop_theorems.

Theorem KRSimplifySound_list_list_ModuleElt: forall e,
    KRExprDenote_list_list_ModuleElt e = KRExprDenote_list_list_ModuleElt (KRSimplify_list_list_ModuleElt e).
Proof.
  KRSimplifySound_setup KRExpr_list_list_ModuleElt_mut H H0 H1.
  repeat KRSimplifySound_unit.
  repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
    replace (KRExprDenote_string k1 = KRExprDenote_string (KRSimplify_string k)) with
        (KRExprDenote_string (KRSimplify_string k) = KRExprDenote_string k1). reflexivity.
    apply my_eq_refl.
  - repeat KRSimplifySound_crunch.
    erewrite sdisjPrefix_false.
    + reflexivity.
    + rewrite HeqH2.
      reflexivity.
  - repeat KRSimplifySound_crunch.
    replace (KRExprDenote_RegInitT k1 = KRExprDenote_RegInitT (KRSimplify_RegInitT k)) with
        (KRExprDenote_RegInitT (KRSimplify_RegInitT k) = KRExprDenote_RegInitT k1). reflexivity.
    apply my_eq_refl.
  - repeat KRSimplifySound_crunch.
    replace (KRExprDenote_Rule k1 = KRExprDenote_Rule (KRSimplify_Rule k)) with
        (KRExprDenote_Rule (KRSimplify_Rule k) = KRExprDenote_Rule k1). reflexivity.
    apply my_eq_refl.
  - repeat KRSimplifySound_crunch.
    replace (KRExprDenote_DefMethT k1 = KRExprDenote_DefMethT (KRSimplify_DefMethT k)) with
        (KRExprDenote_DefMethT (KRSimplify_DefMethT k) = KRExprDenote_DefMethT k1). reflexivity.
    apply my_eq_refl.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
Qed.

Theorem KRSimplifySound_BaseModule: forall e,
    KRExprDenote_BaseModule e = KRExprDenote_BaseModule (KRSimplify_BaseModule e).
Proof.
  KRSimplifySound_setup KRExpr_BaseModule_mut H H0 H1.
  repeat KRSimplifySound_unit.
  repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
    replace (KRExprDenote_string k1 = KRExprDenote_string (KRSimplify_string k)) with
        (KRExprDenote_string (KRSimplify_string k) = KRExprDenote_string k1). reflexivity.
    apply my_eq_refl.
  - repeat KRSimplifySound_crunch.
    erewrite sdisjPrefix_false.
    + reflexivity.
    + rewrite HeqH2.
      reflexivity.
  - repeat KRSimplifySound_crunch.
    replace (KRExprDenote_RegInitT k1 = KRExprDenote_RegInitT (KRSimplify_RegInitT k)) with
        (KRExprDenote_RegInitT (KRSimplify_RegInitT k) = KRExprDenote_RegInitT k1). reflexivity.
    apply my_eq_refl.
  - repeat KRSimplifySound_crunch.
    replace (KRExprDenote_Rule k1 = KRExprDenote_Rule (KRSimplify_Rule k)) with
        (KRExprDenote_Rule (KRSimplify_Rule k) = KRExprDenote_Rule k1). reflexivity.
    apply my_eq_refl.
  - repeat KRSimplifySound_crunch.
    replace (KRExprDenote_DefMethT k1 = KRExprDenote_DefMethT (KRSimplify_DefMethT k)) with
        (KRExprDenote_DefMethT (KRSimplify_DefMethT k) = KRExprDenote_DefMethT k1). reflexivity.
    apply my_eq_refl.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
Qed.

Theorem KRSimplifySound_RegFileBase: forall e,
    KRExprDenote_RegFileBase e = KRExprDenote_RegFileBase (KRSimplify_RegFileBase e).
Proof.
  intros.
  destruct e. reflexivity.
Qed.

Theorem KRSimplifySound_CallWithSign: forall e,
    KRExprDenote_CallWithSign e = KRExprDenote_CallWithSign (KRSimplify_CallWithSign e).
Proof.
  intros.
  destruct e. reflexivity.
Qed.

Theorem KRSimplifySound_list_CallWithSign: forall e,
    KRExprDenote_list_CallWithSign e = KRExprDenote_list_CallWithSign (KRSimplify_list_CallWithSign e).
Proof.
  KRSimplifySound_setup KRExpr_list_CallWithSign_mut H H0 H1.
  repeat KRSimplifySound_unit.
  repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
    replace (KRExprDenote_string k1 = KRExprDenote_string (KRSimplify_string k)) with
        (KRExprDenote_string (KRSimplify_string k) = KRExprDenote_string k1). reflexivity.
    apply my_eq_refl.
  - repeat KRSimplifySound_crunch.
    erewrite sdisjPrefix_false.
    + reflexivity.
    + rewrite HeqH2.
      reflexivity.
  - repeat KRSimplifySound_crunch.
    replace (KRExprDenote_RegInitT k1 = KRExprDenote_RegInitT (KRSimplify_RegInitT k)) with
        (KRExprDenote_RegInitT (KRSimplify_RegInitT k) = KRExprDenote_RegInitT k1). reflexivity.
    apply my_eq_refl.
  - repeat KRSimplifySound_crunch.
    replace (KRExprDenote_Rule k1 = KRExprDenote_Rule (KRSimplify_Rule k)) with
        (KRExprDenote_Rule (KRSimplify_Rule k) = KRExprDenote_Rule k1). reflexivity.
    apply my_eq_refl.
  - repeat KRSimplifySound_crunch.
    replace (KRExprDenote_DefMethT k1 = KRExprDenote_DefMethT (KRSimplify_DefMethT k)) with
        (KRExprDenote_DefMethT (KRSimplify_DefMethT k) = KRExprDenote_DefMethT k1). reflexivity.
    apply my_eq_refl.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
  - repeat KRSimplifySound_crunch.
Qed.

