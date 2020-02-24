Require Import Kami.Notations.
Require Import Kami.Syntax.
Require Import List.
Require Import Kami.Notations_rewrites.
Require Import Program.Equality.
Require Import Kami.kami_rewrites_reflection_pre.
Require Import Kami.kami_rewrites_reflection_soundTop_theorems.

Theorem KRSimplifySound_list_string: forall e,
    KRExprDenote_list_string e = KRExprDenote_list_string (KRSimplify_list_string e).
Proof.
  KRSimplifySound_setup KRExpr_list_string_mut H H0 H1.
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

Theorem KRSimplifySound_list_list_string: forall e,
    KRExprDenote_list_list_string e = KRExprDenote_list_list_string (KRSimplify_list_list_string e).
Proof.
  KRSimplifySound_setup KRExpr_list_list_string_mut H H0 H1.
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

Theorem KRSimplifySound_Prop: forall e,
    KRExprDenote_Prop e = KRExprDenote_Prop (KRSimplify_Prop e).
Proof.
  KRSimplifySound_setup KRExpr_Prop_mut H H0 H1.
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

