Require Import Kami.Notations.
Require Import Kami.Syntax.
Require Import List.
Require Import Kami.Notations_rewrites.
Require Import Program.Equality.
Require Import Kami.Rewrites.ReflectionPre.
Require Import Kami.Rewrites.ReflectionSoundTopTheorems.

Theorem KRSimplifySound_list_list_Rule: forall e,
    KRExprDenote_list_list_Rule e = KRExprDenote_list_list_Rule (KRSimplify_list_list_Rule e).
Proof.
  KRSimplifySound_setup KRExpr_list_list_Rule_mut H H0 H1.
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
  
Theorem KRSimplifySound_list_list_DefMethT: forall e,
    KRExprDenote_list_list_DefMethT e = KRExprDenote_list_list_DefMethT (KRSimplify_list_list_DefMethT e).
Proof.
  KRSimplifySound_setup KRExpr_list_list_DefMethT_mut H H0 H1.
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

Theorem KRSimplifySound_list_DefMethT: forall e,
    KRExprDenote_list_DefMethT e = KRExprDenote_list_DefMethT (KRSimplify_list_DefMethT e).
Proof.
  KRSimplifySound_setup KRExpr_list_DefMethT_mut H H0 H1.
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

Theorem KRSimplifySound_list_ModuleElt: forall e,
    KRExprDenote_list_ModuleElt e = KRExprDenote_list_ModuleElt (KRSimplify_list_ModuleElt e).
Proof.
  KRSimplifySound_setup KRExpr_list_ModuleElt_mut H H0 H1.
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

