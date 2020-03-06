Require Import Kami.Notations.
Require Import Kami.Syntax.
Require Import List.
Require Import Kami.Notations_rewrites.
Require Import Program.Equality.
Require Import Kami.Rewrites.ReflectionPre.

Theorem KRSimplifyTopSound_RegInitT: forall e,
    KRExprDenote_RegInitT (KRSimplifyTop_RegInitT e)=KRExprDenote_RegInitT e.
Proof.
  solve_KRSimplifyTopSound.
Qed.

Hint Rewrite KRSimplifyTopSound_RegInitT : KRSimplify.

Theorem KRSimplifyTopSound_Rule: forall e,
     KRExprDenote_Rule (KRSimplifyTop_Rule e)=KRExprDenote_Rule e.
Proof.
  solve_KRSimplifyTopSound.
Qed.

Hint Rewrite KRSimplifyTopSound_Rule : KRSimplify.

Theorem KRSimplifyTopSound_DefMethT: forall e,
    KRExprDenote_DefMethT (KRSimplifyTop_DefMethT e)=KRExprDenote_DefMethT e.
Proof.
  solve_KRSimplifyTopSound.
Qed.

Hint Rewrite KRSimplifyTopSound_DefMethT : KRSimplify.

Theorem KRSimplifyTopSound_ModuleElt: forall e,
    KRExprDenote_ModuleElt (KRSimplifyTop_ModuleElt e)=KRExprDenote_ModuleElt e.
Proof.
  solve_KRSimplifyTopSound.
Qed.

Hint Rewrite KRSimplifyTopSound_ModuleElt : KRSimplify.

Theorem KRSimplifyTopSound_list_RegInitT: forall e,
    KRExprDenote_list_RegInitT (KRSimplifyTop_list_RegInitT e)=KRExprDenote_list_RegInitT e.
Proof.
  solve_KRSimplifyTopSound;solve_KRSimplifyTopSound;
    repeat solve_contKRSimplifyTopSound.
Qed.

Hint Rewrite KRSimplifyTopSound_list_RegInitT : KRSimplify.

Theorem KRSimplifyTopSound_list_list_RegInitT: forall e,
   KRExprDenote_list_list_RegInitT (KRSimplifyTop_list_list_RegInitT e)=KRExprDenote_list_list_RegInitT e.
Proof.
  solve_KRSimplifyTopSound;solve_KRSimplifyTopSound;
    repeat solve_contKRSimplifyTopSound.
Qed.

Hint Rewrite KRSimplifyTopSound_list_list_RegInitT : KRSimplify.

Theorem KRSimplifyTopSound_list_Rule: forall e,
   KRExprDenote_list_Rule (KRSimplifyTop_list_Rule e)=KRExprDenote_list_Rule e.
Proof.
  solve_KRSimplifyTopSound;solve_KRSimplifyTopSound;
    repeat solve_contKRSimplifyTopSound.
Qed.

Hint Rewrite KRSimplifyTopSound_list_Rule : KRSimplify.

Theorem KRSimplifyTopSound_list_list_Rule: forall e,
   KRExprDenote_list_list_Rule (KRSimplifyTop_list_list_Rule e)=KRExprDenote_list_list_Rule e.
Proof.
  solve_KRSimplifyTopSound;solve_KRSimplifyTopSound;
    repeat solve_contKRSimplifyTopSound.
Qed.

Hint Rewrite KRSimplifyTopSound_list_list_Rule : KRSimplify.

Theorem KRSimplifyTopSound_list_DefMethT: forall e,
    KRExprDenote_list_DefMethT (KRSimplifyTop_list_DefMethT e)=KRExprDenote_list_DefMethT e.
Proof.
  solve_KRSimplifyTopSound;solve_KRSimplifyTopSound;
    repeat solve_contKRSimplifyTopSound.
Qed.

Hint Rewrite KRSimplifyTopSound_list_DefMethT : KRSimplify.

Theorem KRSimplifyTopSound_list_ModuleElt: forall e,
    KRExprDenote_list_ModuleElt (KRSimplifyTop_list_ModuleElt e)=KRExprDenote_list_ModuleElt e.
Proof.
  solve_KRSimplifyTopSound;
  solve_KRSimplifyTopSound;
  repeat solve_contKRSimplifyTopSound.
Qed.

Hint Rewrite KRSimplifyTopSound_list_ModuleElt : KRSimplify.

Theorem KRSimplifyTopSound_list_list_ModuleElt: forall e,
    KRExprDenote_list_list_ModuleElt (KRSimplifyTop_list_list_ModuleElt e)=KRExprDenote_list_list_ModuleElt e.
Proof.
  solve_KRSimplifyTopSound;
  solve_KRSimplifyTopSound;
  repeat solve_contKRSimplifyTopSound.
Qed.

Hint Rewrite KRSimplifyTopSound_list_list_ModuleElt : KRSimplify.

Theorem KRSimplifyTopSound_string: forall e,
    KRExprDenote_string (KRSimplifyTop_string e)=KRExprDenote_string e.
Proof.
  solve_KRSimplifyTopSound;solve_KRSimplifyTopSound;
    repeat solve_contKRSimplifyTopSound.
Qed.

Hint Rewrite KRSimplifyTopSound_string : KRSimplify.

Theorem KRSimplifyTopSound_list_string: forall e,
    KRExprDenote_list_string (KRSimplifyTop_list_string e)=KRExprDenote_list_string e.
Proof.
  solve_KRSimplifyTopSound;
  solve_KRSimplifyTopSound;
  repeat solve_contKRSimplifyTopSound.
Qed.

Hint Rewrite KRSimplifyTopSound_list_string : KRSimplify.

Theorem KRSimplifyTopSound_list_list_string: forall e,
    KRExprDenote_list_list_string (KRSimplifyTop_list_list_string e)=KRExprDenote_list_list_string e.
Proof.
  solve_KRSimplifyTopSound;
  solve_KRSimplifyTopSound;
  repeat solve_contKRSimplifyTopSound.
Qed.

Hint Rewrite KRSimplifyTopSound_list_list_string : KRSimplify.

Theorem KRSimplifyTopSound_BaseModule: forall e,
    KRExprDenote_BaseModule (KRSimplifyTop_BaseModule e)=KRExprDenote_BaseModule e.
Proof.
  solve_KRSimplifyTopSound;
  solve_KRSimplifyTopSound;
  repeat solve_contKRSimplifyTopSound.
Qed.

Hint Rewrite KRSimplifyTopSound_BaseModule : KRSimplify.

Theorem KRSimplifyTopSound_Mod: forall e,
     KRExprDenote_Mod (KRSimplifyTop_Mod e)=KRExprDenote_Mod e.
Proof.
  solve_KRSimplifyTopSound;
  solve_KRSimplifyTopSound;
  repeat solve_contKRSimplifyTopSound.
Qed.

Hint Rewrite KRSimplifyTopSound_Mod : KRSimplify.

Theorem KRSimplifyTopSound_list_Mod: forall e,
     KRExprDenote_list_Mod (KRSimplifyTop_list_Mod e)=KRExprDenote_list_Mod e.
Proof.
  solve_KRSimplifyTopSound;
  solve_KRSimplifyTopSound;
  repeat solve_contKRSimplifyTopSound.
Qed.

Hint Rewrite KRSimplifyTopSound_list_Mod : KRSimplify.

Theorem KRSimplifyTopSound_RegFileBase: forall e,
     KRExprDenote_RegFileBase (KRSimplifyTop_RegFileBase e)=KRExprDenote_RegFileBase e.
Proof.
  solve_KRSimplifyTopSound;
  solve_KRSimplifyTopSound;
  repeat solve_contKRSimplifyTopSound.
Qed.

Hint Rewrite KRSimplifyTopSound_RegFileBase : KRSimplify.

Theorem KRSimplifyTopSound_list_RegFileBase: forall e,
     KRExprDenote_list_RegFileBase (KRSimplifyTop_list_RegFileBase e)=KRExprDenote_list_RegFileBase e.
Proof.
  solve_KRSimplifyTopSound;
  solve_KRSimplifyTopSound;
  repeat solve_contKRSimplifyTopSound.
Qed.

Hint Rewrite KRSimplifyTopSound_list_RegFileBase : KRSimplify.

Theorem KRSimplifyTopSound_Prop: forall e,
    KRExprDenote_Prop (KRSimplifyTop_Prop e)=KRExprDenote_Prop e.
Proof.
  solve_KRSimplifyTopSound;
  solve_KRSimplifyTopSound;
  repeat solve_contKRSimplifyTopSound.
  - replace (KRExprDenote_string k=KRExprDenote_string k0) with (KRExprDenote_string k0=KRExprDenote_string k). reflexivity.
    apply my_eq_refl.
  - remember (sdisjPrefix (srev s) (srev s0)).
    destruct b.
    + simpl.
      apply sdisjPrefix_false.
      rewrite Heqb.
      reflexivity.
    + reflexivity.
  - replace (KRExprDenote_RegInitT k=KRExprDenote_RegInitT k0) with (KRExprDenote_RegInitT k0=KRExprDenote_RegInitT k). reflexivity.
    apply my_eq_refl.
  - replace (KRExprDenote_Rule k=KRExprDenote_Rule k0) with (KRExprDenote_Rule k0=KRExprDenote_Rule k). reflexivity.
    apply my_eq_refl.
  - replace (KRExprDenote_DefMethT k=KRExprDenote_DefMethT k0) with (KRExprDenote_DefMethT k0=KRExprDenote_DefMethT k). reflexivity.
    apply my_eq_refl.
Qed.

Hint Rewrite KRSimplifyTopSound_Prop : KRSimplify.

