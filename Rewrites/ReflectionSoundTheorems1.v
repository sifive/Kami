Require Import Kami.Notations.
Require Import Kami.Syntax.
Require Import List.
Require Import Kami.Rewrites.Notations_rewrites.
Require Import Program.Equality.
Require Import Kami.Rewrites.ReflectionPre.
Require Import Kami.Rewrites.ReflectionSoundTopTheorems.

(************************************************************************************************************)

Scheme KRExpr_RegInitT_mut := Induction for KRExpr_RegInitT Sort Prop
  with KRExpr_Rule_mut := Induction for KRExpr_Rule Sort Prop
  with KRExpr_DefMethT_mut := Induction for KRExpr_DefMethT Sort Prop
  with KRExpr_string_mut := Induction for KRExpr_string Sort Prop.

Ltac KRSimplifySound_setup1 mut H H0 H1 :=
  intros;
  eapply (mut
            (fun e : KRExpr_RegInitT => KRExprDenote_RegInitT (KRSimplify_RegInitT e) = KRExprDenote_RegInitT e)
            (fun e : KRExpr_Rule => KRExprDenote_Rule (KRSimplify_Rule e) = KRExprDenote_Rule e)
            (fun e : KRExpr_DefMethT => KRExprDenote_DefMethT (KRSimplify_DefMethT e) = KRExprDenote_DefMethT e)
            (fun e : KRExpr_string => KRExprDenote_string (KRSimplify_string e) = KRExprDenote_string e)
         );
  try (intros);try(autorewrite with KRSimplify); try(autorewrite with KRSimplifyTopSound); try(simpl); try (rewrite H); try  (rewrite H0); try (rewrite H1); try(reflexivity);intros.

(************************************************************************************************************)

Theorem KRSimplifySound_RegInitT: forall e,
    KRExprDenote_RegInitT (KRSimplify_RegInitT e) = KRExprDenote_RegInitT e.
Proof.
  KRSimplifySound_setup1 KRExpr_RegInitT_mut H H0 H1; repeat KRSimplifySound_unit; repeat KRSimplifySound_crunch; try (rewrite H); try (rewrite H0); try(reflexivity).
  - rewrite <- H. reflexivity.
  - rewrite <- H. reflexivity.
  - rewrite <- H. reflexivity.
Qed.

Hint Rewrite KRSimplifySound_RegInitT : KRSimplify.

Theorem KRSimplifySound_Rule: forall e,
    KRExprDenote_Rule (KRSimplify_Rule e) = KRExprDenote_Rule e.
Proof.
  KRSimplifySound_setup1 KRExpr_Rule_mut H H0 H1; repeat KRSimplifySound_unit; repeat KRSimplifySound_crunch; try (rewrite H); try (rewrite H0); try(reflexivity).
  - rewrite <- H. reflexivity.
  - rewrite <- H. reflexivity.
  - rewrite <- H. reflexivity.
Qed.

Hint Rewrite KRSimplifySound_Rule : KRSimplify.

Theorem KRSimplifySound_DefMethT: forall e,
    KRExprDenote_DefMethT (KRSimplify_DefMethT e) = KRExprDenote_DefMethT e.
Proof.
  KRSimplifySound_setup1 KRExpr_DefMethT_mut H H0 H1; repeat KRSimplifySound_unit; repeat KRSimplifySound_crunch; try (rewrite H); try (rewrite H0); try(reflexivity).
  - rewrite <- H. reflexivity.
  - rewrite <- H. reflexivity.
  - rewrite <- H. reflexivity.
Qed.

Hint Rewrite KRSimplifySound_DefMethT : KRSimplify.

Theorem KRSimplifySound_string: forall e,
    KRExprDenote_string (KRSimplify_string e) = KRExprDenote_string e.
Proof.
  KRSimplifySound_setup1 KRExpr_string_mut H H0 H1;
  repeat KRSimplifySound_unit;
  repeat KRSimplifySound_crunch; try (rewrite H0); try (rewrite H); try reflexivity.
  - rewrite <- H; reflexivity.
  - rewrite <- H; reflexivity.
  - rewrite <- H; reflexivity.
Qed.

Hint Rewrite KRSimplifySound_string : KRSimplify.

(************************************************************************************************************)

Theorem KRSimplifySound_ModuleElt: forall e,
    KRExprDenote_ModuleElt (KRSimplify_ModuleElt e) = KRExprDenote_ModuleElt e.
Proof.
  induction e.
  - reflexivity.
  - simpl.
    autorewrite with KRSimplify.
    reflexivity.
  - simpl.
    autorewrite with KRSimplify.
    reflexivity.
  - simpl.
    autorewrite with KRSimplify.
    reflexivity.
Qed.

Hint Rewrite KRSimplifySound_ModuleElt : KRSimplify.

(************************************************************************************************************)

Theorem KRSimplifySound_CallWithSign: forall e,
    KRExprDenote_CallWithSign (KRSimplify_CallWithSign e) = KRExprDenote_CallWithSign e.
Proof.
  intros.
  destruct e. reflexivity.
Qed.

Hint Rewrite KRSimplifySound_CallWithSign : KRSimplify.

(************************************************************************************************************)

Scheme KRExpr_list_CallWithSign_mut := Induction for KRExpr_list_CallWithSign Sort Prop
  with KRExpr_list_list_CallWithSign_mut := Induction for KRExpr_list_list_CallWithSign Sort Prop.

Ltac KRSimplifySound_setup2 mut H H0 H1 :=
  intros;
  eapply (mut
            (fun e : KRExpr_list_CallWithSign => KRExprDenote_list_CallWithSign (KRSimplify_list_CallWithSign e) = KRExprDenote_list_CallWithSign e)
            (fun e : KRExpr_list_list_CallWithSign => KRExprDenote_list_list_CallWithSign (KRSimplify_list_list_CallWithSign e) = KRExprDenote_list_list_CallWithSign e)
         );
  try (intros);try(autorewrite with KRSimplify); try(autorewrite with KRSimplifyTopSound); try(simpl); try (rewrite H); try  (rewrite H0); try (rewrite H1); try(reflexivity);intros.

(************************************************************************************************************)

Theorem KRSimplifySound_list_CallWithSign: forall e,
    KRExprDenote_list_CallWithSign (KRSimplify_list_CallWithSign e) = KRExprDenote_list_CallWithSign e.
Proof.
  KRSimplifySound_setup2 KRExpr_list_CallWithSign_mut H H0 H1; repeat KRSimplifySound_unit; repeat KRSimplifySound_crunch; try (autorewrite with KRSimplify); try (rewrite H); try (rewrite H0); try (rewrite H1);try (reflexivity).
  - rewrite <- H0.
    repeat KRSimplifySound_unit.
  - rewrite <- H.
    repeat KRSimplifySound_unit.
  - rewrite app_comm_cons.
    rewrite H.
    reflexivity.
  - rewrite <- H0.
    rewrite app_nil_r.
    reflexivity.
  - rewrite <- H0.
    rewrite app_nil_r.
    reflexivity.
  - rewrite <- H0.
    rewrite app_nil_r.
    reflexivity.
  - rewrite <- H.
    rewrite app_nil_l.
    reflexivity.
  - rewrite app_comm_cons.
    rewrite H.
    reflexivity.
  - rewrite <- H0.
    rewrite app_nil_r.
    reflexivity.
Qed.

Hint Rewrite KRSimplifySound_list_CallWithSign : KRSimplify.

Theorem KRSimplifySound_list_list_CallWithSign: forall e,
    KRExprDenote_list_list_CallWithSign (KRSimplify_list_list_CallWithSign e) = KRExprDenote_list_list_CallWithSign e.
Proof.
  KRSimplifySound_setup2 KRExpr_list_list_CallWithSign_mut H H0 H1; repeat KRSimplifySound_unit; repeat KRSimplifySound_crunch; try (autorewrite with KRSimplify); try (rewrite H); try (rewrite H0); try (rewrite H1);try (reflexivity).
  - rewrite <- H0.
    repeat KRSimplifySound_unit.
  - rewrite <- H.
    repeat KRSimplifySound_unit.
  - rewrite app_comm_cons.
    rewrite H.
    reflexivity.
  - rewrite <- H0.
    rewrite app_nil_r.
    reflexivity.
Qed.

Hint Rewrite KRSimplifySound_list_list_CallWithSign : KRSimplify.

(************************************************************************************************************)

Theorem KRSimplifySound_list_RegFileBase: forall e,
    KRExprDenote_list_RegFileBase (KRSimplify_list_RegFileBase e) = KRExprDenote_list_RegFileBase e.
Proof.
  induction e; try (reflexivity).
  - simpl.
    autorewrite with KRSimplify.
    rewrite IHe.
    reflexivity.
  - repeat KRSimplifySound_unit; repeat KRSimplifySound_crunch.
    + rewrite <- IHe2.
      rewrite app_nil_r.
      reflexivity.
    + rewrite IHe2.
      reflexivity.
    + rewrite IHe2.
      reflexivity.
    + rewrite <- IHe1.
      rewrite app_nil_l.
      apply IHe2.
    + rewrite app_comm_cons.
      rewrite IHe1.
      rewrite IHe2.
      reflexivity.
    + rewrite IHe1.
      reflexivity.
    + rewrite <- IHe2.
      rewrite IHe1.
      rewrite app_nil_r.
      reflexivity.
    + rewrite IHe1.
      rewrite IHe2.
      reflexivity.
    + rewrite IHe2.
      rewrite IHe1.
      reflexivity.
Qed.

Hint Rewrite KRSimplifySound_list_RegFileBase : KRSimplify.

(************************************************************************************************************)

Scheme KRExpr_list_RegInitT_mut := Induction for KRExpr_list_RegInitT Sort Prop
  with KRExpr_list_list_RegInitT_mut := Induction for KRExpr_list_list_RegInitT Sort Prop
  with KRExpr_BaseModule_mut := Induction for KRExpr_BaseModule Sort Prop
  with KRExpr_Mod_mut := Induction for KRExpr_Mod Sort Prop
  with KRExpr_list_ModuleElt_mut := Induction for KRExpr_list_ModuleElt Sort Prop
  with KRExpr_list_list_ModuleElt_mut := Induction for KRExpr_list_list_ModuleElt Sort Prop
  with KRExpr_list_Mod_mut := Induction for KRExpr_list_Mod Sort Prop
  with KRExpr_list_DefMethT_mut := Induction for KRExpr_list_DefMethT Sort Prop
  with KRExpr_list_list_DefMethT_mut := Induction for KRExpr_list_list_DefMethT Sort Prop
  with KRExpr_list_Rule_mut := Induction for KRExpr_list_Rule Sort Prop
  with KRExpr_list_list_Rule_mut := Induction for KRExpr_list_list_Rule Sort Prop.

Ltac KRSimplifySound_setup3 mut H H0 H1 :=
  intros;
  eapply (mut
            (fun e : KRExpr_list_RegInitT => KRExprDenote_list_RegInitT (KRSimplify_list_RegInitT e) = KRExprDenote_list_RegInitT e)
            (fun e : KRExpr_list_list_RegInitT => KRExprDenote_list_list_RegInitT (KRSimplify_list_list_RegInitT e) = KRExprDenote_list_list_RegInitT e)
            (fun e : KRExpr_BaseModule => KRExprDenote_BaseModule (KRSimplify_BaseModule e) = KRExprDenote_BaseModule e)
            (fun e : KRExpr_Mod => KRExprDenote_Mod (KRSimplify_Mod e) = KRExprDenote_Mod e)
            (fun e : KRExpr_list_ModuleElt => KRExprDenote_list_ModuleElt (KRSimplify_list_ModuleElt e) = KRExprDenote_list_ModuleElt e)
            (fun e : KRExpr_list_list_ModuleElt => KRExprDenote_list_list_ModuleElt (KRSimplify_list_list_ModuleElt e) = KRExprDenote_list_list_ModuleElt e)
            (fun e : KRExpr_list_Mod => KRExprDenote_list_Mod (KRSimplify_list_Mod e) = KRExprDenote_list_Mod e)
            (fun e : KRExpr_list_DefMethT => KRExprDenote_list_DefMethT (KRSimplify_list_DefMethT e) = KRExprDenote_list_DefMethT e)
            (fun e : KRExpr_list_list_DefMethT => KRExprDenote_list_list_DefMethT (KRSimplify_list_list_DefMethT e) = KRExprDenote_list_list_DefMethT e)
            (fun e : KRExpr_list_Rule => KRExprDenote_list_Rule (KRSimplify_list_Rule e) = KRExprDenote_list_Rule e)
            (fun e : KRExpr_list_list_Rule => KRExprDenote_list_list_Rule (KRSimplify_list_list_Rule e) = KRExprDenote_list_list_Rule e)
         );
  try (intros);try(autorewrite with KRSimplify); try(autorewrite with KRSimplifyTopSound); try(simpl); try (rewrite H); try  (rewrite H0); try (rewrite H1); try(reflexivity);intros.

(************************************************************************************************************)

Theorem KRSimplifySound_list_RegInitT: forall e,
    KRExprDenote_list_RegInitT (KRSimplify_list_RegInitT e) = KRExprDenote_list_RegInitT e.
Proof.
  KRSimplifySound_setup3 KRExpr_list_RegInitT_mut H H0 H1; repeat KRSimplifySound_unit.
  - repeat KRSimplifySound_unit; repeat KRSimplifySound_crunch; try (rewrite <- H); try (simpl); try (autorewrite with kami_rewrite_db); try (reflexivity).
  - repeat KRSimplifySound_unit; repeat KRSimplifySound_crunch; try (rewrite <- H0); try (rewrite <- H); try (autorewrite with kami_rewrite_db); try (reflexivity).
  - repeat KRSimplifySound_crunch; try (rewrite <- H); repeat KRSimplifySound_unit.
  - repeat KRSimplifySound_crunch; try (rewrite <- H); try (rewrite <- H0); repeat KRSimplifySound_unit.
  - repeat KRSimplifySound_crunch; try (rewrite <- H); try (rewrite <- H0); repeat KRSimplifySound_unit.
  - repeat KRSimplifySound_crunch; try (rewrite <- H); try (rewrite <- H0); repeat KRSimplifySound_unit.
  - repeat KRSimplifySound_crunch; try (rewrite <- H); try (rewrite <- H0); repeat KRSimplifySound_unit.
  - repeat KRSimplifySound_crunch; try (rewrite <- H); try (rewrite <- H0); repeat KRSimplifySound_unit.
Qed.

Hint Rewrite KRSimplifySound_list_RegInitT : KRSimplify.

Theorem KRSimplifySound_list_list_RegInitT: forall e,
   KRExprDenote_list_list_RegInitT (KRSimplify_list_list_RegInitT e) = KRExprDenote_list_list_RegInitT e.
Proof.
  KRSimplifySound_setup3 KRExpr_list_list_RegInitT_mut H H0 H1. repeat KRSimplifySound_unit.
  - repeat KRSimplifySound_crunch; try (rewrite <- H); try (rewrite <- H0); repeat KRSimplifySound_unit.
  - repeat KRSimplifySound_crunch; try (rewrite <- H); try (rewrite <- H0); repeat KRSimplifySound_unit.
    + autorewrite with KRSimplify in HeqH.
      inversion HeqH; subst; clear HeqH.
      reflexivity.
    + autorewrite with KRSimplify in HeqH.
      inversion HeqH; subst; clear HeqH.
    + autorewrite with KRSimplify in HeqH.
      inversion HeqH; subst; clear HeqH.
  - repeat KRSimplifySound_crunch; try (rewrite <- H); try (rewrite <- H0); repeat KRSimplifySound_unit.
  - repeat KRSimplifySound_crunch; try (rewrite <- H); try (rewrite <- H0); repeat KRSimplifySound_unit.
  - repeat KRSimplifySound_crunch; try (rewrite <- H); try (rewrite <- H0); repeat KRSimplifySound_unit.
  - repeat KRSimplifySound_crunch; try (rewrite <- H); try (rewrite <- H0); repeat KRSimplifySound_unit.
  - repeat KRSimplifySound_crunch; try (rewrite <- H); try (rewrite <- H0); repeat KRSimplifySound_unit.
  - repeat KRSimplifySound_crunch; try (rewrite <- H); try (rewrite <- H0); repeat KRSimplifySound_unit.
  - repeat KRSimplifySound_crunch; try (rewrite <- H); try (rewrite <- H0); repeat KRSimplifySound_unit.
    + autorewrite with KRSimplify in HeqH.
      inversion HeqH; subst; clear HeqH.
      reflexivity.
    + autorewrite with KRSimplify in HeqH.
      inversion HeqH; subst; clear HeqH.
    + autorewrite with KRSimplify in HeqH.
      inversion HeqH; subst; clear HeqH.
  - repeat KRSimplifySound_crunch; try (rewrite <- H); try (rewrite <- H0); repeat KRSimplifySound_unit.
  - repeat KRSimplifySound_crunch; try (rewrite <- H); try (rewrite <- H0); repeat KRSimplifySound_unit.
  - repeat KRSimplifySound_crunch; try (rewrite <- H); try (rewrite <- H0); repeat KRSimplifySound_unit.
Qed.

Hint Rewrite KRSimplifySound_list_list_RegInitT : KRSimplify.

Theorem KRSimplifySound_list_Rule: forall e,
  KRExprDenote_list_Rule (KRSimplify_list_Rule e) = KRExprDenote_list_Rule e.
Proof.
  KRSimplifySound_setup3 KRExpr_list_Rule_mut H H0 H1; repeat KRSimplifySound_unit.
  - repeat KRSimplifySound_unit; repeat KRSimplifySound_crunch; try (rewrite <- H); try (simpl); try (autorewrite with kami_rewrite_db); try (reflexivity).
  - repeat KRSimplifySound_unit; repeat KRSimplifySound_crunch; try (rewrite <- H0); try (rewrite <- H); try (autorewrite with kami_rewrite_db); try (reflexivity).
  - repeat KRSimplifySound_crunch; try (rewrite <- H); repeat KRSimplifySound_unit.
  - repeat KRSimplifySound_crunch; try (rewrite <- H); try (rewrite <- H0); repeat KRSimplifySound_unit.
  - repeat KRSimplifySound_crunch; try (rewrite <- H); try (rewrite <- H0); repeat KRSimplifySound_unit.
  - repeat KRSimplifySound_crunch; try (rewrite <- H); try (rewrite <- H0); repeat KRSimplifySound_unit.
Qed.

Hint Rewrite KRSimplifySound_list_Rule : KRSimplify.

Theorem KRSimplifySound_list_list_Rule: forall e,
   KRExprDenote_list_list_Rule (KRSimplify_list_list_Rule e) = KRExprDenote_list_list_Rule e.
Proof.
  KRSimplifySound_setup3 KRExpr_list_list_Rule_mut H H0 H1. repeat KRSimplifySound_unit.
  - repeat KRSimplifySound_crunch; try (rewrite <- H); try (rewrite <- H0); repeat KRSimplifySound_unit.
  - repeat KRSimplifySound_crunch; try (rewrite <- H); try (rewrite <- H0); repeat KRSimplifySound_unit.
  - repeat KRSimplifySound_crunch; try (rewrite <- H); try (rewrite <- H0); repeat KRSimplifySound_unit.
  - repeat KRSimplifySound_crunch; try (rewrite <- H); try (rewrite <- H0); repeat KRSimplifySound_unit.
  - repeat KRSimplifySound_crunch; try (rewrite <- H); try (rewrite <- H0); repeat KRSimplifySound_unit.
  - repeat KRSimplifySound_crunch; try (rewrite <- H); try (rewrite <- H0); repeat KRSimplifySound_unit.
    + autorewrite with KRSimplify in HeqH.
      inversion HeqH; subst; clear HeqH.
      reflexivity.
    + autorewrite with KRSimplify in HeqH.
      inversion HeqH; subst; clear HeqH.
    + autorewrite with KRSimplify in HeqH.
      inversion HeqH; subst; clear HeqH.    
  - repeat KRSimplifySound_crunch; try (rewrite <- H); try (rewrite <- H0); repeat KRSimplifySound_unit.
Qed.

Hint Rewrite KRSimplifySound_list_list_Rule : KRSimplify.

Theorem KRSimplifySound_list_list_DefMethT: forall e,
    KRExprDenote_list_list_DefMethT (KRSimplify_list_list_DefMethT e) = KRExprDenote_list_list_DefMethT e.
Proof.
  KRSimplifySound_setup3 KRExpr_list_list_DefMethT_mut H H0 H1.
  - repeat KRSimplifySound_crunch; try (rewrite <- H); try (rewrite <- H0); repeat KRSimplifySound_unit.
  - repeat KRSimplifySound_crunch; try (rewrite <- H); try (rewrite <- H0); repeat KRSimplifySound_unit.
  - repeat KRSimplifySound_crunch; try (rewrite <- H); try (rewrite <- H0); repeat KRSimplifySound_unit.
  - repeat KRSimplifySound_crunch; try (rewrite <- H); try (rewrite <- H0); repeat KRSimplifySound_unit.
  - repeat KRSimplifySound_crunch; try (rewrite <- H); try (rewrite <- H0); repeat KRSimplifySound_unit.
  - repeat KRSimplifySound_crunch; try (rewrite <- H); try (rewrite <- H0); repeat KRSimplifySound_unit.
  - repeat KRSimplifySound_crunch; try (rewrite <- H); try (rewrite <- H0); repeat KRSimplifySound_unit.
    + autorewrite with KRSimplify in HeqH.
      inversion HeqH; subst; clear HeqH.
      reflexivity.
    + autorewrite with KRSimplify in HeqH.
      inversion HeqH; subst; clear HeqH.
    + autorewrite with KRSimplify in HeqH.
      inversion HeqH; subst; clear HeqH.    
Qed.

Hint Rewrite KRSimplifySound_list_list_DefMethT : KRSimplify.

Theorem KRSimplifySound_list_DefMethT: forall e,
  KRExprDenote_list_DefMethT (KRSimplify_list_DefMethT e) = KRExprDenote_list_DefMethT e.
Proof.
  KRSimplifySound_setup3 KRExpr_list_DefMethT_mut H H0 H1; repeat KRSimplifySound_unit.
  - repeat KRSimplifySound_unit; repeat KRSimplifySound_crunch; try (rewrite <- H); try (simpl); try (autorewrite with kami_rewrite_db); try (reflexivity).
  - repeat KRSimplifySound_unit; repeat KRSimplifySound_crunch; try (rewrite <- H0); try (rewrite <- H); try (autorewrite with kami_rewrite_db); try (reflexivity).
  - repeat KRSimplifySound_unit; repeat KRSimplifySound_crunch; try (rewrite <- H0); try (rewrite <- H); try (autorewrite with kami_rewrite_db); try (reflexivity).
Qed.

Hint Rewrite KRSimplifySound_list_DefMethT : KRSimplify.

Theorem KRSimplifySound_list_ModuleElt: forall e,
   KRExprDenote_list_ModuleElt (KRSimplify_list_ModuleElt e) = KRExprDenote_list_ModuleElt e.
Proof.
  KRSimplifySound_setup3 KRExpr_list_ModuleElt_mut H H0 H1; repeat KRSimplifySound_unit.
  - repeat KRSimplifySound_unit; repeat KRSimplifySound_crunch; try (rewrite <- H); try (simpl); try (autorewrite with kami_rewrite_db); try (reflexivity).
  - repeat KRSimplifySound_unit; repeat KRSimplifySound_crunch; try (rewrite <- H0); try (rewrite <- H); try (autorewrite with kami_rewrite_db); try (reflexivity).
Qed.

Hint Rewrite KRSimplifySound_list_ModuleElt : KRSimplify.

Theorem KRSimplifySound_list_list_ModuleElt: forall e,
    KRExprDenote_list_list_ModuleElt (KRSimplify_list_list_ModuleElt e) = KRExprDenote_list_list_ModuleElt e.
Proof.
  KRSimplifySound_setup3 KRExpr_list_list_ModuleElt_mut H H0 H1.
  - repeat KRSimplifySound_crunch; try (rewrite <- H); try (rewrite <- H0); repeat KRSimplifySound_unit.
Qed.

Hint Rewrite KRSimplifySound_list_list_ModuleElt : KRSimplify.

Theorem KRSimplifySound_BaseModule: forall e,
  KRExprDenote_BaseModule (KRSimplify_BaseModule e) = KRExprDenote_BaseModule e.
Proof.
  KRSimplifySound_setup3 KRExpr_BaseModule_mut H H0 H1; repeat KRSimplifySound_unit.
  repeat KRSimplifySound_crunch; try (rewrite <- H0); try (rewrite <- H); try (autorewrite with kami_rewrite_db); try (reflexivity).
Qed.

Hint Rewrite KRSimplifySound_BaseModule : KRSimplify.

Theorem KRSimplifySound_Mod: forall e,
    KRExprDenote_Mod (KRSimplify_Mod e) = KRExprDenote_Mod e.
Proof.
  KRSimplifySound_setup3 KRExpr_Mod_mut H H0 H1;
  repeat KRSimplifySound_unit;
  repeat KRSimplifySound_crunch; try (rewrite <- H0); try (rewrite <- H); try (autorewrite with kami_rewrite_db); try (reflexivity).
Qed.

Hint Rewrite KRSimplifySound_Mod : KRSimplify.

Theorem KRSimplifySound_list_Mod: forall e,
    KRExprDenote_list_Mod (KRSimplify_list_Mod e) = KRExprDenote_list_Mod e.
Proof.
  KRSimplifySound_setup3 KRExpr_list_Mod_mut H H0 H1;
  repeat KRSimplifySound_unit.
  repeat KRSimplifySound_crunch; try (rewrite <- H0); try (rewrite <- H); try (autorewrite with kami_rewrite_db); try (reflexivity).
Qed.

Hint Rewrite KRSimplifySound_list_Mod : KRSimplify.

Theorem KRSimplifySound_RegFileBase: forall e,
     KRExprDenote_RegFileBase (KRSimplify_RegFileBase e) = KRExprDenote_RegFileBase e.
Proof.
  intros.
  destruct e. reflexivity.
Qed.

Hint Rewrite KRSimplifySound_RegFileBase : KRSimplify.
