Require Import Kami.Notations.
Require Import Kami.Syntax.
Require Import List.
Require Import Kami.Rewrites.Notations_rewrites.
Require Import Program.Equality.
Require Import Kami.Rewrites.ReflectionPre.
Require Import Kami.Rewrites.ReflectionSoundTopTheorems.
Require Import Kami.Rewrites.ReflectionSoundTheorems1.

(************************************************************************************************************)

Scheme KRExpr_list_string_mut := Induction for KRExpr_list_string Sort Prop
  with KRExpr_list_list_string_mut := Induction for KRExpr_list_list_string Sort Prop
  with KRExpr_Prop_mut := Induction for KRExpr_Prop Sort Prop.

Ltac KRSimplifySound_setup3 mut H H0 H1 :=
  intros;
  eapply (mut
            (fun e : KRExpr_list_string => KRExprDenote_list_string (KRSimplify_list_string e) = KRExprDenote_list_string e)
            (fun e : KRExpr_list_list_string => KRExprDenote_list_list_string (KRSimplify_list_list_string e) = KRExprDenote_list_list_string e)
            (fun e : KRExpr_Prop => KRExprDenote_Prop (KRSimplify_Prop e) = KRExprDenote_Prop e)
         );
  try (try (intros);try(autorewrite with KRSimplify); try(autorewrite with KRSimplifyTopSound); try(simpl); try (rewrite H); try  (rewrite H0); try (rewrite H1); reflexivity).

(************************************************************************************************************)

Theorem KRSimplify_list_string_KRApp_list_string:
  forall f r, KRSimplify_list_string (KRApp_list_string f r)=
              KRSimplifyTop_list_string (KRApp_list_string (KRSimplify_list_string f)
                                                           (KRSimplify_list_string r)).
Proof.
  reflexivity.
Qed.

Hint Rewrite KRSimplify_list_string_KRApp_list_string : KRSimplify.

Theorem KRSimplify_list_string_KRgetCallsPerMod:
  forall m, KRSimplify_list_string(KRgetCallsPerMod m)=
            KRSimplifyTop_list_string(KRgetCallsPerMod (KRSimplify_Mod m)).
Proof.
  reflexivity.
Qed.

Hint Rewrite KRSimplify_list_string_KRgetCallsPerMod : KRSimplify.

Theorem KRSimplify_list_string_KRmap_RegInitT_string:
  forall f l, KRSimplify_list_string (KRmap_RegInitT_string f l)=
              KRSimplifyTop_list_string (KRmap_RegInitT_string (KRSimplify_RegInitT_string_Func f) (KRSimplify_list_RegInitT l)).
Proof.
  reflexivity.
Qed.

Hint Rewrite KRSimplify_list_string_KRmap_RegInitT_string : KRSimplify.

Theorem KRSimplify_list_string_KRmap_Rule_string:
  forall f l, KRSimplify_list_string (KRmap_Rule_string f l)=
              KRSimplifyTop_list_string (KRmap_Rule_string (KRSimplify_Rule_string_Func f) (KRSimplify_list_Rule l)).
Proof.
  reflexivity.
Qed.

Hint Rewrite KRSimplify_list_string_KRmap_Rule_string : KRSimplify.

Theorem KRSimplify_list_string_KRmap_DefMethT_string:
  forall f l, KRSimplify_list_string (KRmap_DefMethT_string f l)=
              KRSimplifyTop_list_string (KRmap_DefMethT_string (KRSimplify_DefMethT_string_Func f) (KRSimplify_list_DefMethT l)).
Proof.
  reflexivity.
Qed.

Hint Rewrite KRSimplify_list_string_KRmap_DefMethT_string : KRSimplify.

Theorem KRSimplify_list_list_string_KRCons_list_list_string:
  forall f r, KRSimplify_list_list_string (KRCons_list_list_string f r)=
              KRSimplifyTop_list_list_string (KRCons_list_list_string (KRSimplify_list_string f) (KRSimplify_list_list_string r)).
Proof.
  reflexivity.
Qed.

Hint Rewrite KRSimplify_list_list_string_KRCons_list_list_string : KRSimplify.

Theorem KRSimplify_list_list_string_KRApp_list_list_string:
  forall f r, KRSimplify_list_list_string (KRApp_list_list_string f r)=
              KRSimplifyTop_list_list_string (KRApp_list_list_string (KRSimplify_list_list_string f) (KRSimplify_list_list_string r)).
Proof.
  reflexivity.
Qed.

Hint Rewrite KRSimplify_list_list_string_KRApp_list_list_string : KRSimplify.

Theorem KRSimplify_Prop_KRAnd_Prop: forall a b,
     KRSimplify_Prop (KRAnd_Prop a b)= KRSimplifyTop_Prop (KRAnd_Prop (KRSimplify_Prop a) (KRSimplify_Prop b)).
Proof.
  reflexivity.
Qed.

Hint Rewrite KRSimplify_Prop_KRAnd_Prop : KRSimplify.

Theorem KRSimplify_Prop_KROr_Prop: forall a b,
     KRSimplify_Prop (KROr_Prop a b)= KRSimplifyTop_Prop (KROr_Prop (KRSimplify_Prop a) (KRSimplify_Prop b)).
Proof.
  reflexivity.
Qed.

Hint Rewrite KRSimplify_Prop_KROr_Prop : KRSimplify.

Theorem KRSimplify_Prop_KRNot_Prop: forall a,
     KRSimplify_Prop (KRNot_Prop a)= KRSimplifyTop_Prop (KRNot_Prop (KRSimplify_Prop a)).
Proof.
  reflexivity.
Qed.

Hint Rewrite KRSimplify_Prop_KRNot_Prop : KRSimplify.

Theorem KRSimplify_Prop_KRIn_string_Prop: forall a b,
     KRSimplify_Prop (KRIn_string_Prop a b)= KRSimplifyTop_Prop (KRIn_string_Prop (KRSimplify_string a) (KRSimplify_list_string b)).
Proof.
  reflexivity.
Qed.

Hint Rewrite KRSimplify_Prop_KRIn_string_Prop : KRSimplify.

Theorem KRSimplify_Prop_KRIn_RegInitT_Prop: forall a b,
     KRSimplify_Prop (KRIn_RegInitT_Prop a b)= KRSimplifyTop_Prop (KRIn_RegInitT_Prop (KRSimplify_RegInitT a) (KRSimplify_list_RegInitT b)).
Proof.
  reflexivity.
Qed.

Hint Rewrite KRSimplify_Prop_KRIn_RegInitT_Prop : KRSimplify.

Theorem KRSimplify_Prop_KRIn_DefMethT_Prop: forall a b,
     KRSimplify_Prop (KRIn_DefMethT_Prop a b)= KRSimplifyTop_Prop (KRIn_DefMethT_Prop (KRSimplify_DefMethT a) (KRSimplify_list_DefMethT b)).
Proof.
  reflexivity.
Qed.

Hint Rewrite KRSimplify_Prop_KRIn_DefMethT_Prop : KRSimplify.

Theorem KRSimplify_Prop_KRIn_Rule_Prop: forall a b,
     KRSimplify_Prop (KRIn_Rule_Prop a b)= KRSimplifyTop_Prop (KRIn_Rule_Prop (KRSimplify_Rule a) (KRSimplify_list_Rule b)).
Proof.
  reflexivity.
Qed.

Hint Rewrite KRSimplify_Prop_KRIn_Rule_Prop : KRSimplify.

Theorem KRSimplify_Prop_KRDisjKey_RegInitT_Prop: forall a b,
     KRSimplify_Prop (KRDisjKey_RegInitT a b)= KRSimplifyTop_Prop (KRDisjKey_RegInitT (KRSimplify_list_RegInitT a) (KRSimplify_list_RegInitT b)).
Proof.
  reflexivity.
Qed.

Hint Rewrite KRSimplify_Prop_KRDisjKey_RegInitT_Prop : KRSimplify.

Theorem KRSimplify_Prop_KRDisjKey_DefMethT_Prop: forall a b,
     KRSimplify_Prop (KRDisjKey_DefMethT a b)= KRSimplifyTop_Prop (KRDisjKey_DefMethT (KRSimplify_list_DefMethT a) (KRSimplify_list_DefMethT b)).
Proof.
  reflexivity.
Qed.

Hint Rewrite KRSimplify_Prop_KRDisjKey_DefMethT_Prop : KRSimplify.

Theorem KRSimplify_Prop_KRDisjKey_Rule_Prop: forall a b,
     KRSimplify_Prop (KRDisjKey_Rule a b)= KRSimplifyTop_Prop (KRDisjKey_Rule (KRSimplify_list_Rule a) (KRSimplify_list_Rule b)).
Proof.
  reflexivity.
Qed.

Hint Rewrite KRSimplify_Prop_KRDisjKey_Rule_Prop : KRSimplify.

Theorem KRSimplify_Prop_KREq_string_Prop: forall a b,
     KRSimplify_Prop (KREq_string_Prop a b)= KRSimplifyTop_Prop (KREq_string_Prop (KRSimplify_string a) (KRSimplify_string b)).
Proof.
  reflexivity.
Qed.

Hint Rewrite KRSimplify_Prop_KREq_string_Prop : KRSimplify.

Theorem KRSimplify_Prop_KREq_RegInitT_Prop: forall a b,
     KRSimplify_Prop (KREq_RegInitT_Prop a b)= KRSimplifyTop_Prop (KREq_RegInitT_Prop (KRSimplify_RegInitT a) (KRSimplify_RegInitT b)).
Proof.
  reflexivity.
Qed.

Hint Rewrite KRSimplify_Prop_KREq_RegInitT_Prop : KRSimplify.

Theorem KRSimplify_Prop_KREq_DefMethT_Prop: forall a b,
     KRSimplify_Prop (KREq_DefMethT_Prop a b)= KRSimplifyTop_Prop (KREq_DefMethT_Prop (KRSimplify_DefMethT a) (KRSimplify_DefMethT b)).
Proof.
  reflexivity.
Qed.

Hint Rewrite KRSimplify_Prop_KREq_DefMethT_Prop : KRSimplify.

Theorem KRSimplify_Prop_KREq_Rule_Prop: forall a b,
     KRSimplify_Prop (KREq_Rule_Prop a b)= KRSimplifyTop_Prop (KREq_Rule_Prop (KRSimplify_Rule a) (KRSimplify_Rule b)).
Proof.
  reflexivity.
Qed.

Hint Rewrite KRSimplify_Prop_KREq_Rule_Prop : KRSimplify.

Theorem KRSimplifySound_list_string: forall e,
    KRExprDenote_list_string (KRSimplify_list_string e) = KRExprDenote_list_string e.
Proof.
   eapply (KRExpr_list_string_mut
            (fun e : KRExpr_list_string => KRExprDenote_list_string (KRSimplify_list_string e) = KRExprDenote_list_string e)
            (fun e : KRExpr_list_list_string => KRExprDenote_list_list_string (KRSimplify_list_list_string e) = KRExprDenote_list_list_string e)
            (fun e : KRExpr_Prop => KRExprDenote_Prop (KRSimplify_Prop e) = KRExprDenote_Prop e)
          ); try (intros; autorewrite with KRSimplify;simpl;try(f_equal);autorewrite with KRSimplify;try (apply H);try (apply H0);reflexivity).
Qed.

Hint Rewrite KRSimplifySound_list_string : KRSimplify.

Theorem KRSimplifySound_list_list_string: forall e,
   KRExprDenote_list_list_string (KRSimplify_list_list_string e) = KRExprDenote_list_list_string e.
Proof.
   eapply (KRExpr_list_list_string_mut
            (fun e : KRExpr_list_string => KRExprDenote_list_string (KRSimplify_list_string e) = KRExprDenote_list_string e)
            (fun e : KRExpr_list_list_string => KRExprDenote_list_list_string (KRSimplify_list_list_string e) = KRExprDenote_list_list_string e)
            (fun e : KRExpr_Prop => KRExprDenote_Prop (KRSimplify_Prop e) = KRExprDenote_Prop e)
          ); try (intros; autorewrite with KRSimplify;simpl;try(f_equal);autorewrite with KRSimplify;try (apply H);try (apply H0);reflexivity).
Qed.

Hint Rewrite KRSimplifySound_list_list_string : KRSimplify.

Theorem KRSimplifySound_Prop: forall e,
    KRExprDenote_Prop (KRSimplify_Prop e) = KRExprDenote_Prop e.
Proof.
   eapply (KRExpr_Prop_mut
            (fun e : KRExpr_list_string => KRExprDenote_list_string (KRSimplify_list_string e) = KRExprDenote_list_string e)
            (fun e : KRExpr_list_list_string => KRExprDenote_list_list_string (KRSimplify_list_list_string e) = KRExprDenote_list_list_string e)
            (fun e : KRExpr_Prop => KRExprDenote_Prop (KRSimplify_Prop e) = KRExprDenote_Prop e)
          ); try (intros; autorewrite with KRSimplify;simpl;try(f_equal);autorewrite with KRSimplify;try (apply H);try (apply H0);reflexivity).
Qed.

Hint Rewrite KRSimplifySound_Prop : KRSimplify.

