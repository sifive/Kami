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
  with KRExpr_list_list_string_mut := Induction for KRExpr_list_list_string Sort Prop.

Ltac KRSimplifySound_setup3 mut H H0 H1 :=
  intros;
  eapply (mut
            (fun e : KRExpr_list_string => KRExprDenote_list_string (KRSimplify_list_string e) = KRExprDenote_list_string e)
            (fun e : KRExpr_list_list_string => KRExprDenote_list_list_string (KRSimplify_list_list_string e) = KRExprDenote_list_list_string e)
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

Theorem KRSimplifySound_list_string: forall e,
    KRExprDenote_list_string (KRSimplify_list_string e) = KRExprDenote_list_string e.
Proof.
   eapply (KRExpr_list_string_mut
            (fun e : KRExpr_list_string => KRExprDenote_list_string (KRSimplify_list_string e) = KRExprDenote_list_string e)
            (fun e : KRExpr_list_list_string => KRExprDenote_list_list_string (KRSimplify_list_list_string e) = KRExprDenote_list_list_string e)
          ); try (intros; autorewrite with KRSimplify;simpl;try(f_equal);autorewrite with KRSimplify;try (apply H);try (apply H0);reflexivity).
Qed.

Hint Rewrite KRSimplifySound_list_string : KRSimplify.

Theorem KRSimplifySound_list_list_string: forall e,
   KRExprDenote_list_list_string (KRSimplify_list_list_string e) = KRExprDenote_list_list_string e.
Proof.
   eapply (KRExpr_list_list_string_mut
            (fun e : KRExpr_list_string => KRExprDenote_list_string (KRSimplify_list_string e) = KRExprDenote_list_string e)
            (fun e : KRExpr_list_list_string => KRExprDenote_list_list_string (KRSimplify_list_list_string e) = KRExprDenote_list_list_string e)
          ); try (intros; autorewrite with KRSimplify;simpl;try(f_equal);autorewrite with KRSimplify;try (apply H);try (apply H0);reflexivity).
Qed.

Hint Rewrite KRSimplifySound_list_list_string : KRSimplify.

