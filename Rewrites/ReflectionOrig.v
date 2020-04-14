Require Import Kami.Notations.
Require Import Kami.Syntax.
Require Import List.
Require Import Kami.Rewrites.Notations_rewrites.
Require Import Program.Equality.
Require Import Kami.Rewrites.ReflectionPre.
Require Import Kami.Rewrites.ReflectionSoundTopTheorems.
Require Import Kami.Rewrites.ReflectionSoundTheorems1.
Require Import Kami.Rewrites.ReflectionSoundTheorems2.

Definition KRSimplifyTop_Prop (e: KRExpr_Prop) : KRExpr_Prop :=
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
  | KRNot_Prop (KRAnd_Prop a b) => (KROr_Prop (KRNot_Prop a) (KRNot_Prop b))
  | KRNot_Prop (KROr_Prop a b) => (KRAnd_Prop (KRNot_Prop a) (KRNot_Prop b))
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

Fixpoint KRSimplify_Prop(p:KRExpr_Prop) :=
       KRSimplifyTop_Prop (match p with
                           | KRAnd_Prop a b => KRAnd_Prop (KRSimplify_Prop a) (KRSimplify_Prop b)
                           | KROr_Prop a b => KROr_Prop (KRSimplify_Prop a) (KRSimplify_Prop b)
                           | KRNot_Prop a => KRNot_Prop (KRSimplify_Prop a)
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

Theorem sdisjPrefix_false: forall p1 p2 s1 s2,
    sdisjPrefix (srev s1) (srev s2)=true -> False=(p1++s1=p2++s2)%string.
Admitted.

Theorem my_in_app_iff: forall A (a:A) (l1:list A) (l2:list A), (@In A a (l1++l2)) = (@In A a l1 \/ @In A a l2).
Admitted.

Hint Rewrite my_in_app_iff : kami_rewrite_db.

Theorem my_DisjKey_Append1:
  forall T Q (x:list (T*Q)) y z,
  (DisjKey (x++y) z)=(DisjKey x z /\ DisjKey y z).
Admitted.

Hint Rewrite my_DisjKey_Append1 : kami_rewrite_db.

Theorem my_DisjKey_Append2:
    forall T Q (x:list (T*Q)) y z,
           (DisjKey x (y++z))=(DisjKey x y /\ DisjKey x z).
Admitted.

Hint Rewrite my_DisjKey_Append2 : kami_rewrite_db.

Theorem my_DisjKey_In_map2:
  forall A B a (k:A) r l, @DisjKey A B a ((k,r)::l)=(~List.In k (List.map fst a) /\ (DisjKey a l)).
Admitted.

Hint Rewrite my_DisjKey_In_map2 : kami_rewrite_db.

Theorem my_DisjKey_In_map1: forall A B b (k:A) r l,
    (@DisjKey A B ((k,r)::l) b)=(~List.In k (List.map fst b) /\ (DisjKey l b)).
Admitted.

Hint Rewrite my_DisjKey_In_map1 : kami_rewrite_db.

Theorem my_DisjKey_In_map_fst2: forall A B a (f:(A*B)) l,
    @DisjKey A B a (f::l)=(~List.In (fst f) (List.map fst a) /\ (DisjKey a l)).
Admitted.

Hint Rewrite my_DisjKey_In_map_fst2 : kami_rewrite_db.

Theorem my_DisjKey_In_map_fst1: forall A B b (f:(A*B)) l (W:forall (a1:A) (a2:A), {a1=a2}+{a1<>a2}),
    @DisjKey A B (f::l) b=(~List.In (fst f) (List.map fst b) /\ (DisjKey l b)).
Admitted.
    
Hint Rewrite my_DisjKey_In_map_fst1 : kami_rewrite_db.

Theorem my_and_true1: forall p, (p /\ True)=p.
Admitted.

Hint Rewrite my_and_true1 : kami_rewrite_db.

Theorem my_and_false1: forall p, (p /\ False)=False.
Admitted.

Hint Rewrite my_and_false1 : kami_rewrite_db.

Theorem my_and_true2: forall p, (True /\ p )=p.
Admitted.

Hint Rewrite my_and_true2 : kami_rewrite_db.

Theorem my_and_false2: forall p, (False /\ p)=False.
Admitted.

Hint Rewrite my_and_false2 : kami_rewrite_db.

Theorem my_or_true1: forall p, (p \/ True)=True.
Admitted.

Hint Rewrite my_or_true1 : kami_rewrite_db.

Theorem my_or_false1: forall p, (p \/ False)=p.
Admitted.

Hint Rewrite my_or_false1 : kami_rewrite_db.

Theorem my_or_true2: forall p, (True \/ p )=True.
Admitted.

Hint Rewrite my_or_true2 : kami_rewrite_db.

Theorem my_or_false2: forall p, (False \/ p)=p.
Admitted.

Hint Rewrite my_or_false2 : kami_rewrite_db.

Theorem my_not_not: forall p, (~ (~ p))=p.
Admitted.

Hint Rewrite my_not_not : kami_rewrite_db.

Theorem my_not_and_or: forall p q, (~ (p /\ q)) = ((~p) \/ (~q)).
Admitted.

Hint Rewrite my_not_and_or : kami_rewrite_db.

Theorem my_not_or_and: forall p q, (~ (p \/ q)) = ((~p) /\ (~q)).
Admitted.

Hint Rewrite my_not_or_and : kami_rewrite_db.

Theorem my_DisjKey_nil1 : forall A B (x:list (A*B)), DisjKey [] x=True.
Admitted.

Hint Rewrite my_DisjKey_nil1 : kami_rewrite_db.

Theorem my_DisjKey_nil2 : forall A B (x:list (A*B)), DisjKey x []=True.
Admitted.

Hint Rewrite my_DisjKey_nil2 : kami_rewrite_db.

Theorem my_not_true_false : (~ True) = False.
Admitted.

Hint Rewrite my_not_true_false : kami_rewrite_db.

Theorem my_not_false_true : (~ False) = True.
Admitted.

Hint Rewrite my_not_false_true : kami_rewrite_db.

Theorem my_eq_refl : forall A (a:A) (b:A), (a=b)=(b=a).
Admitted.

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

Theorem KRSimplifySound_Prop: forall e,
    KRExprDenote_Prop (KRSimplify_Prop e) = KRExprDenote_Prop e.
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
                KRSimplify_Prop KRSimplifyTop_Prop
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
                KRSimplify_Prop KRSimplifyTop_Prop
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

