Require Import Kami.All.
Require Import Kami.GallinaModules.AuxLemmas.
Require Import Kami.GallinaModules.Relations.

(* subst, but also rewrites with arbitrary equalities *)
Ltac mySubst :=
  progress first [subst |
                  match goal with
                  | [H : _ = _ |- _] =>
                    try rewrite H in *; clear H; subst
                  end].

Ltac find_if_inside :=
  match goal with
  | [H : ?X = _ |- context[if ?X then _ else _]] => rewrite H
  | [ |- context[if ?X then _ else _]]
    => let G := fresh "G" in
       has_evar X
       ; destruct X eqn: G
  end.

(* clear out trivially true statements *)
Ltac clean_useless_hyp :=
  match goal with
  | [ H : ?a = ?a |- _] => clear H
  | [ H : True |- _] => clear H
  | [ H : SubList nil _ |- _] => clear H
  | [ H : key_not_In _ nil |- _] => clear H
  | [ H : DisjKey _ nil |- _] => clear H
  | [ H : DisjKey nil _ |- _] => clear H
  | [ H : NoDup nil |- _] => clear H
  | [ H : NoDup (_ :: nil) |- _] => clear H
  | [ H : ~In _ nil |- _] => clear H
  | [ H1 : ?P, H2 : ?P |- _] => clear H1
  end.

(* Transforms hypotheses and goals into a form suitable for the solvers *)
Ltac my_simplifier :=
  match goal with
  | [ H1 : ?a = ?b,
           H2 : ?a = ?c |- _] => rewrite H1 in H2
  | [ H : context [map _ nil] |- _] => rewrite map_nil in H
  | [ H : context [map ?f (?l1 ++ ?l2)] |- _] => rewrite (map_app f l1 l2) in H
  | [ H : context [map ?f (?l1 :: ?l2)] |- _] => rewrite (map_cons f l1 l2) in H
  | [ H : context [?a ++ nil] |- _] => rewrite (app_nil_r a) in H
  | [ H : context [nil ++ ?a] |- _] => rewrite (app_nil_l a) in H
  | [ H : _ \/ _ |- _] => destruct H
  | [ H : _ /\ _ |- _] => destruct H
  | [ H : SubList _ nil |- _] => apply SubList_nil_r in H
  | [ H : (_, _) = (_, _) |- _] => apply inversionPair in H; destruct H as [? ?]
  | [ H : existT ?a ?b ?c1 = existT ?a ?b ?c2 |- _] => apply Eqdep.EqdepTheory.inj_pair2 in H
  | [ H : existT ?a ?b1 ?c1 = existT ?a ?b2 ?c2 |- _] => apply inversionExistT in H; destruct H as [? ?]
  | [ H1 : In (?a, ?b) ?c, H2 : ~In ?a (map fst ?c) |- _] => apply (in_map fst) in H1; contradiction
  | [ H : forall _, (~In _ (map fst ?l1)) \/ (~In _ (map fst ?l2)) |- _] => fold (DisjKey l1 l2) in H
  | [ |- context [map _ nil]] => rewrite map_nil
  | [ |- context [map ?f (?l1 ++ ?l2)]] => rewrite (map_app f l1 l2)
  | [ |- context [map _ (?l1 :: ?l2)]] => rewrite map_cons
  | [ |- context [In _ (_ :: _)]] => rewrite in_cons_iff
  | [ |- context [In _ (_ ++ _)]] => rewrite in_app_iff
  | [ |- context [map fst (doUpdRegs _ _)]] => rewrite doUpdRegs_preserves_keys
  | [ |- context [fst (doUpdReg _ _ )]] => rewrite doUpdReg_preserves_keys
  | [ |- context [doUpdRegs nil _]] => rewrite doUpdRegs_nil
  | [ |- context [doUpdReg nil _]] => rewrite doUpdReg_nil
  | [ |- ( _ , _ ) = ( _ , _ )] => f_equal
  | [ |- (map (fun x => (fst x, projT1 (snd x))) _) = _ :: _] => eapply BreakGKAEvar1
  | [ |- (map (fun x => (fst x, projT1 (snd x))) _) = _ ++ _] => eapply BreakGKAEvar2
  | [ H : SubList (_ :: _) _ |- _] => rewrite SubList_cons_l_iff in H
  | [ H : SubList (_ ++ _) _ |- _] => rewrite SubList_app_l_iff in H
  end.

Ltac decompose_In H :=
  repeat (rewrite in_cons_iff in H || rewrite in_app_iff in H).

Ltac aggressive_key_finder2 :=
  (match goal with
   | [ H1 : SubList (map fst _) (map fst _) |- _]
     => revert H1
        ; aggressive_key_finder2
   | [ H1 : SubList (map (fun x => (fst x, projT1 (snd x))) _)
                    (map (fun y => (fst y, projT1 (snd y))) _) |- _]
     => apply (SubList_map fst) in H1
        ; repeat rewrite fst_getKindAttr in H1
        ; revert H1
        ; aggressive_key_finder2
   | [ H1 : SemAction _ _ _ _ _ _ |- _]
     => apply SemActionSub in H1
        ; destruct H1 as [? ?]
        ; aggressive_key_finder2
   | [ H1 : SubList _ _ |- _]
     => apply (SubList_map fst) in H1
        ; revert H1
        ; aggressive_key_finder2
   | _ => idtac
   end)
  ; intros.

(* Aggressively attempts to find getKindAttr connections, probably should be more aggressive *)
Ltac aggressive_gka_finder l1 :=
  match goal with
  | [ H1 : SubList l1 _ |- _]
    => apply (SubList_map (fun x => (fst x, projT1 (snd x)))) in H1
  | [ H1 : SemAction _ _ l1 _ _ _ |- _]
    => apply SemActionReadsSub in H1
  | [ H1 : SemAction _ _ _ l1 _ _ |- _]
    => apply SemActionUpdSub in H1
  end.

(* Aggressively attempts to find getKindAttr connections, probably should be more aggressive *)
Ltac aggressive_gka_finder2 :=
  (match goal with
   | [ H1 : SubList (map (fun x => (fst x, projT1 (snd x))) _)
                    (map (fun y => (fst y, projT1 (snd y))) _) |- _]
     => revert H1
        ; aggressive_gka_finder2
   | [ H1 : SubList _ _ |- _]
     => apply (SubList_map (fun x => (fst x, projT1 (snd x)))) in H1
        ; revert H1
        ; aggressive_gka_finder2
   | [ H1 : SemAction _ _ _ _ _ _ |- _]
     => apply SemActionSub in H1
        ; destruct H1 as [? ?]
        ; aggressive_gka_finder2
   | [ H1 : SemAction _ _ _ _ _ _ |- _]
     => apply SemActionSub in H1
        ; destruct H1 as [? ?]
        ; aggressive_gka_finder2
   | _ => idtac
   end)
  ; intros.

(* Searches for hypotheses that can be transormed into SubList statements *)
Ltac aggressive_sublist_finder2 :=
  (match goal with
   | [ H : SubList _ _ |- _]
     => revert H
        ; aggressive_sublist_finder2
   | [ H : SemAction _ _ _ _ _ _ |- _]
     => apply SemActionSub in H
        ; destruct H
        ; aggressive_sublist_finder2
   | _ => idtac
   end)
  ; intros.

(* Attempts to solve statements about simplified SubLists *)
Ltac sublist_sol :=
  (match goal with
   | [ |- SubList _ (map (fun y => (fst y, projT1 (snd y))) ?b)]
     => aggressive_gka_finder2
   | [ |- SubList ?a ?b] =>
     aggressive_sublist_finder2
   end)
  ; let v := fresh "v" in
    let HIn := fresh "H" in
    intros v HIn
    ; repeat my_simplifier
    ; repeat
        (match goal with
         | [HSubList : SubList ?c ?d |- _] =>
           (specialize (HSubList v) || clear HSubList)
         end)
    ; tauto.
  
(* Attempts to solve key Disjointness goals by aggressively finding
     all logical connections between every type of key *)
Ltac solve_keys :=
  let TMP1 := fresh "H" in
  let TMP2 := fresh "H" in
  let v := fresh "k" in
  (match goal with
   | [ |- ~ In ?k (map fst ?l1)]
     => specialize (SubList_refl (map fst l1)) as TMP1
        ; aggressive_key_finder2
        ; repeat (match goal with
                  | [H : SubList (map fst _) (map fst _) |- _] => specialize (H k)
                  | [H : DisjKey _ _ |- _] => specialize (H k)
                  end)
        ; repeat rewrite key_not_In_fst in *
   | [ |- DisjKey ?l1 ?l2]
     => specialize (SubList_refl (map fst l1)) as TMP1
        ; specialize (SubList_refl (map fst l2)) as TMP2
        ; aggressive_key_finder2
        ; intro v
        ; repeat (match goal with
                  | [H : SubList (map fst _) (map fst _) |- _] => specialize (H v)
                  | [H : DisjKey _ _ |- _] => specialize (H v)
                  end)
   end); repeat rewrite key_not_In_fst in *
  ; tauto.

(* Breaks SubList goal into multiple, generic goals recognizable by the solver *)
Ltac normalize_sublist_l :=
  match goal with
  | [ |- In _ _] => my_simplifier
  | [ |- SubList (_ :: _) _]
    => rewrite SubList_cons_l_iff; split
  | [ |- SubList (_ ++ _) _]
    => rewrite SubList_app_l_iff; split
  end.

(* slightly problematic, unifies variables under a specific condition 
     asserts should attempt to solve using the solver instead of just leaving it for later *)
Ltac resolve_sublist :=
  let HNoDup := fresh "HNoDup" in
  let HSubList2 := fresh "HSubList" in
  match goal with
  | [Heq : (map (fun x => (fst x, _)) ?o1) = (map (fun y => (fst y, _)) ?o2),
           HSubList1 : SubList ?o1 ?o3 |- _] =>
    assert (NoDup (map fst o3)) as HNoDup
    ;[ 
    | assert (SubList o2 o3) as HSubList2
      ; [clear HNoDup
        | specialize (SubList_chain HNoDup HSubList1 HSubList2 (getKindAttr_fst _ _ Heq)) as ?
          ; subst
          ; clear Heq HNoDup HSubList1 HSubList2]
    ]
  | [Heq : (map fst ?o1) = (map fst ?o2),
           HSubList1 : SubList ?o1 ?o3 |- _] =>
    assert (NoDup (map fst o3)) as HNoDup
    ;[clear HNoDup
     | assert (SubList o2 o3) as HSubList2
       ; [
       | specialize (SubList_chain HNoDup HSubList1 HSubList2 Heq) as ?
         ; subst
         ; clear Heq HNoDup HSubList1 HSubList2]
     ]
  end.

(* slightly problematic, unifies variables under a specific condition 
     asserts should attempt to solve using the solver instead of just leaving it for later *)
Ltac resolve_sublist2 :=
  match goal with
  | [ Heq:map (fun x => (fst x, _)) ?o1 = map (fun y => (fst y, _)) ?o2,
          HSubList1 : SubList ?o1 ?o3,
                      HNoDup:NoDup (map fst ?o3)
      |- _ ]
    => let HSubList2 := fresh "H" in
       assert (HSubList2 : SubList o2 o3)
       ;[ sublist_sol
        | specialize (SubList_chain HNoDup HSubList1 HSubList2 (getKindAttr_fst _ _ Heq)) as ?
          ; clear HSubList2]
       ; mySubst
  end.

(* solves specific Effectful/Effectless relation conditions *)
Ltac resolve_rel :=
  let HupdsNil := fresh "HupdsNil" in
  let HcallsNil := fresh "HcallsNil" in
  let reads_s := fresh "reads_s" in
  let HSemAction_s := fresh "HSemAction_s" in
  let upds_s := fresh "upds_s" in
  let HdoUpdRegsR := fresh "HdoUpdRegsR" in
  match goal with
  | [HSemAction : SemAction ?o_i ?a_i _ _ _ _,
                  HERelation : EffectlessRelation ?R ?a_i _,
                               HoRelation : ?R ?o_i _ |- _] =>
    specialize (HERelation _ _ HoRelation _ _ _ _ HSemAction)
      as [HupdsNil [HcallsNil [reads_s HSemAction_s]]]
    ; clear HSemAction
  | [HSemAction : SemAction ?o_i1 (?a_i _) _ _ _ _,
                  HERelation : forall _, EffectlessRelation ?R (?a_i _) _,
       HoRelation : ?R ?o_i2 ?o_j |- _] =>
    specialize (HERelation _ _ _ HoRelation _ _ _ _ HSemAction) as [HupdsNil [HcallsNil [reads_s HSemAction_s]]]
    ; clear HSemAction
  | [HSemAction : SemAction ?o_i1 ?a_i _ _ _ _,
                  HERelation : EffectfulRelation ?R ?a_i _,
                               HoRelation : ?R ?o_i2 ?o_j |- _] =>
    specialize (HERelation _ _ HoRelation _ _ _ _ HSemAction) as [reads_s [upds_s [HSemAction_s HdoUpdRegsR]]]
    ; clear HSemAction
  | [HSemAction : SemAction ?o_i1 (?a_i _) _ _ _ _,
                  HERelation : forall _, EffectfulRelation ?R (?a_i _) _,
       HoRelation : ?R ?o_i2 ?o_j |- _] =>
    specialize (HERelation _ _ _ HoRelation _ _ _ _ HSemAction) as [reads_s [upds_s [HSemAction_s HdoUpdRegsR]]]
    ; clear HSemAction
  end.

(* Despite the name, likely not aggressive enough.
     Should replace SemAction*Sub with SemActionReadsUpdSub and just match every SemAction *)
Ltac aggressive_key_finder l1 :=
  match goal with
  | [ H1 : SubList l1 _ |- _]
    => apply (SubList_map fst) in H1
  | [ H1 : SubList (map (fun x => (fst x, projT1 (snd x))) l1) (map (fun y => (fst y, projT1 (snd y))) _) |- _]
    => apply (SubList_map fst) in H1
       ; repeat rewrite fst_getKindAttr in H1
  | [ H1 : SemAction _ _ l1 _ _ _ |- _]
    => apply SemActionReadsSub in H1
  | [ H1 : SemAction _ _ _ l1 _ _ |- _]
    => apply SemActionUpdSub in H1
  end.

(* Transforms doUpdRegs statements into a version recognizable by the reducer *)
Ltac doUpdRegs_simpl :=
  match goal with
  | [ |- context [doUpdRegs ?a (?b ++ ?c)]] => rewrite (doUpdRegs_app_r b a c)
  | [ |- context [doUpdRegs ?a (?b :: ?c)]] => rewrite (doUpdRegs_cons_r' a c b)
  | [ |- context [doUpdRegs (?a ++ ?b) ?c]] => rewrite (doUpdRegs_app_l c a b)
  | [ |- context [doUpdRegs (?a :: ?b) ?c]] => rewrite (doUpdRegs_cons_l' b c a)
  | [ |- context [doUpdReg (?a ++ ?b) ?c]] => rewrite (doUpdReg_app a b c)
  | [ |- context [doUpdReg (?a :: ?b) ?c]] => rewrite (doUpdReg_cons b a c)
  | [H : context [doUpdRegs ?a (?b ++ ?c)] |- _] => rewrite doUpdRegs_app_r in H
  | [H : context [doUpdRegs ?a (?b :: ?c)] |- _] => rewrite doUpdRegs_cons_r' in H
  | [H : context [doUpdRegs (?a ++ ?b) ?c] |- _] => rewrite doUpdRegs_app_l in H
  | [H : context [doUpdRegs (?a :: ?b) ?c] |- _] => rewrite doUpdRegs_cons_l' in H
  | [H : context [doUpdReg (?a ++ ?b) ?c] |- _] => rewrite doUpdReg_app in H
  | [H : context [doUpdReg (?a_ :: ?b) ?c] |- _] => rewrite doUpdReg_cons in H
  end.

(* Simply breaks apart a goal *)
Ltac goal_split :=
  match goal with
  | [ |- ex _] => eexists
  | [ |- _ /\ _] => split
  end.

(* Attempts to reduce statements about the getKindAttr of doUpdRegs *)
Ltac gka_doUpdReg_red :=
  match goal with
  | [ |- context [getKindAttr (doUpdRegs ?u ?o)]]
    => let TMP1 := fresh "H" in
       let TMP2 := fresh "H" in
       assert (NoDup (map fst o)) as TMP1
       ; [repeat rewrite doUpdRegs_preserves_keys (*a bit weak *)
          ; auto
         | assert (SubList (getKindAttr u) (getKindAttr o)) as TMP2
           ;[ repeat (aggressive_gka_finder u)
              ; auto
            | rewrite (doUpdReg_preserves_getKindAttr _ _ TMP1 TMP2)
              ; clear TMP1 TMP2]]
  end.


(* Makes a best guess for a solution and unifies Evars
     potentially dangerous. *)
Ltac my_risky_solver :=
  match goal with
  | [ |- _ :: _ = _ :: _ ] => f_equal
  | [ |- _ ++ _ = _ ++ _ ] => f_equal
  | [ H : ?a = ?b |- _] => discriminate
  | [ |- map _ ?x = nil] => is_evar x; apply map_nil
  end.

(* Reduces simple goals, but may make things more difficult by changing forms to 
     something harder to solve *)
Ltac my_risky_simplifier :=
  match goal with
  | [ |- context [_ ++ nil]] => rewrite app_nil_r
  | [ |- context [nil ++ _]] => rewrite app_nil_l
  end.

(* A bit of a patch, trying to fulfill obligations down the line that are not alway obvious *)
Ltac sublist_iff :=
  match goal with
  | [ H : SubList ?l (map (fun x => (fst x, projT1 (snd x))) _)
      |- _] => (match l with
                | (map (fun y => (fst y, projT1 (snd y))) _) => revert H; sublist_iff
                | _ => rewrite SubList_map_iff in H; dest; sublist_iff
                end)
  | _ => intros
  end.


Ltac extract_gatherActions' subRegs :=
  match goal with
  | [ H : SemAction ?o (gatherActions (map ?f ?l) (fun _ : _ => ?s)) _ _ _ _ |- _]
    => assert (ActionWb subRegs s /\
               (forall t',
                   ActionWb subRegs (f t')))
  end.

(* consumes the main body of a SemAction *)
Ltac main_body :=
  match goal with
  | [H: SemAction _ (Return _) _ _ _ _ |- _]
    => apply inversionSemAction' in H
       ; destruct H as [? [? [? ?]]]
  | [H: SemAction _ (MCall _ _ _ _) _ _ _ _ |- _]
    => apply inversionSemAction' in H
       ; destruct H as [? [? [? ?]]]
  | [H: SemAction _ (LetAction _ _) _ _ _ _ |- _]
    => apply inversionSemAction' in H
       ; destruct H as [? [? [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]]]]
  | [H: SemAction _ (ReadReg _ _ _) _ _ _ _ |- _]
    => let TMP := fresh "H" in
       apply inversionSemAction' in H
       ; destruct H as [? [? [TMP [? ?]]]]; decompose_In TMP
  | [H: SemAction _ (WriteReg _ _ _) _ _ _ _ |- _]
    => apply inversionSemAction' in H
       ; destruct H as [? [? [? [? ?]]]]
  | [H: SemAction _ (IfElse _ _ _ _) _ _ _ _ |- _]
    => apply inversionSemAction' in H;
       let TMP := fresh "H" in
       destruct evalExpr eqn:TMP in H
       ; destruct H as [? [? ?]]
  | [H: SemAction _ (LetExpr _ _) _ _ _ _ |- _]
    => apply inversionSemAction' in H
  | [H: SemAction _ (ReadNondet _ _) _ _ _ _ |- _]
    => apply inversionSemAction' in H
       ; destruct H as [? ?]
  | [H: SemAction _ (Sys _ _) _ _ _ _ |- _]
    => apply inversionSemAction' in H
  | [H: SemAction _ (gatherActions (map _ ?l) _) _ _ _ _ |- _]
    => idtac (* TODO : put gatherActions workflow here *)
  end.

Ltac risky_unify :=
  match goal with
  | [ |- ?a = _] => has_evar a; reflexivity
  | [ |- _ = ?a] => has_evar a; reflexivity
  end.

Ltac resolve_In :=
  let TMP := fresh "H" in
  match goal with
  | [ HNoDup : NoDup (map fst ?o),
               H1 : In (?s, ?a) ?o,
                    H2 : In (?s, ?b) ?o |- _]
    => specialize (NoDup_map_fst HNoDup H1 H2) as TMP; EqDep_subst; clear H1
  end.

Ltac extract_in_map :=
  (match goal with
   | [H : In _ (map _ _) |- _]
     => let TMP := fresh "H" in
        specialize H as TMP
        ; rewrite in_map_iff in TMP
        ; revert H TMP
        ; extract_in_map
   | [H : SubList _ (map _ _) |- _]
     => let TMP := fresh "H" in
        specialize H as TMP
        ; rewrite SubList_map_iff in TMP
        ; revert H TMP
        ; extract_in_map
   | _ => idtac
   end)
  ; intros
  ; dest.

Ltac extract_in_map' :=
  (match goal with
   | [H : In _ (map _ _) |- _]
     => let TMP := fresh "H" in
        specialize H as TMP
        ; rewrite in_map_iff in TMP
        ; let x1 := fresh "x" in
          let x2 := fresh "x" in
          let x3 := fresh "x" in
          let Hfeq := fresh "H" in
          let HIn := fresh "H" in
          destruct TMP as [[x1 [x2 x3]] [Hfeq HIn]]
          ; revert H x1 Hfeq HIn
          ; extract_in_map'
   | [H : SubList _ (map _ _) |- _]
     => let TMP := fresh "H" in
        specialize H as TMP
        ; rewrite SubList_map_iff in TMP
        ; revert H TMP
        ; extract_in_map'
   | _ => idtac
   end)
  ; intros
  ; dest
  ; simpl in *
  ; repeat my_simplifier; subst.

Ltac dangerous_solver :=
  match goal with
  | [ H : ?a = ?b |- ?c = ?b] =>
    has_evar c
    ; apply H
  end.

Ltac right_subst :=
  match goal with
  | [ H1 : ?b = ?a,
           H2 : ?c = ?a
      |- _] => rewrite <- H1 in H2
  end.

Ltac normalize_key_hyps1 :=
  match goal with
  | [ H : context [map fst (_ ++ _)] |- _] => rewrite map_app in H
  | [ H : forall _, (~In _ (map fst ?l1)) \/ (~In _ (map fst ?l2)) |- _]
    => fold (DisjKey l1 l2) in H
  | [ H : NoDup (_ ++ _) |- _]
    => rewrite (NoDup_app_Disj_iff string_dec) in H; destruct H as [? [? ?]]
  | [ H : DisjKey (_ ++ _) _ |- _] => rewrite DisjKey_app_split_l in H; destruct H as [? ?]
  | [ H : DisjKey _ (_ ++ _) |- _] => rewrite DisjKey_app_split_r in H; destruct H as [? ?]
  | [ H : ~In _ (_ ++ _) |- _] => rewrite (nIn_app_iff string_dec) in H; destruct H as [? ?]
  | [ H : DisjKey (_ :: _) _ |- _] => rewrite DisjKey_cons_l_str in H; destruct H as [? ?]
  | [ H : DisjKey _ (_ :: _) |- _] => rewrite DisjKey_cons_r_str in H; destruct H as [? ?]
  end.

Ltac normalize_key_hyps2 :=
  match goal with
  | [ H : context [map fst (_ :: _)] |- _] => rewrite map_cons in H
  | [ H : context [map fst nil] |- _] => rewrite map_nil in H
  | [ H : NoDup (_ :: _) |- _] => rewrite NoDup_cons_iff in H; destruct H as [? ?]
  | [ H : key_not_In _ (_ :: _) |- _] => rewrite key_not_In_cons in H; destruct H as [? ?]
  | [ H : ~In _ (_ :: _) |- _] => rewrite not_in_cons in H; destruct H as [? ?]
  end.

Ltac normalize_key_hyps :=
  repeat normalize_key_hyps1;
  repeat normalize_key_hyps2;
  cbn [fst] in *;
  repeat clean_useless_hyp.

Ltac my_simpl_solver :=
  match goal with
  | [ H : ?P |- ?P] => apply H
  | [ |- DisjKey nil _] => apply DisjKey_nil_l
  | [ |- DisjKey _ nil] => apply DisjKey_nil_r
  | [ |- ?a = ?a] => reflexivity
  | [ |- True] => apply I
  | [ |- NoDup nil] => constructor
  | [ |- ~In _ nil] => intro; my_simpl_solver
  | [ H : False |- _] => exfalso; apply H
  | [ H : ?a <> ?a |- _] => exfalso; apply H; reflexivity
  | [ H : In _ nil |- _] => inversion H
  | [ |- SubList nil _ ] => apply SubList_nil_l
  | [ |- SubList ?a ?a] => apply SubList_refl
  | [ |- ?a = ?b] => is_evar a; reflexivity
  | [ |- ?a = ?b] => is_evar b; reflexivity
  | [ H: ?a = ?b |- _] => discriminate
  | [H1 : ?a = ?b,
          H2 : ?a <> ?b |- _] => exfalso; apply H2; rewrite H1; reflexivity
  | [H1 : ?a = ?b,
          H2 : ?b <> ?a |- _] => exfalso; apply H2; rewrite H1; reflexivity
  | [|- nil = ?l1 ++ ?l2] => symmetry; apply (app_eq_nil l1 l2); split
  | [|- ?l1 ++ ?l2 = nil] => apply (app_eq_nil l1 l2); split
  | [H1 : key_not_In ?s ?l, H2 : In (?s, _) ?l |- _]
    => exfalso; specialize (H1 _ H2); contradiction
  | [H1 : key_not_In ?s ?l |- ~In ?s (map fst ?l)]
      => rewrite <- key_not_In_fst; apply H1
  | [H1 : key_not_In ?s ?l, H2 : In ?s (map fst ?l) |- _]
    => exfalso; rewrite key_not_In_fst in H1; contradiction
  | [H1 : ?a <> ?b |- ?b <> ?a]
    => apply (not_eq_sym H1)
  end.

Ltac or_unify :=
  match goal with
  | [ |- In _ _ ] => repeat my_simplifier; my_simpl_solver
  | [ |- ?a = ?b] => repeat my_simplifier; my_simpl_solver
  | [ |- ?a \/ ?b] => left; or_unify
  | [ |- ?a \/ ?b] => right; or_unify
  end.

Ltac normalize_key_concl1 :=
  match goal with
  | [|- context [map fst (_ ++ _)]] => rewrite map_app               
  | [|- forall _, (~In _ (map fst ?l1)) \/ (~In _ (map fst ?l2))]
    => fold (DisjKey l1 l2)
  | [ |- NoDup (_ ++ _)] => rewrite (NoDup_app_Disj_iff string_dec); repeat split
  | [ |- DisjKey (_ ++ _) _] => rewrite DisjKey_app_split_l; split
  | [ |- DisjKey _ (_ ++ _)] => rewrite DisjKey_app_split_r; split
  | [ |- ~In _ (_ ++ _)] => rewrite (nIn_app_iff string_dec); split
  | [ |- DisjKey (_ :: _) _] => rewrite DisjKey_cons_l_str; split
  | [ |- DisjKey _ (_ :: _)] => rewrite DisjKey_cons_r_str; split
  end.

Ltac normalize_key_concl2 :=
  match goal with
  | [ |- context [map fst (_ :: _)]] => rewrite map_cons
  | [ |- context [map fst nil]] => rewrite map_nil
  | [ |- NoDup (_ :: _)] => rewrite NoDup_cons_iff; split
  | [ |- key_not_In _ (_ :: _)] => rewrite key_not_In_cons; split
  | [ |- ~In _ (_ :: _)] => rewrite not_in_cons; split
  | [ |- key_not_In _ ?l] =>
    match l with
    | _ => has_evar l; idtac
    | _ => rewrite key_not_In_fst
    end
  | [ |- ~In _ (_ :: _)] => rewrite not_in_cons; split
  | [ |- ~In _ (_ ++ _)] => rewrite (nIn_app_iff string_dec); split
  end.

Ltac normalize_key_concl :=
  repeat normalize_key_concl1;
  repeat normalize_key_concl2;
  cbn [fst];
  repeat (solve_keys || my_simpl_solver).

Ltac normal_solver :=
  repeat my_simplifier
  ; repeat my_simpl_solver
  ; repeat or_unify
  ; repeat find_if_inside
  ; repeat normalize_key_concl
  ; repeat sublist_sol
  ; repeat solve_keys.

Ltac normal_solver2 :=
  repeat my_simplifier
  ; repeat my_simpl_solver
  ; repeat resolve_In
  ; repeat or_unify
  ; repeat risky_unify
  ; repeat resolve_sublist2
  ; repeat find_if_inside
  ; repeat normalize_key_concl
  ; repeat normalize_sublist_l
  ; repeat sublist_sol
  ; repeat solve_keys.

Ltac resolve_wb :=
  let HNoDup := fresh "H" in
  let HSubList := fresh "H" in
  match goal with
  | [HSemAction1 :SemAction ?o1 ?a_i _ _ _ _,
                  HActionWb : ActionWb ?myR ?a_i |- _] =>
    assert (NoDup (map fst o1)) as HNoDup
    ;[repeat normalize_key_concl
     | assert (SubList myR (getKindAttr o1)) as HSubList
       ;[clear HNoDup HSemAction1
         ; repeat normalize_sublist_l
         ; sublist_sol
        | specialize (HActionWb _ _ _ _ _ HNoDup HSubList HSemAction1)
          as [[? [? [? [? ?]]]] ?]
          ; try resolve_sublist2
          ; clear HSemAction1 HNoDup HSubList]]
  | [HSemAction1 : SemAction ?o1 (?a_i _) _ _ _ _,
                   HActionWb : forall _, ActionWb ?myR (?a_i _) |- _] =>
    assert (NoDup (map fst o1)) as HNoDup
    ;[repeat normalize_key_concl
     | assert (SubList myR (getKindAttr o1)) as HSubList
       ;[clear HNoDup HSemAction1
         ; repeat normalize_sublist_l
         ; sublist_sol
        | specialize (HActionWb _ _ _ _ _ _ HNoDup HSubList HSemAction1)
          as [[? [? [? [? ?]]]] ?]
          ; try resolve_sublist2
          ; clear HSemAction1 HNoDup HSubList]]
  end.

Ltac hyp_consumer :=
  repeat mySubst;
  normalize_key_hyps;
  repeat (repeat main_body
          ; repeat mySubst
          ; repeat (my_simplifier; repeat my_simpl_solver; repeat clean_useless_hyp)
          ; repeat mySubst
          ; repeat normalize_key_hyps
          ; repeat (my_simplifier; repeat my_simpl_solver; repeat clean_useless_hyp)
          ; repeat (resolve_wb; repeat my_simpl_solver; repeat clean_useless_hyp)
          ; repeat resolve_rel
          ; repeat mySubst
          ; repeat (my_simplifier ; repeat my_simpl_solver; repeat clean_useless_hyp))
  ; repeat my_simpl_solver
  ; cbn [fst] in *.

Ltac goal_body :=
  match goal with
  | [ |- SemAction _ (Return _) _ _ _ _ ] => econstructor 10
  | [ |- SemAction _ (MCall _ _ _ _) _ _ _ _] => econstructor 1
  | [ |- SemAction _ (LetAction _ _) _ _ _ _] => econstructor 3
  | [ |- SemAction _ (ReadReg _ _ _) _ _ _ _] => econstructor 5
  | [ |- SemAction _ (WriteReg _ _ _) _ _ _ _] => econstructor 6
  | [ |- SemAction _ (IfElse _ _ _ _) _ _ _ _]
    => eapply SemAction_if_split
       ;[ find_if_inside| | | | ]
  | [ |- SemAction _ (LetExpr _ _) _ _ _ _] => econstructor 2
  | [ |- SemAction _ (ReadNondet _ _) _ _ _ _] => econstructor 4
  | [ |- SemAction _ (Sys _ _) _ _ _ _] => econstructor 9
  | [ H : SemAction ?o ?a _ _ _ _ |- SemAction ?o ?a _ _ _ _]
    => apply H
  | [ H : SemAction ?o1 ?a _ _ _ _ |- SemAction ?o2 ?a _ _ _ _]
    => eapply SemActionExpand;[| apply H; sublist_sol]
  end.

Ltac doUpdRegs_red :=  
  repeat 
    (match goal with
     | [ |- context [ doUpdRegs nil _]] => rewrite doUpdRegs_nil
     | [ |- context [ doUpdReg nil _]] => rewrite doUpdReg_nil
     | |- context [ oneUpdRegs ?r ?o ] =>
       let TMP := fresh "H" in
       assert (TMP : ~ In (fst r) (map fst o));
       [ repeat
           match goal with
           | |- context [ map fst (doUpdRegs _ _) ] => rewrite doUpdRegs_preserves_keys
           end; (solve_keys || my_simpl_solver)
       | rewrite (oneUpdRegs_notIn _ _ TMP); clear TMP ]
     | |- context [ doUpdReg ?u ?r ] =>
       let TMP := fresh "H" in
       assert (TMP : ~ In (fst r) (map fst u));
       [ repeat
           match goal with
           | |- context [ map fst (doUpdRegs _ _) ] => rewrite doUpdRegs_preserves_keys
           end; (solve_keys || my_simpl_solver)
       | rewrite (doUpdReg_notIn _ _ TMP); clear TMP ]; cbn[fst]
     end);
  repeat
    match goal with
    | |- context [oneUpdReg _ _ ] => cbv [oneUpdReg fst]
    | [|- context [?a =? ?a]] => rewrite eqb_refl 
    | H : fst ?r1 = fst ?r2
      |- context [fst ?r1 =? fst ?r2] =>
      rewrite (proj2 (String.eqb_eq (fst r1) (fst r2)) H)
    | H : fst ?r2 = fst ?r1
      |- context [fst ?r1 =? fst ?r2] =>
      apply eq_sym in H; rewrite (proj2 (String.eqb_eq (fst r1) (fst r2)) H)
    | H : fst ?r1 <> fst ?r2
      |- context [fst ?r1 =? fst ?r2] =>
      rewrite (proj2 (String.eqb_neq (fst r1) (fst r2)) H)
    | H : fst ?r2 <> fst ?r1
      |- context [fst ?r1 =? fst ?r2] =>
      apply not_eq_sym in H; rewrite (proj2 (String.eqb_neq (fst r1) (fst r2)) H) 
    | H : ?a = ?b
      |- context [?a =? ?b] =>
      rewrite (proj2 (String.eqb_eq a b) H)
    | H : ?b = ?a
      |- context [?a =? ?b] =>
      apply eq_sym in H; rewrite (proj2 (String.eqb_eq a b) H)
    | H : ?a <> ?b
      |- context [?a =? ?b] =>
      rewrite (proj2 (String.eqb_neq a b) H)
    | H : ?b <> ?a
      |- context [?a =? ?b] =>
      apply not_eq_sym in H; rewrite (proj2 (String.eqb_neq a b) H)
    end.

Ltac extractGKAs :=
  let var := fresh "x" in
  let vfst := fresh "x" in
  let vsnd := fresh "x" in
  let p1 := fresh "x" in
  let p2 := fresh "x" in
  let Heq := fresh "H" in
  let HIn := fresh "H" in
  let Heq1 := fresh "H" in
  let Heq2 := fresh "H" in
  match goal with
  | [HNoDup : NoDup (map fst ?o),
              H1 : In (?a, ?b) (map (fun x => (fst x, projT1 (snd x))) ?o) |- _]
    => rewrite in_map_iff in H1; destruct H1 as [var [Heq HIn]];
       destruct var as [vfst vsnd]; destruct vsnd as [p1 p2];
       cbn [fst snd projT1] in Heq;
       apply inversionPair in Heq;
       inversion_clear Heq as [Heq1 Heq2]; subst;
       repeat resolve_In
  end.

Ltac goal_consumer1 :=
  repeat (repeat goal_split
          ; repeat goal_body
          ; repeat normal_solver)
  ; repeat (repeat doUpdRegs_simpl
            ; doUpdRegs_red
            ; repeat normal_solver).

Ltac SubList_gka_deconstruct :=
  let x := fresh "x" in
  let Heq1 := fresh "H" in
  let Heq2 := fresh "H" in
  match goal with
  | [H : SubList _ (map (fun x => (fst x, projT1 (snd x))) ?o) |- _]
    => apply SubList_map_iff in H; destruct H as [x [Heq1 Heq2]]; mySubst
  end.

Ltac goal_consumer2 :=
  repeat SubList_gka_deconstruct;
  repeat extractGKAs;
  repeat goal_split
  ; repeat goal_body
  ; repeat normal_solver2
  ; repeat my_risky_solver
  ; repeat normal_solver2.
