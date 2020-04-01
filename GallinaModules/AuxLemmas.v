Require Import Kami.All.
Require Import Kami.GallinaModules.Relations.

Definition doUpdReg (u : RegsT) (r : RegT) : RegT :=
  match findReg (fst r) u with
  | Some y => (fst r, y)
  | None => r
  end.

Fixpoint oneUpdRegs (r : RegT) (o : RegsT) : RegsT :=
  match o with
  | nil => nil
  | x :: o'
    => (if String.eqb (fst x) (fst r)
        then r
        else x) :: (oneUpdRegs r o')
  end.

Definition oneUpdReg (r1 r2 : RegT) : RegT :=
  if String.eqb (fst r2) (fst r1) then r1 else r2.



Lemma InGetKindAttr: forall {name} {o: RegsT} {k} {v} (H: In (name, existT (fullType type) (SyntaxKind k) v) o),
    In (name, SyntaxKind k) (getKindAttr o).
Proof.
  intros; rewrite in_map_iff; eexists; split; eauto; simpl; reflexivity.
Qed.

Lemma doUpdRegs_nil: forall r,
    doUpdRegs [] r = r.
Proof.
  intros.
  induction r; auto.
  simpl.
  rewrite IHr.
  auto.
Qed.

Lemma in_app_fst: forall {A} {B} {a: A} {l l': list (A * B)},
    ~ In a (map fst l) ->
    In a (map fst (l ++ l')) ->
    In a (map fst l').
Proof.
  intros.
  induction l, l'; simpl in *; auto; intuition.
Qed.

Lemma inImpInFst: forall {A B: Type} (a: A) (b: B) (l: list (A * B)),
    In (a,b) l ->
    In a (map fst l).
Proof.
  intros; rewrite in_map_iff; exists (a, b); auto.
Qed.

Lemma noDupSame: forall (o_s: RegsT),
    List.NoDup (map fst o_s) ->
    forall name k rv_1 rv_2,
      In (name, existT (fullType type) (SyntaxKind k) rv_1) o_s ->
      In (name, existT (fullType type) (SyntaxKind k) rv_2) o_s ->
      rv_1 = rv_2.
Proof.
  induction o_s; intros; simpl in *; intuition; subst.
  - apply inversionPairExistT in H0; inv H0; EqDep_subst; reflexivity.
  - exfalso.
    inv H; apply H3; apply (in_map fst) in H0; auto.
  - exfalso.
    inv H; apply H3; apply (in_map fst) in H2; auto.
  - inv H; eapply IHo_s; eauto.
Qed.

Lemma SubList_Strengthen: forall A (l1 l2: list A) (a: A),
    SubList l1 (a::l2) ->
    ~ In a l1 ->
    SubList l1 l2.
Proof.
  intros.
  unfold SubList in *.
  intros.
  specialize (H x H1).
  inversion H; subst; solve [intuition].
Qed.

Lemma getKindAttrEqImpFstEq: forall (r1 r2: RegsT), (* Possibly replace *)
    getKindAttr r1 = getKindAttr r2 ->
    map fst r1 = map fst r2.
Proof.
  apply getKindAttr_fst.
Qed.

Lemma inGetKindAttrImpInMapFstRegs: forall (r: RegsT) a k,
    In (a, k) (getKindAttr r) ->
    In a (map fst r).
Proof.
  intros.
  erewrite <- fst_getKindAttr, in_map_iff; exists (a, k); eauto.
Qed.

Lemma inFstGetKindAttrIffInFst: forall (r: RegsT) a,
    In a (map fst (getKindAttr r)) <->
    In a (map fst r).
Proof.
  intros; split; intros;
    [rewrite <- fst_getKindAttr | rewrite fst_getKindAttr]; assumption.
Qed.

Lemma stripIrrelevantUpd: forall (name: string) (regs: RegsT) (upds: list RegT) v,
    ~ In name (map fst regs) ->
    doUpdRegs ((name, v) :: upds) regs = doUpdRegs upds regs.
  intros.
  induction regs; simpl; auto;
    simpl in H.
  erewrite IHregs; intuition.
  induction upds; simpl; auto; f_equal;
    case_eq (fst a =? name); auto;
      intro;
      intuition;
      epose (String.eqb_eq (fst a) name);
      destruct i;
      specialize (H3 H2);
      intuition.
Qed.

Lemma NoDupMapFstGetKindAttr: forall (r: RegsT), NoDup (map fst r) <-> NoDup (map fst (getKindAttr r)).
Proof.
  intros; split; intro; [rewrite fst_getKindAttr| rewrite <- fst_getKindAttr]; assumption.
Qed.

Lemma inversionSemAction'
      k o a reads news calls retC
      (evalA: @SemAction o k a reads news calls retC):
  match a with
  | MCall m s e c =>
    exists mret pcalls,
    SemAction o (c mret) reads news pcalls retC /\
    calls = (m, (existT _ _ (evalExpr e, mret))) :: pcalls
  | LetExpr _ e cont =>
    SemAction o (cont (evalExpr e)) reads news calls retC
  | LetAction _ a cont =>
    exists reads1 news1 calls1 reads2 news2 calls2 r1,
    DisjKey news1 news2 /\
    SemAction o a reads1 news1 calls1 r1 /\
    SemAction o (cont r1) reads2 news2 calls2 retC /\
    reads = reads1 ++ reads2 /\
    news = news1 ++ news2 /\
    calls = calls1 ++ calls2
  | ReadNondet k c =>
    exists rv,
    SemAction o (c rv) reads news calls retC
  | ReadReg r k c =>
    exists rv reads2,
    In (r, existT _ k rv) o /\
    SemAction o (c rv) reads2 news calls retC /\
    reads = (r, existT _ k rv) :: reads2
  | WriteReg r k e a =>
    exists pnews,
    In (r, k) (getKindAttr o) /\
    key_not_In r pnews /\
    SemAction o a reads pnews calls retC /\
    news = (r, (existT _ _ (evalExpr e))) :: pnews
  | IfElse p _ aT aF c =>
    match evalExpr p with
    | true =>
      exists r1,
      r1 = retC /\
      SemAction o (LetAction aT c) reads news calls r1
    | false =>
      exists r1,
      r1 = retC /\
      SemAction o (LetAction aF c) reads news calls retC
    end
  | Sys _ c =>
    SemAction o c reads news calls retC
  | Return e =>
    retC = evalExpr e /\
    news = nil /\
    calls = nil /\
    reads = nil
  end.
Proof.
  destruct evalA; eauto; repeat eexists; eauto; destruct (evalExpr p); try discriminate; eexists; split; econstructor; eauto.
Qed.

Lemma SemActionExpand o o' {k} {a : ActionT type k} {reads upds calls ret}:
  forall 
    (HSubList : SubList o o')
    (HSemAction : SemAction o a reads upds calls ret),
    SemAction o' a reads upds calls ret.
Proof.
  revert reads upds calls ret.
  induction a; intros; try (apply inversionSemAction in HSemAction); dest; subst.
  7 : { destruct (evalExpr e) eqn:G; dest; [econstructor 7 | econstructor 8]; eauto. }
  all : econstructor; eauto.
  rewrite in_map_iff in H; dest.
  specialize (HSubList _ H2).
  rewrite in_map_iff.
  exists x0; split; auto.
Qed.

Lemma SubList_chain {B C : Type} (l1 : list (B * C)):
  forall (l2 l3 : list (B * C))
         (HNoDup : NoDup (map fst l2))
         (HSubList1 : SubList l1 l2)
         (HSubList2 : SubList l3 l2)
         (HKeysMatch : map fst l1 = map fst l3),
    l1 = l3.
Proof.
  induction l1; intros.
  - destruct l3; inv HKeysMatch; auto.
  - destruct a; simpl in *.
    destruct l3; inversion HKeysMatch.
    destruct p; simpl in *; subst.
    rewrite (NoDup_map_fst HNoDup (HSubList1 _ (in_eq _ _)) (HSubList2 _ (in_eq _ _))) in *.
    erewrite IHl1; eauto; eapply SubList_cons; eauto.
Qed.


Lemma app_cons :
  (forall (A : Type) (a : A) (l : list A),
      a :: l = [a] ++ l).
Proof. auto. Qed.

Lemma NoDup_app_Disj_iff {B : Type} (eqDec : forall a1 a2 : B, {a1 = a2} + {a1 <> a2}):
  forall (l1 l2 : list B),
    NoDup (l1 ++ l2) <-> NoDup l1 /\ NoDup l2 /\ (forall a : B, ~In a l1 \/ ~In a l2).
Proof.
  red; repeat split; intros; dest.
  rewrite NoDup_app_iff in H; dest; auto.
  rewrite NoDup_app_iff in H; dest; auto.
  apply NoDup_app_Disj; auto.
  rewrite NoDup_app_iff; repeat split; auto; intros.
  destruct (in_dec eqDec a l2); eauto.
  destruct (H1 a); eauto.
  destruct (in_dec eqDec a l1); eauto.
  destruct (H1 a); eauto.
Qed.

Corollary NoDup_app_DisjKey {B : Type} :
  forall (l1 l2 : list (string * B)),
    NoDup (map fst (l1 ++ l2)) <-> NoDup (map fst l1) /\ NoDup (map fst l2) /\ DisjKey l1 l2.
Proof.
  intros; rewrite map_app, NoDup_app_Disj_iff; unfold DisjKey;[reflexivity|apply string_dec].
Qed.

Lemma DisjKey_app_split_r {B C : Type} :
  forall (l1 l2 l3 : list (B * C)),
    DisjKey l1 (l2 ++ l3) <-> DisjKey l1 l2 /\ DisjKey l1 l3.
Proof.
  split; intros.
  - split; intro k; specialize (H k); rewrite map_app, in_app_iff, DeM1 in H; destruct H; dest; auto.
  - dest; intro.
    destruct (H k); destruct (H0 k); rewrite map_app, in_app_iff, DeM1; auto.
Qed.


Corollary DisjKey_app_split_l {B C : Type} :
  forall (l1 l2 l3 : list (B * C)),
    DisjKey (l1 ++ l2) l3 <-> DisjKey l1 l3 /\ DisjKey l2 l3.
Proof.
  split; intros.
  - apply DisjKey_Commutative in H; rewrite DisjKey_app_split_r in H; dest; eauto using DisjKey_Commutative.
  - apply DisjKey_Commutative; rewrite DisjKey_app_split_r; dest; eauto using DisjKey_Commutative.
Qed.

Lemma NoDup_singleton_map {B C : Type}:
  forall (a : B) (f : B -> C),
    NoDup (map f [a]) <-> True.
Proof.
  intros; repeat constructor; auto.
Qed.

Lemma DisjKey_singletons {B : Type} :
  forall (a b : string * B),
    DisjKey [a] [b] <-> fst a <> fst b.
Proof.
  unfold DisjKey; split; repeat intro; simpl in *.
  - rewrite H0 in H; destruct (H (fst b)); auto.
  - destruct (string_dec k (fst b)); subst.
    + left; intro G; destruct G; auto.
    + right; intro G; destruct G; auto.
Qed.

Lemma DisjKey_singleton_l {B : Type} :
  forall (a : string * B) (l : list (string * B)),
    DisjKey [a] l <-> key_not_In (fst a) l.
Proof.
  unfold DisjKey, key_not_In; split; simpl; repeat intro.
  - apply (in_map fst) in H0; simpl in *.
    specialize (H (fst a)); destruct H; auto.
  - destruct (string_dec k (fst a)); subst.
    + right; intro.
      rewrite in_map_iff in H0; dest; destruct x; simpl in *; subst.
      specialize (H b); contradiction.
    + left; intro; destruct H0; auto.
Qed.


Corollary DisjKey_singleton_r {B : Type} :
  forall (a : string * B) (l : list (string * B)),
    DisjKey l [a] <-> key_not_In (fst a) l.
Proof.
  split; intro.
  - apply DisjKey_Commutative in H; rewrite DisjKey_singleton_l in H; assumption.
  - apply DisjKey_Commutative; rewrite DisjKey_singleton_l; assumption.
Qed.

Lemma key_not_In_cons {B C : Type} :
  forall (a : B) (b : B * C) (l : list (B * C)),
    key_not_In a (b :: l) <->  a <> fst b /\ key_not_In a l.
Proof.
  split; intros; rewrite app_cons in *; [rewrite key_not_In_app_iff in H| rewrite key_not_In_app_iff]; dest; split; auto.
  - intro; destruct b; simpl in *; subst; eapply H; simpl; auto.
  - repeat intro; destruct b; simpl in *; subst; destruct H1; auto.
    apply inversionPair in H1; dest; subst; apply H; reflexivity.
Qed.

Lemma DisjKey_cons_l {B C : Type} (Heq_dec : forall (a b : B), {a = b} + {a <> b}):
  forall (b : B * C) (l1 l2 : list (B * C)),
    DisjKey (b :: l1) l2 <-> key_not_In (fst b) l2 /\ DisjKey l1 l2.
Proof.
  repeat split; intros; dest.
  - specialize (H (fst b)); destruct H; rewrite key_not_In_fst; simpl in *; auto.
  - rewrite app_cons in H.
    rewrite DisjKey_app_split_l in H; dest; auto.
  - rewrite app_cons, DisjKey_app_split_l; split; auto.
    repeat intro.
    rewrite key_not_In_fst in H.
    destruct (Heq_dec k (fst b)); subst; simpl; auto.
    left; intro; destruct H1; auto.
Qed.

Corollary DisjKey_cons_l_str {B : Type} :
  forall (b : string * B) (l1 l2 : list (string * B)),
    DisjKey (b :: l1) l2 <-> key_not_In (fst b) l2 /\ DisjKey l1 l2.
Proof. intros; apply (DisjKey_cons_l string_dec). Qed.

Corollary DisjKey_cons_r_str {B : Type} :
  forall (b : string * B) (l1 l2 : list (string * B)),
    DisjKey l1 (b :: l2) <-> key_not_In (fst b) l1 /\ DisjKey l1 l2.
Proof.
  split; intros; [ apply DisjKey_Commutative in H; rewrite DisjKey_cons_l_str in H
                 | apply DisjKey_Commutative; rewrite DisjKey_cons_l_str]
  ; dest; split; auto; apply DisjKey_Commutative; assumption.
Qed.

Lemma map_nil {B C : Type} {f : B -> C}:
  map f nil = nil.
Proof. auto. Qed.


Lemma doUpdRegs_app_r o :
  forall u o', 
    doUpdRegs u (o ++ o') = (doUpdRegs u o) ++ (doUpdRegs u o').
Proof.
  induction o; intros; simpl; auto.
  case_eq (findReg (fst a) u); intros; subst; f_equal; rewrite IHo; auto.
Qed.

Lemma findReg_Some_app u :
  forall s u' x,
    findReg s (u ++ u') = Some x ->
    findReg s u  = Some x \/ findReg s u' = Some x.
Proof.
  induction u; simpl; intros; auto.
  destruct String.eqb eqn:G; auto.
Qed.

Lemma findReg_Some_app_ordered u :
  forall s u' x y,
    findReg s (u ++ u') = Some x ->
    findReg s u = Some y ->
    x = y.
Proof.
  induction u; simpl; intros;[discriminate|].
  destruct String.eqb.
  - rewrite H in H0; inv H0; reflexivity.
  - eapply IHu; eauto.
Qed.

Lemma doUpdRegs_l_reduce o :
  forall u u',
    DisjKey u o ->
    doUpdRegs (u ++ u') o = doUpdRegs u' o.
Proof.
  induction o; simpl; auto; intros.
  destruct (findReg (fst a) (u ++ u')) eqn:G, (findReg (fst a) u') eqn:G0.
  - apply findReg_Some_app in G.
    destruct G.
    + exfalso.
      apply findRegs_Some', (in_map fst) in H0.
      specialize (H (fst a)).
      destruct H; simpl in *; auto.
    + rewrite H0 in G0; inv G0; f_equal; apply IHo.
      intro k; specialize (H k); simpl in H; destruct H; auto.
  - exfalso.
    apply findReg_Some_app in G.
    destruct G;[apply findRegs_Some', (in_map fst) in H0| rewrite H0 in G0; discriminate].
    specialize (H (fst a)).
    destruct H; simpl in *; auto.
  - exfalso.
    rewrite <- findRegs_None, map_app, in_app_iff, DeM1 in G; dest.
    apply findRegs_Some', (in_map fst) in G0; auto.
  - rewrite IHo; auto.
    intro k; specialize (H k); simpl in *; destruct H; auto.
Qed.


Lemma doUpdRegs_r_reduce o :
  forall u u',
    DisjKey u' o ->
    doUpdRegs (u ++ u') o = doUpdRegs u o.
Proof.
  induction o; simpl; auto; intros.
  destruct (findReg (fst a) (u ++ u')) eqn:G, (findReg (fst a) u) eqn:G0.
  - apply findReg_Some_app in G.
    destruct G.
    + rewrite H0 in G0; inv G0; f_equal; apply IHo.
      intro k; specialize (H k); simpl in H; destruct H; auto.
    + exfalso.
      apply findRegs_Some', (in_map fst) in H0.
      specialize (H (fst a)).
      destruct H; simpl in *; auto.
  - exfalso.
    apply findReg_Some_app in G.
    destruct G;[rewrite H0 in G0; discriminate| apply findRegs_Some', (in_map fst) in H0].
    specialize (H (fst a)).
    destruct H; simpl in *; auto.
  - exfalso.
    rewrite <- findRegs_None, map_app, in_app_iff, DeM1 in G; dest.
    apply findRegs_Some', (in_map fst) in G0; auto.
  - rewrite IHo; auto.
    intro k; specialize (H k); simpl in *; destruct H; auto.
Qed.

Lemma doUpdRegs_DisjKey o :
  forall u,
    DisjKey u o ->
    doUpdRegs u o = o.
Proof.
  induction o; simpl; auto; intros.
  destruct (findReg (fst a) u) eqn:G.
  - exfalso; apply findRegs_Some' in G.
    apply (in_map fst) in G; destruct (H (fst a)); auto.
    apply H0; simpl; auto.
  - rewrite IHo; auto.
    intro k; destruct (H k); simpl in *; auto.
Qed.

Lemma doUpdRegs_app_l o :
  forall u u',
    doUpdRegs (u ++ u') o = doUpdRegs u (doUpdRegs u' o).
Proof.
  induction o; simpl; auto; intros.
  destruct (findReg (fst a) (u ++ u')) eqn:G, (findReg (fst a) u') eqn:G0, (findReg (fst a) u) eqn:G1
  ; simpl; try (rewrite G1).
  - f_equal; auto.
    rewrite (findReg_Some_app_ordered _ _ _ G G1); reflexivity.
  - apply findReg_Some_app in G; destruct G as [G|G]; rewrite G in *;[discriminate|inv G0].
    f_equal; eauto.
  - apply findReg_Some_app in G; destruct G as [G|G]; rewrite G in *;[inv G1|discriminate].
    f_equal; eauto.
  - apply findReg_Some_app in G; rewrite G0, G1 in G; destruct G; discriminate.
  - rewrite <- findRegs_None, map_app, in_app_iff, DeM1 in G.
    apply findRegs_Some', (in_map fst) in G0; dest; contradiction.
  - rewrite <- findRegs_None, map_app, in_app_iff, DeM1 in G.
    apply findRegs_Some', (in_map fst) in G0; dest; contradiction.
  - rewrite <- findRegs_None, map_app, in_app_iff, DeM1 in G.
    apply findRegs_Some', (in_map fst) in G1; dest; contradiction.
  - f_equal; eauto.
Qed.

Lemma doUpdRegs_cons_l o :
  forall r u,
    doUpdRegs (r::u) o = doUpdRegs [r] (doUpdRegs u o).
Proof.
  intros; rewrite app_cons; apply doUpdRegs_app_l.
Qed.

Lemma doUpdReg_preserves_getKindAttr :
  forall u o,
    NoDup (map fst o) ->
    SubList (getKindAttr u) (getKindAttr o) ->
    getKindAttr (doUpdRegs u o) = getKindAttr o.
Proof.
  symmetry; erewrite getKindAttr_doUpdRegs; eauto; intros.
  apply H0; rewrite in_map_iff; eexists; split; eauto.
  simpl; reflexivity.
Qed.

Lemma doUpdRegs_preserves_keys o :
  forall u,
    map fst (doUpdRegs u o) = map fst o.
Proof.
  induction o; simpl; auto; intros.
  destruct findReg; rewrite IHo; reflexivity.
Qed.

Lemma DisjKey_rewrite_l {B C : Type} :
  forall (l1 l2 l3: list (B * C)),
    map fst l1 = map fst l2 ->
    DisjKey l1 l3 <-> DisjKey l2 l3.
Proof.
  intros; split; unfold DisjKey; repeat intro; rewrite H in *; auto.
Qed.

Lemma doUpdRegs_key_not_In a l1 :
  key_not_In (fst a) l1 ->
  doUpdRegs [a] l1 = l1.
Proof.
  intro.
  rewrite <- DisjKey_singleton_l in H.
  apply doUpdRegs_DisjKey; assumption.
Qed.

Lemma doUpdRegs_keys_neq a b :
  fst a <> fst b ->
  doUpdRegs [a] [b] = [b].
Proof.
  rewrite <- DisjKey_singletons; intros.
  apply doUpdRegs_DisjKey; assumption.
Qed.

Lemma in_cons_iff {B : Type} {a b : B} {l : list B}:
  In a (b :: l) <-> b = a \/ In a l.
Proof.
  split; intros; simpl in *; auto.
Qed.

Lemma nIn_app_iff {B : Type} (Heq_dec : forall (a b : B), {a = b} + {a <> b}) :
  forall (a : B) (l1 l2 : list B),
    ~In a (l1 ++ l2) <-> ~In a l1 /\ ~In a l2.
Proof. split; intros; rewrite in_app_iff, DeM1 in *; auto. Qed.

Lemma SubList_nil_r {B : Type} :
  forall (l : list B),
    SubList l nil -> l = nil.
Proof.
  repeat intro; induction l; auto.
  exfalso; specialize (H _ (in_eq _ _)); auto.
Qed.

Lemma SubList_filter {B : Type} :
  forall (a : B) (l1 l2 : list B),
    SubList l1 l2 ->
    ~In a l2 ->
    ~In a l1.
Proof. repeat intro; eauto. Qed.

Lemma DisjKey_filter {B C : Type} :
  forall (l1 l2 l3 l4 : list (B * C)),
    SubList (map fst l3) (map fst l1) ->
    SubList (map fst l4) (map fst l2) ->
    DisjKey l1 l2 ->
    DisjKey l3 l4.
Proof. repeat intro; firstorder fail. Qed.

Lemma DisjKey_filter_r {B C : Type} :
  forall (l1 l2 l3 : list (B * C)),
    SubList (map fst l3) (map fst l2) ->
    DisjKey l1 l2 ->
    DisjKey l1 l3.
Proof. repeat intros; firstorder fail. Qed.

Lemma DisjKey_filter_l {B C : Type} :
  forall (l1 l2 l3 : list (B * C)),
    SubList (map fst l3) (map fst l2) ->
    DisjKey l2 l1 ->
    DisjKey l3 l1.
Proof. repeat intros; firstorder fail. Qed.

Lemma doUpdRegs_cons_r' :
  forall (u o : RegsT) (r : RegT),
    doUpdRegs u (r :: o) = doUpdReg u r :: doUpdRegs u o.
Proof. intros; simpl; auto. Qed.

Lemma oneUpdRegs_doUpdRegs :
  forall (o : RegsT) (r : RegT),
    doUpdRegs [r] o = oneUpdRegs r o.
Proof.
  induction o; intros; auto.
  simpl; destruct String.eqb eqn:G; f_equal; eauto.
  rewrite String.eqb_eq in G; rewrite G; destruct r; reflexivity.
Qed.


Lemma doUpdRegs_cons_l' :
  forall (u o : RegsT) (r : RegT),
    doUpdRegs (r :: u) o = oneUpdRegs r (doUpdRegs u o).
Proof.
  intros.
  rewrite <- oneUpdRegs_doUpdRegs, doUpdRegs_cons_l; reflexivity.
Qed.

Lemma doUpdReg_oneUpdReg :
  forall (r1 r2 : RegT),
    oneUpdReg r1 r2 = doUpdReg [r1] r2.
Proof.
  intros; unfold oneUpdReg, doUpdReg, findReg.
  destruct String.eqb eqn:G; auto.
  rewrite String.eqb_eq in G; rewrite G; destruct r1; reflexivity.
Qed.

Lemma oneUpdRegs_cons :
  forall (o : RegsT) (r1 r2 : RegT),
    oneUpdRegs r1 (r2 :: o) = oneUpdReg r1 r2 :: oneUpdRegs r1 o.
Proof.
  intros; rewrite <- oneUpdRegs_doUpdRegs, doUpdRegs_cons_r', <- doUpdReg_oneUpdReg.
  f_equal; apply oneUpdRegs_doUpdRegs.
Qed.

Lemma oneUpdRegs_app :
  forall (o1 o2 : RegsT) (r : RegT),
    oneUpdRegs r (o1 ++ o2) = oneUpdRegs r o1 ++ oneUpdRegs r o2.
Proof.
  intros; repeat rewrite <- oneUpdRegs_doUpdRegs; rewrite doUpdRegs_app_r; reflexivity.
Qed.

Lemma doUpdReg_doUpdRegs :
  forall (u : RegsT) (r : RegT),
    doUpdRegs u [r] = [doUpdReg u r].
Proof. auto. Qed.

Lemma doUpdReg_app :
  forall (u1 u2 : RegsT) (r : RegT),
    doUpdReg (u1 ++ u2) r = doUpdReg u1 (doUpdReg u2 r).
Proof.
  intros.
  enough ([doUpdReg (u1 ++ u2) r] = [doUpdReg u1 (doUpdReg u2 r)]) as P.
  { inv P; reflexivity. }
  repeat rewrite <- doUpdReg_doUpdRegs; rewrite doUpdRegs_app_l; reflexivity.
Qed.

Lemma doUpdReg_cons :
  forall (u : RegsT) (r1 r2 : RegT),
    doUpdReg (r1 :: u) r2 = oneUpdReg r1 (doUpdReg u r2).
Proof.
  intros.
  enough ([doUpdReg (r1 :: u) r2] = [oneUpdReg r1 (doUpdReg u r2)]) as P.
  { inv P; reflexivity. }
  rewrite <- doUpdReg_doUpdRegs, doUpdRegs_cons_l, doUpdReg_doUpdRegs, oneUpdRegs_doUpdRegs.
  reflexivity.
Qed.

Lemma doUpdReg_notIn :
  forall  (u : RegsT) (r : RegT),
    ~ In (fst r) (map fst u) ->
    doUpdReg u r = r.
Proof.
  induction u; intros; auto.
  unfold doUpdReg; destruct findReg eqn:G; auto.
  exfalso; apply findRegs_Some', (in_map fst) in G; apply H; assumption.
Qed.

Corollary doUpdReg_nil :
  forall (r : RegT),
    doUpdReg nil r = r.
Proof. eauto using in_nil, doUpdReg_notIn. Qed.

Lemma oneUpdRegs_notIn :
  forall (u : RegsT) (r : RegT),
    ~ In (fst r) (map fst u) ->
    oneUpdRegs r u = u.
Proof.
  induction u; intros; auto.
  simpl; destruct String.eqb eqn:G.
  - rewrite String.eqb_eq in G; simpl in H; subst.
    exfalso; apply H; auto.
  - f_equal; apply IHu; intro; apply H; simpl; auto.
Qed.

Lemma DisjKey_rewrite_r {B C : Type}:
  forall (l1 l2 l3 : list (B * C)),
    map fst l1 = map fst l2 ->
    DisjKey l3 l1 <->
    DisjKey l3 l2.
Proof.
  split; intros; apply DisjKey_Commutative.
  - rewrite DisjKey_rewrite_l; [apply (DisjKey_Commutative H0)| apply eq_sym, H].
  - rewrite DisjKey_rewrite_l; [apply (DisjKey_Commutative H0)| apply H].
Qed.

Lemma BreakGKAEvar1 {B C : Type} {P : C -> Type} (l1 : list (B * {x : C & P x})) x l2 :
  forall a b l3 p,
    l1 = (a, (existT _ b p)) :: l3 ->
    (a, b) = x ->
    getKindAttr l3 = l2 ->
    getKindAttr l1 = x :: l2.
Proof. intros; subst; simpl; f_equal. Qed.

Lemma BreakGKAEvar2 {B C : Type} {f : B -> C} l1 l2 l3 :
  forall l4 l5,
    l1 = l4 ++ l5 ->
    map f l4 = l2 ->
    map f l5 = l3 ->
    map f l1 = l2 ++ l3.
Proof. intros; subst; rewrite map_app; reflexivity. Qed.

Lemma doUpdReg_preserves_keys :
  forall (u : RegsT) (r : RegT),
    fst (doUpdReg u r) = fst r.
Proof.
  induction u; intros; eauto using doUpdReg_nil.
  unfold doUpdReg; simpl; destruct String.eqb; auto; apply IHu.
Qed.

Lemma SubList_cons_l_iff {B : Type}:
  forall (a : B) (l1 l2 : list B),
    SubList (a :: l1) l2 <->
    In a l2 /\ SubList l1 l2.
Proof.
  split; intros; rewrite app_cons, SubList_app_l_iff in *; split; try firstorder fail.
  repeat intro; inv H0; dest; auto.
  inv H1.
Qed.

Lemma SubList_nil_l {B : Type} :
  forall (l : list B),
    SubList nil l.
Proof. repeat intro; inv H. Qed.

Lemma gatherAction_invar {B: Type} {k_in k_out} (f : B -> ActionT type k_in)
      myReg (cont : ActionT type k_out):
  ActionWb myReg cont ->
  (forall (b : B),
      ActionWb myReg (f b)) ->
  forall (l : list B),
    ActionWb myReg (gatherActions (map f l) (fun val => cont)).
Proof.
  induction l; simpl; intros; auto.
  unfold ActionWb; intros.
  apply inversionSemAction' in H3; dest; subst.
  specialize (H0 _ _ _ _ _ _ H1 H2 H4).
  specialize (IHl _ _ _ _ _ H1 H2 H5); dest.
  rewrite <- H10 in H13.
  specialize (SubList_chain H1 H6 H0 (getKindAttr_fst _ _ (eq_sym H13))) as P; subst.
  split.
  - eexists; repeat split; eauto.
    + rewrite SubList_app_l_iff; split; auto.
    + econstructor; eauto.
  - rewrite map_app, SubList_app_l_iff; split; auto.
Qed.

Lemma ActionWbExpand :
  forall k (a : ActionT type k) myRegs1 myRegs2,
    SubList myRegs1 myRegs2 ->
    ActionWb myRegs1 a ->
    ActionWb myRegs2 a.
Proof.
  unfold ActionWb; intros.
  specialize (H0 _ _ _ _ _ H1 (SubList_transitive H H2) H3); dest.
  rewrite SubList_map_iff in H2; dest.
  assert (SubList x x0).
  { rewrite <- H8, <- H6 in H.
    repeat intro.
    specialize (H0 _ H9).
    specialize (in_map fst _ _ H9) as P.
    apply (SubList_map fst) in H; repeat rewrite fst_getKindAttr in H.
    specialize (H _ P).
    rewrite in_map_iff in H; dest.
    specialize (H2 _ H10).
    rewrite (KeyMatching3 _ _ _ H1 H0 H2 (eq_sym H)).
    assumption.
  }
  split.
  - exists x0; repeat split; auto.
    + apply (SubList_transitive H5 H9).
    + eapply SemActionExpand; [apply H9| assumption].
  - apply (SubList_transitive H4 H).
Qed.

Lemma RetvWb :
  ActionWb nil Retv%kami_action.
Proof.
  unfold ActionWb; intros.
  apply inversionSemAction' in H1; dest; subst.
  split; [eexists; repeat split; auto; try instantiate (1 := nil) |]; eauto using SubList_nil_l.
  constructor; auto.
Qed.

Lemma SemActionSub :
  forall o k (a : ActionT type k) reads upds calls ret,
    SemAction o a reads upds calls ret
    -> SubList reads o /\ SubList (getKindAttr upds) (getKindAttr o).
Proof. intros; eauto using SemActionReadsSub, SemActionUpdSub. Qed.

Lemma doUpdRegs_idemp o :
  NoDup (map fst o) ->
  doUpdRegs o o = o.
Proof.
  induction o; auto; intros.
  inv H; destruct a; simpl.
  rewrite String.eqb_refl, doUpdRegs_cons_l, doUpdRegs_key_not_In, IHo; auto.
  rewrite IHo; auto.
  repeat intro; apply H2.
  rewrite in_map_iff.
  exists (s, v); auto.
Qed.

Lemma doUpdRegs_idemp' o o' :
  o = o' ->
  NoDup (map fst o) ->
  doUpdRegs o o' = o'.
Proof.
  intros; subst; apply doUpdRegs_idemp; auto.
Qed.

