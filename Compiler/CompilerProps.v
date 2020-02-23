Require Import Kami.StateMonad Kami.Syntax Kami.Properties Kami.PProperties Kami.PPlusProperties Kami.Lib.EclecticLib Kami.Notations Kami.Compiler.Compiler.
Import Word.Notations.

Require Import ZArith.

Set Implicit Arguments.
Set Asymmetric Patterns.

Local Coercion BaseRegFile : RegFileBase >-> BaseModule.
(* Section Defs *)

Definition inline_Meths (l : list DefMethT) (xs : list nat) (meth : DefMethT) : DefMethT :=
  let (name, sig_body) := meth in
  (name,
   let (sig, body) := sig_body in
   existT _ sig (fun ty arg => fold_left (inlineSingle_pos l) xs (body ty arg))).

Definition inlineSingle_Meth_pos (l : list DefMethT) (meth : DefMethT) (n : nat) : DefMethT :=
  match nth_error l n with
  | Some f => inlineSingle_Meth f meth
  | None => meth
  end.

Definition inline_Rules (l : list DefMethT) (xs : list nat) (rule : RuleT) : RuleT :=
  let (s, a) := rule in
  (s, fun ty => fold_left (inlineSingle_pos l) xs (a ty)).

Definition listRfMethods (lrf : list RegFileBase) : (list DefMethT) :=
  (concat (map (fun rf => getRegFileMethods rf) lrf)).

Definition inlineRf_Rules_Flat (lrf : list RegFileBase) (l : list RuleT) :=
  map (inline_Rules (listRfMethods lrf) (seq 0 (length (listRfMethods lrf)))) l.

Definition inlineRf_Meths_Flat (lrf : list RegFileBase) (l : list DefMethT) :=
  map (inline_Meths (listRfMethods lrf) (seq 0 (length (listRfMethods lrf)))) l.

Definition flatInlineSingleRfNSC (m : BaseModule) (lrf : list RegFileBase) :=
  BaseMod (getRegisters m  ++ (concat (map (fun rf => getRegFileRegisters rf) lrf)))
          (inlineRf_Rules_Flat lrf (getRules m))
          ((inlineRf_Meths_Flat lrf (getMethods m)) ++ (concat (map (fun rf => getRegFileMethods rf) lrf))).

Definition inlineSingle_Rule_pos (meths : list DefMethT) n (rule : RuleT) :=
  match nth_error meths n with
  | Some f => (inlineSingle_Rule f rule)
  | None => rule
  end.

Definition inlineSingle_Meths_posmap (meths : list DefMethT) (currMap : DefMethT -> DefMethT) (n : nat) :=
  match nth_error meths n with
  | Some f => (fun x => inlineSingle_Meth (currMap f) (currMap x))
  | None => currMap
  end.

Definition inlineAll_Rules_map (meths : list DefMethT) (rules : list RuleT) :=
  map (fold_left (fun rle n => inlineSingle_Rule_pos meths n rle) (seq 0 (length meths))) rules.

Fixpoint subseq_list {A : Type} (l : list A) (xs : list nat) :=
  match xs with
  | n::xs' => match nth_error l n with
              | Some d => d :: (subseq_list l xs')
              | None => (subseq_list l xs')
              end
  | nil => nil
  end.

Definition mergeSeparatedSingle (b : BaseModule) (lrf : list RegFileBase) : Mod :=
  ConcatMod (Base b) (mergeSeparatedBaseFile lrf).


(* End Defs *)

(* begin misc properties *)


Lemma WfBaseMod_inlineSingle_map (m : BaseModule) (HWfMod : WfBaseModule m) k (a : ActionT type k) (n : nat):
  forall  (lf : list DefMethT),
    SubList lf (getMethods m) ->
    WfActionT (getRegisters m) a ->
    WfActionT (getRegisters m) (apply_nth (map (fun f a' => @inlineSingle type k a' f) lf) a n).
Proof.
  intros.
  unfold apply_nth; remember (nth_error _ _) as err0; symmetry in Heqerr0; destruct err0; auto.
  apply nth_error_In in Heqerr0; rewrite in_map_iff in Heqerr0; dest.
  rewrite <- H1.
  apply WfBaseMod_inlineSingle; auto.
Qed.

Lemma WfBaseMod_inlineSome_map (m : BaseModule) (HWfMod : WfBaseModule m) xs:
  forall  (lf : list DefMethT) k (a : ActionT type k),
    SubList lf (getMethods m) ->
    WfActionT (getRegisters m) a ->
    WfActionT (getRegisters m) (fold_left (apply_nth (map (fun f a' => @inlineSingle type k a' f) lf)) xs a).
Proof.
  induction xs; simpl; intros; eauto.
  apply IHxs; auto.
  apply WfBaseMod_inlineSingle_map; assumption.
Qed.


Lemma subseq_list_app {A : Type} (l : list A) (xs1 xs2 : list nat):
  subseq_list l (xs1 ++ xs2) = subseq_list l xs1 ++ subseq_list l xs2.
Proof.
  induction xs1; simpl; auto.
  remember (nth_error _ _) as err0; symmetry in Heqerr0; destruct err0; auto.
  rewrite <-app_comm_cons, IHxs1; reflexivity.
Qed.

Lemma subseq_list_shift {A : Type} (xs : list nat) :
  forall (l1 l2 : list A),
    (forall n, In n xs -> length l1 <= n) ->
    subseq_list (l1 ++ l2) xs = subseq_list l2 (map (fun x => x - (length l1)) xs).
Proof.
  induction xs; simpl; auto; intros.
  remember (nth_error _ _ ) as err0.
  remember (nth_error l2 _ ) as err1.
  symmetry in Heqerr0, Heqerr1; destruct err0; rewrite nth_error_app2, Heqerr1 in Heqerr0;
    auto; rewrite Heqerr0; auto.
  apply f_equal; auto.
Qed.

Lemma subseq_list_all {A : Type} (l : list A) :
  subseq_list l (seq 0 (length l)) = l.
Proof.
  induction l; auto.
  simpl; apply f_equal.
  rewrite <- IHl at 3.
  assert (a :: l = [a] ++ l) as P0; auto; rewrite P0.
  rewrite subseq_list_shift.
  - rewrite Reduce_seq; auto.
  - intros; rewrite in_seq in *; dest; auto.
Qed.

Lemma existsb_nexists_sync sync l :
  existsb (SyncRead_eqb sync) l = false <->
  ~ In sync l.
Proof.
  split; repeat intro.
  - assert (exists x, In x l /\ (SyncRead_eqb sync) x = true) as P0.
    { exists sync; split; auto. unfold SyncRead_eqb; repeat rewrite String.eqb_refl; auto. }
    rewrite <- existsb_exists in P0; rewrite P0 in *; discriminate.
  - remember (existsb _ _) as exb; symmetry in Heqexb; destruct exb; auto.
    exfalso; rewrite existsb_exists in Heqexb; dest.
    rewrite SyncRead_eqb_eq in *; subst; auto.
Qed.

(* end misc properties *)

Lemma inline_Rules_eq_inlineSome (xs : list nat) :
  forall (meths : list DefMethT) (rules : list RuleT),
    fold_left (fun newRules n => inlineSingle_Rules_pos meths n newRules) xs rules
    = map (inline_Rules meths xs) rules.
Proof.
  induction xs; unfold inline_Rules; simpl; intros.
  - induction rules; simpl; auto.
    apply f_equal2; auto.
    destruct a; apply f_equal.
    eexists.
  - rewrite IHxs.
    clear; induction rules; simpl.
    + unfold inlineSingle_Rules_pos; destruct nth_error; auto.
    + rewrite <- IHrules. 
      unfold inlineSingle_Rules_pos.
      remember (nth_error meths a) as nth_err.
      destruct nth_err; simpl.
      * apply f_equal2; auto.
        unfold inlineSingle_pos, inline_Rules, inlineSingle_Rule;
          rewrite <- Heqnth_err; simpl.
        destruct a0; simpl.
        apply f_equal.
        eexists.
      * unfold inline_Rules; destruct a0.
        apply f_equal2; auto; apply f_equal.
        unfold inlineSingle_pos at 3; rewrite <- Heqnth_err.
        reflexivity.
Qed.

Corollary inlineAll_Rules_in (lm : list DefMethT) :
  forall lr,
    inlineAll_Rules lm lr = map (inline_Rules lm (seq 0 (length lm))) lr.
Proof.
  unfold inlineAll_Rules; intros; rewrite inline_Rules_eq_inlineSome; reflexivity.
Qed.

Lemma inlineSingle_map meths:
  forall n,
    inlineSingle_Meths_pos meths n = map (inlineSingle_Meths_posmap meths (fun x => x) n) meths.
Proof.
  intros.
  unfold inlineSingle_Meths_pos, inlineSingle_Meths_posmap; destruct nth_error;[|rewrite map_id]; auto.
Qed.

Lemma inlineSome_map xs :
  forall meths,
    fold_left inlineSingle_Meths_pos xs meths = map (fold_left (inlineSingle_Meths_posmap meths) xs (fun x => x)) meths.
Proof.
  induction xs; simpl; intros;[rewrite map_id; reflexivity|].
  rewrite inlineSingle_map.
  unfold inlineSingle_Meths_posmap at 1 3; destruct nth_error.
  - rewrite IHxs.
    rewrite map_map, forall_map; intros.
    repeat rewrite <- fold_left_rev_right.
    clear.
    revert x; induction (rev xs); simpl; auto; intros.
    unfold inlineSingle_Meths_posmap at 1 3.
    remember (nth_error _ _) as nth_err0.
    remember (nth_error meths a) as nth_err1.
    destruct nth_err0, nth_err1; auto.
    + symmetry in Heqnth_err1.
      apply (map_nth_error (fun x => inlineSingle_Meth d x)) in Heqnth_err1.
      rewrite Heqnth_err1 in Heqnth_err0; inv Heqnth_err0.
      rewrite IHl; simpl.
      apply f_equal2; auto.
    + exfalso.
      specialize (nth_error_map (fun x : DefMethT => inlineSingle_Meth d x) (fun x => False) a meths) as P0.
      rewrite <- Heqnth_err0, <- Heqnth_err1 in P0; rewrite P0; auto.
    + exfalso.
      specialize (nth_error_map (fun x : DefMethT => inlineSingle_Meth d x) (fun x => False) a meths) as P0.
      rewrite <- Heqnth_err0, <- Heqnth_err1 in P0; rewrite <- P0; auto.
  - rewrite map_id; apply IHxs.
Qed.

Lemma inlineAll_Rules_in' (lm : list DefMethT) :
  forall lr,
    inlineAll_Rules lm lr = inlineAll_Rules_map lm lr.
Proof.
  unfold inlineAll_Rules, inlineAll_Rules_map.
  induction (seq 0 (length lm)); simpl; intros.
  - rewrite map_id; reflexivity.
  - rewrite IHl.
    clear; induction lr; simpl.
    + unfold inlineSingle_Rules_pos; destruct nth_error; simpl; auto.
    + unfold inlineSingle_Rules_pos, inlineSingle_Rule_pos at 3.
      remember (nth_error lm a) as nth_err.
      destruct nth_err; simpl; apply f_equal; rewrite <- IHlr;
        unfold inlineSingle_Rules_pos; rewrite <- Heqnth_err; reflexivity.
Qed.

Lemma NeverCall_inlineSingle_pos ty k (a : ActionT ty k) :
  forall (l : list DefMethT) (n : nat) (f : DefMethT)
         (HNeverCall : forall meth ty,
             In meth l ->
             forall arg, NeverCallActionT (projT2 (snd meth) ty arg)),
    nth_error l n = Some f ->
    NoCallActionT [f] (inlineSingle_pos l a n).
Proof.
  unfold inlineSingle_pos; intros.
  remember (nth_error _ _) as nth_err0; symmetry in Heqnth_err0; destruct nth_err0; auto; inv H.
  apply NeverCall_inline; eauto using nth_error_In.
Qed.

Lemma NeverCall_inlineSingle_pos_persistent k ty (a : ActionT ty k) :
  forall (l ls : list DefMethT) (n : nat)
         (HNeverCall : forall meth ty,
             In meth l ->
             forall arg, NeverCallActionT (projT2 (snd meth) ty arg)),
    NoCallActionT ls a ->
    NoCallActionT ls (inlineSingle_pos l a n).
Proof.
  unfold inlineSingle_pos; intros.
  destruct (nth_error _ _) eqn:err0; auto.
  apply NeverCall_inline_persistent; eauto using nth_error_In.
Qed.

Lemma NeverCall_inlineSome_pos_persistent xs:
  forall ty k (a : ActionT ty k)
         (l ls : list DefMethT)
         (HNeverCall : forall meth ty,
             In meth l ->
             forall arg, NeverCallActionT (projT2 (snd meth) ty arg)),
    NoCallActionT ls a ->
    NoCallActionT ls (fold_left (inlineSingle_pos l) xs a).
Proof.
  induction xs; intros; simpl in *; auto.
  eapply IHxs; eauto using NeverCall_inlineSingle_pos_persistent.
Qed.

Lemma NeverCall_inlineSome_pos xs:
  forall ty k (a : ActionT ty k)
         (l : list DefMethT)
         (HNeverCall : forall meth ty,
             In meth l ->
             forall arg, NeverCallActionT (projT2 (snd meth) ty arg)),
    (forall f, In f (subseq_list l xs) ->
               NoCallActionT [f] (fold_left (inlineSingle_pos l) xs a)).
Proof.
  induction xs; simpl; intros; auto;[contradiction|].
  destruct (nth_error _ _) eqn:G; auto.
  inv H; auto.
  eapply NeverCall_inlineSome_pos_persistent; eauto using NeverCall_inlineSingle_pos.
Qed.

Lemma NeverCall_inlineSome_pos_full xs :
  forall ty k (a : ActionT ty k)
         (l : list DefMethT)
         (HNeverCall : forall meth ty,
             In meth l ->
             forall arg, NeverCallActionT (projT2 (snd meth) ty arg)),
    NoCallActionT (subseq_list l xs) (fold_left (inlineSingle_pos l) xs a).
Proof.
  induction xs; eauto using NilNoCall; intros.
  simpl; unfold inlineSingle_pos at 2.
  destruct (nth_error _ _) eqn:G; eauto.
  assert (d::subseq_list l xs = [d] ++ subseq_list l xs) as TMP; auto; rewrite TMP; clear TMP.
  apply NoCallActionT_Stitch; auto.
  apply NeverCall_inlineSome_pos_persistent; auto.
  apply  NeverCall_inline; eauto using nth_error_In.
Qed.

Lemma NoSelfCall_ignorable k (a : ActionT type k) :
  forall (l1 l2 : list DefMethT) (n : nat),
    n < length l1 ->
    NoCallActionT l1 a ->
    inlineSingle_pos (inlineAll_Meths (l1 ++ l2)) a n = a.
Proof.
  unfold inlineSingle_pos; intros;
    remember (nth_error (inlineAll_Meths (l1 ++ l2)) n) as nth_err0; destruct nth_err0; auto.
  eapply NotCalled_NotInlined; eauto.
  symmetry in Heqnth_err0.
  apply (map_nth_error (fun x => (fst x, projT1 (snd x)))) in Heqnth_err0.
  rewrite <- SameKindAttrs_inlineAll_Meths, map_app, nth_error_app1 in Heqnth_err0.
  + apply (nth_error_In _ _ Heqnth_err0).
  + rewrite map_length; assumption.
Qed.

Lemma SemRegExprVals expr :
  forall o1 o2,
    SemRegMapExpr expr o1 ->
    SemRegMapExpr expr o2 ->
    o1 = o2.
Proof.
  induction expr; intros; inv H; inv H0; EqDep_subst; auto;
    try congruence; specialize (IHexpr _ _ HSemRegMap HSemRegMap0); inv IHexpr; auto.
Qed.

Lemma UpdRegs_same_nil o :
  UpdRegs (nil::nil) o o.
Proof.
  unfold UpdRegs.
  repeat split; auto.
  intros.
  right; unfold not; split; intros; dest; auto.
  destruct H0; subst; auto.
Qed.

Lemma PriorityUpds_Equiv old upds new
      (HNoDupOld : NoDup (map fst old))
      (HNoDupUpds : forall u, In u upds -> NoDup (map fst u)) :
  PriorityUpds old upds new ->
  forall new',
    PriorityUpds old upds new' ->
    SubList new new'.
Proof.
  induction 1; intros.
  - inv H.
    + apply SubList_refl.
    + discriminate.
  - subst.
    inv H0; inv HFullU.
    repeat intro.
    destruct x.
    specialize (Hcurr _ _ H0).
    specialize (getKindAttr_map_fst _ _ currRegsTCurr0) as P0.
    specialize (getKindAttr_map_fst _ _ currRegsTCurr) as P1.
    assert (In s (map fst new')).
    { rewrite <- P0, P1, in_map_iff. exists (s, s0); split; auto. }
    rewrite in_map_iff in H1; dest.
    destruct x; simpl in *; subst.
    specialize (Hcurr0 _ _ H2).
    specialize (HNoDupUpds _ (or_introl _ (eq_refl))) as P3.
    destruct Hcurr, Hcurr0; dest.
    + rewrite <-(KeyMatching3 _ _ _ P3 H3 H1 eq_refl).
      assumption.
    + exfalso; apply H3.
      rewrite in_map_iff.
      exists (s, s0); split; auto.
    + exfalso; apply H1.
      rewrite in_map_iff.
      exists (s, s2); split; auto.
    + assert (forall u,  In u prevUpds0 -> NoDup (map fst u)) as P4; eauto.
      specialize (IHPriorityUpds P4 _ prevCorrect _ H5).
      rewrite (getKindAttr_map_fst _ _ (prevPrevRegsTrue prevCorrect)) in HNoDupOld.
      rewrite (KeyMatching3 _ _ _ HNoDupOld H4 IHPriorityUpds eq_refl) in *.
      assumption.
Qed.


Lemma PriorityUpdsCompact upds:
  forall old new,
    PriorityUpds old upds new -> PriorityUpds old (nil::upds) new.
Proof.
  induction upds.
  - econstructor 2 with (u := nil) (prevUpds := nil); eauto; repeat constructor.
    inv H; eauto.
  - intros.
    econstructor 2 with (u := nil) (prevUpds := a :: upds); eauto.
    inv H; auto.
Qed.

Lemma CompactPriorityUpds upds:
  forall old,
    NoDup (map fst old) ->
    forall new, 
      PriorityUpds old (nil::upds) new -> PriorityUpds old upds new.
Proof.
  induction upds; intros.
  - enough (old = new).
    { subst; constructor. }
    inv H0; inv HFullU; inv prevCorrect;[|discriminate]; simpl in *.
    apply getKindAttr_map_fst in currRegsTCurr.
    assert (forall s v, In (s, v) new -> In (s, v) prevRegs).
    { intros.
      destruct (Hcurr _ _ H0);[contradiction|dest]; auto.
    }
    symmetry.
    apply KeyMatch; auto.
    rewrite currRegsTCurr in H; assumption.
  - inv H0; inv HFullU.
    enough ( new = prevRegs).
    { rewrite H0; auto. }
    apply getKindAttr_map_fst in currRegsTCurr.
    specialize (getKindAttr_map_fst _ _ (prevPrevRegsTrue prevCorrect)) as P0.
    rewrite currRegsTCurr in H.
    eapply KeyMatch; eauto.
    + rewrite <- currRegsTCurr; assumption.
    + intros.
      destruct (Hcurr _ _ H0);[contradiction| dest; auto].
Qed.

Lemma CompactPriorityUpds_iff {old} (NoDupsOld : NoDup (map fst old)) upds new:
  PriorityUpds old (nil::upds) new <-> PriorityUpds old upds new.
Proof.
  split; eauto using CompactPriorityUpds, PriorityUpdsCompact.
Qed.

Lemma inline_Meths_eq_inlineSome (xs : list nat) :
  forall (l l' : list DefMethT)
         (HDisjMeths : DisjKey l l'),
    fold_left (inlineSingle_Flat_pos l') xs l = map (inline_Meths l' xs) l.
Proof.
  induction xs; simpl; intros.
  - unfold inline_Meths; induction l; simpl in *; auto.
    rewrite <-IHl.
    + destruct a, s0, x; simpl.
      reflexivity.
    + intro k; specialize (HDisjMeths k); simpl in *; firstorder fail.
  - rewrite IHxs.
    + unfold inlineSingle_Flat_pos.
      remember (nth_error l' a) as nth_err.
      destruct nth_err.
      * unfold inline_Meths at 2; simpl.
        unfold inlineSingle_pos at 2.
        rewrite <- Heqnth_err.
        induction l; simpl; auto.
        rewrite <- IHl.
        -- apply f_equal2; auto.
           unfold inline_Meths, inlineSingle_Meth.
           destruct a0, s0.
           remember (String.eqb _ _ ) as strd; symmetry in Heqstrd.
           destruct strd; auto; rewrite String.eqb_eq in *.
           exfalso.
           specialize (nth_error_In _ _ (eq_sym Heqnth_err)) as P0.
           destruct d; subst.
           apply (in_map fst) in P0.
           clear - HDisjMeths P0.
           destruct (HDisjMeths s0); auto; apply H; left; reflexivity.
        -- clear - HDisjMeths.
           intro k; specialize (HDisjMeths k); simpl in *; firstorder fail.
      * unfold inline_Meths at 2; simpl.
        unfold inlineSingle_pos at 2.
        rewrite <- Heqnth_err.
        fold (inline_Meths l' xs).
        reflexivity.
    + clear - HDisjMeths.
      intro k; specialize (HDisjMeths k).
      enough (map fst (inlineSingle_Flat_pos l' l a) = (map fst l)).
      { rewrite H; auto. }
      unfold inlineSingle_Flat_pos.
      destruct nth_error; auto.
      apply inline_preserves_keys_Meth.
Qed.

Lemma getFromEach_getMethods (rf : RegFileBase) :
  getMethods rf = getEachRfMethod rf.
Proof.
  unfold getEachRfMethod; destruct rf; simpl.
  destruct rfRead; simpl; auto.
  unfold readSyncRegFile, getSyncReq, getSyncRes; simpl.
  destruct isAddr; auto.
Qed.

Lemma inlineSingle_Flat_pos_lengths :
  forall xs ls ls',
    length (fold_left (inlineSingle_Flat_pos ls') xs ls) = length ls.
Proof.
  induction xs; simpl; auto; intros.
  rewrite IHxs.
  unfold inlineSingle_Flat_pos.
  destruct nth_error; auto.
  rewrite map_length.
  reflexivity.
Qed.

Lemma inlineAll_Meths_RegFile_fold_flat2 n :
  forall (l l' : list DefMethT)
         (HNeverCall : forall meth ty,
             In meth l' ->
             (forall arg, NeverCallActionT (projT2 (snd meth) ty arg)))
         (Hlen : 0 < n - length l),
    fold_left inlineSingle_Meths_pos (seq (length l) (n - (length l))) (l ++ l')
    = fold_left (inlineSingle_Flat_pos l') (seq 0 (n - length l)) l ++ l'.
Proof.
  intros; induction n.
  - simpl; auto.
  - assert (length l <= n) as TMP.
    { lia. }
    rewrite Nat.sub_succ_l in *; auto.
    + apply lt_n_Sm_le in Hlen.
      destruct (le_lt_or_eq _ _ Hlen).
      * repeat rewrite seq_eq.
        repeat rewrite fold_left_app; simpl.
        rewrite IHn; [rewrite <- le_plus_minus; [|lia]|]; auto.
        remember (nth_error l' (n - length l)) as nth_err.
        destruct nth_err.
        -- symmetry in Heqnth_err.
           assert (length l <= n) as P1.
           { lia. }
           rewrite <-(inlineSingle_Flat_pos_lengths (seq 0 (n - Datatypes.length l)) l l') in Heqnth_err, P1.
           erewrite inlineAll_Meths_RegFile_flat2; eauto.
           unfold inlineSingle_Flat_pos at 2.
           rewrite inlineSingle_Flat_pos_lengths in Heqnth_err.
           rewrite Heqnth_err.
           reflexivity.
        -- unfold inlineSingle_Meths_pos.
           remember (nth_error (fold_left (inlineSingle_Flat_pos l') (seq 0 (n - Datatypes.length l)) l ++ l') n) as nth_err2.
           destruct nth_err2.
           ++ exfalso.
              assert (nth_error (fold_left (inlineSingle_Flat_pos l') (seq 0 (n - Datatypes.length l)) l ++ l') n <> None) as P1.
              { rewrite <- Heqnth_err2; intro; discriminate. }
              rewrite nth_error_Some in P1.
              rewrite app_length, inlineSingle_Flat_pos_lengths in P1.
              symmetry in Heqnth_err.
              rewrite nth_error_None in Heqnth_err.
              lia.
           ++ unfold inlineSingle_Flat_pos.
              rewrite <- Heqnth_err; reflexivity.
      * rewrite <- H; simpl.
        assert (n = length l) as P0.
        { lia. }
        rewrite  P0 in *; clear TMP.
        remember (nth_error l' (length l - length l)) as nth_err.
        destruct nth_err.
        -- symmetry in Heqnth_err.
           erewrite inlineAll_Meths_RegFile_flat2; eauto.
           unfold inlineSingle_Flat_pos.
           remember (nth_error l' 0) as nth_err2.
           destruct nth_err2.
           ++ rewrite Nat.sub_diag in Heqnth_err.
              rewrite Heqnth_err in *.
              inv Heqnth_err2.
              reflexivity.
           ++ rewrite Nat.sub_diag in Heqnth_err.
              rewrite Heqnth_err in *.
              inv Heqnth_err2.
        -- unfold inlineSingle_Meths_pos.
           remember (nth_error (l ++ l') (Datatypes.length l)) as nth_err2.
           destruct nth_err2.
           ++ exfalso.
              assert (nth_error (l ++ l') (length l) <> None).
              { rewrite <- Heqnth_err2; intro; inv H0. }
              rewrite nth_error_Some in H0.
              symmetry in Heqnth_err.
              rewrite nth_error_None in Heqnth_err.
              rewrite app_length in H0.
              rewrite Nat.sub_diag in Heqnth_err.
              lia.
           ++ unfold inlineSingle_Flat_pos.
              rewrite Nat.sub_diag in Heqnth_err.
              rewrite <- Heqnth_err.
              reflexivity.
Qed.

Lemma inlineAll_Meths_RegFile_fold_flat :
  forall (l l' : list DefMethT)
         (HNeverCall : forall meth ty,
             In meth l' ->
             (forall arg, NeverCallActionT (projT2 (snd meth) ty arg))),
    fold_left inlineSingle_Meths_pos (seq 0 (length (l ++ l'))) (l ++ l')
    = fold_left (inlineSingle_Flat_pos l') (seq 0 (length l'))
                (fold_left inlineSingle_Meths_pos (seq 0 (length l)) l) ++ l'.
Proof.
  intros.
  specialize (Nat.le_add_r (length l) (length l')) as P0.
  rewrite app_length, (seq_app' _ P0), fold_left_app, Nat.add_0_l.
  rewrite inlineAll_Meths_RegFile_fold_flat1; auto.
  destruct (zerop (length l')).
  - rewrite e; rewrite minus_plus; simpl.
    rewrite length_zero_iff_nil in e; rewrite e, app_nil_r; reflexivity.
  - assert (0 < (length l + length l') - length l).
    { rewrite minus_plus; assumption. }
    rewrite <- (inlineSome_Meths_pos_length l (seq 0 (Datatypes.length l))) at 1 2 3.
    rewrite <- (inlineSome_Meths_pos_length l (seq 0 (Datatypes.length l))) in H.
    rewrite inlineAll_Meths_RegFile_fold_flat2; auto.
    rewrite (inlineSome_Meths_pos_length l (seq 0 (Datatypes.length l))) in *.
    rewrite minus_plus.
    rewrite <- (inlineSome_Meths_pos_length l (seq 0 (Datatypes.length l)) ).
    reflexivity.
Qed.

Lemma inlineSingle_pos_NeverCall k ty (a : ActionT ty k) n:
  forall (l : list DefMethT) (ls : list DefMethT),
    (forall meth ty,
        In meth l ->
        (forall arg, NeverCallActionT (projT2 (snd meth) ty arg))) ->
    (forall k, ~In k (map fst l) \/ ~In k (map fst ls)) ->
    NoCallActionT ls (inlineSingle_pos l a n) ->
    NoCallActionT ls a.
Proof.
  unfold inlineSingle_pos; intros; remember (nth_error _ _) as nth_err0; symmetry in Heqnth_err0; destruct nth_err0; auto.
  apply nth_error_In in Heqnth_err0.
  eapply inline_NeverCall; eauto.
  apply (in_map fst) in Heqnth_err0.
  destruct (H0 (fst d)); auto.
  intro; apply H2; rewrite in_map_iff in *; dest; exists x; inv H3; split; auto.
Qed.

Lemma inlineSome_pos_NeverCall xs :
  forall k ty (a : ActionT ty k)
         (l : list DefMethT) (ls : list DefMethT),
    (forall meth ty,
        In meth l ->
        (forall arg, NeverCallActionT (projT2 (snd meth) ty arg))) ->
    (forall k, ~In k (map fst l) \/ ~In k (map fst ls)) ->
    NoCallActionT ls (fold_left (inlineSingle_pos l) xs a) ->
    NoCallActionT ls a.
Proof.
  induction xs; simpl; intros; auto.
  eapply inlineSingle_pos_NeverCall; eauto.
Qed.

Lemma NoCall_Meths_reduction xs :
  forall (l l' : list DefMethT)
         (HDisjKeys : DisjKey l l')
         (HNeverCall : forall meth ty,
             In meth l' ->
             (forall arg, NeverCallActionT (projT2 (snd meth) ty arg))),
    (forall meth ty,
        In meth (fold_left (inlineSingle_Flat_pos l') xs l) ->
        (forall arg, NoCallActionT l (projT2 (snd meth) ty arg))) ->
    (forall meth ty,
        In meth l ->
        (forall arg, NoCallActionT l (projT2 (snd meth) ty arg))).
Proof.
  intros.
  rewrite inline_Meths_eq_inlineSome in *; auto.
  destruct meth, s0; simpl in *.
  specialize (H _ ty (in_map (inline_Meths l' xs) _ _ H0) arg); unfold inline_Meths in *; simpl in *.
  eapply inlineSome_pos_NeverCall; eauto.
  apply DisjKey_Commutative in HDisjKeys; intro k; specialize (HDisjKeys k); assumption.
Qed.   

Lemma NoCall_Rules_reduction :
  forall (l : list DefMethT) (lr : list RuleT) (ls : list DefMethT)
         (DisjKeys : forall k, ~In k (map fst l) \/ ~In k (map fst ls))
         (HNeverCall : forall meth ty,
             In meth l ->
             (forall arg, NeverCallActionT (projT2 (snd meth) ty arg))),
    (forall rule ty,
        In rule (inlineAll_Rules l lr) ->
        NoCallActionT ls (snd rule ty)) ->
    (forall rule ty,
        In rule lr ->
        NoCallActionT ls (snd rule ty)).
Proof.
  intros; destruct rule; simpl in *.
  rewrite inlineAll_Rules_in in *.
  eapply inlineSome_pos_NeverCall; eauto.
  specialize (H _ ty (in_map (inline_Rules l _) _ _ H0)); unfold inline_Rules in *;
    simpl in *; apply H.
Qed.

Lemma SameKeys_inlineSome_Meths_map xs :
  forall (l l' : list DefMethT),
    (map fst (map (inline_Meths l' xs) l)) = map fst l.
Proof.
  unfold inline_Meths; induction l; simpl; auto; intros.
  setoid_rewrite IHl; apply f_equal2; destruct a; auto.
Qed.

Lemma SameKindAttrs_inlineSome_Meths_map xs :
  forall (l l' : list DefMethT),
    (getKindAttr (map (inline_Meths l' xs) l)) = getKindAttr l.
Proof.
  unfold inline_Meths; induction l; simpl; auto; intros.
  setoid_rewrite IHl; apply f_equal2; destruct a, s0; auto.
Qed.


Lemma inlineAll_NoCall_Meths_RegFile_fold_flat :
  forall (l l' : list DefMethT)
         (HNeverCall : forall meth ty,
             In meth l' ->
             (forall arg, NeverCallActionT (projT2 (snd meth) ty arg)))
         (HDisjMeths : DisjKey l l')
         (HNoCall : forall meth ty,
             In meth l -> 
             (forall arg,
                 NoCallActionT l (projT2 (snd meth) ty arg))),
    inlineAll_Meths (l ++ l')
    = map (inline_Meths l' (seq 0 (length l'))) l ++ l' /\
    (forall meth ty,
        In meth (map (inline_Meths l' (seq 0 (length l'))) l) ->
        (forall arg,
            NoCallActionT ((map (inline_Meths l' (seq 0 (length l'))) l)) (projT2 (snd meth) ty arg))).
Proof.
  intros; split.
  - unfold inlineAll_Meths; rewrite inlineAll_Meths_RegFile_fold_flat; auto.
    erewrite (inlineSome_Meths_pos_NoCalls_ident); eauto; [| apply SubList_refl].
    rewrite inline_Meths_eq_inlineSome; auto.
  - intros.
    rewrite in_map_iff in H; dest; subst; destruct x, s0.
    specialize (HNoCall _ ty H0 arg); simpl in *.
    eapply NeverCall_inlineSome_pos_persistent; auto.
    * specialize (SameKindAttrs_inlineSome_Meths_map (seq 0 (length l')) l l') as P0.
      eauto using SignatureReplace_NoCall.
Qed.

Lemma SameKeys_inlineSome_Rules_map xs :
  forall (l' : list DefMethT) (l : list RuleT),
    (map fst (map (inline_Rules l' xs) l)) = map fst l.
Proof.
  unfold inline_Rules; induction l; simpl; auto; intros.
  setoid_rewrite IHl; apply f_equal2; destruct a; auto.
Qed.

Lemma inlineAll_NoCall_Rules_RegFile_fold_flat :
  forall (l l' : list DefMethT) (lr : list RuleT)
         (HNeverCall : forall meth ty,
             In meth l' ->
             (forall arg, NeverCallActionT (projT2 (snd meth) ty arg)))
         (HDisjMeths : DisjKey l l')
         (HNoCall : forall rule ty,
             In rule lr ->
             NoCallActionT l (snd rule ty)),
    inlineAll_Rules (l ++ l') lr = map (inline_Rules l' (seq 0 (length l'))) lr /\
    (forall rule ty,
        In rule (map (inline_Rules l' (seq 0 (length l'))) lr) ->
        NoCallActionT l (snd rule ty)).
Proof.
  intros; split.
  - rewrite inlineAll_Rules_NoCalls; auto.
    unfold inlineAll_Rules at 2.
    erewrite inlineSome_Rules_pos_NoCalls_ident; eauto using SubList_refl.
    apply inlineAll_Rules_in.
  - intros; rewrite in_map_iff in *; dest; subst; destruct x; simpl in *.
    apply NeverCall_inlineSome_pos_persistent; auto.
    apply (HNoCall _ _ H0).
Qed.

Lemma inlineSingle_pos_app_l (l1 l2 : list DefMethT) ty k (a : ActionT ty k) :
  forall n,
    n < length l1 ->
    inlineSingle_pos (l1 ++ l2) a n =  inlineSingle_pos l1 a n.
Proof.
  intros; unfold inlineSingle_pos.
  remember (nth_error (l1 ++ l2) n) as nth_err0.
  destruct nth_err0; rewrite nth_error_app1 in Heqnth_err0; auto; rewrite <- Heqnth_err0; reflexivity.
Qed.

Lemma inlineSingle_pos_app_r (l1 l2 : list DefMethT) ty k (a : ActionT ty k) :
  forall n,
    length l1 <= n ->
    inlineSingle_pos (l1 ++ l2) a n =  inlineSingle_pos l2 a (n - length l1).
Proof.
  intros; unfold inlineSingle_pos.
  remember (nth_error (l1 ++ l2) n) as nth_err0.
  destruct nth_err0; rewrite nth_error_app2 in Heqnth_err0; auto;  rewrite <- Heqnth_err0; reflexivity.
Qed.

Lemma inlineSome_pos_app_l (l1 l2 : list DefMethT) ty k (a : ActionT ty k) n :
  n <= length l1 ->
  fold_left (inlineSingle_pos (l1 ++ l2)) (seq 0 n) a = fold_left (inlineSingle_pos l1) (seq 0 n) a.
Proof.
  induction n; auto; intros.
  rewrite seq_eq; repeat rewrite fold_left_app; simpl.
  rewrite inlineSingle_pos_app_l; [|lia].
  rewrite IHn; auto; lia.
Qed.

Lemma inlineSome_pos_app_r (l1 l2 : list DefMethT) ty k (a : ActionT ty k) n :
  fold_left (inlineSingle_pos (l1 ++ l2)) (seq (length l1) n) a
  = fold_left (inlineSingle_pos l2) (seq 0 n) a.
Proof.
  induction n; auto; intros.
  repeat rewrite seq_eq; repeat rewrite fold_left_app; simpl.
  rewrite inlineSingle_pos_app_r; [|lia].
  rewrite IHn, minus_plus; reflexivity.
Qed.

Lemma inlineSome_pos_app (l1 l2 : list DefMethT) ty k (a : ActionT ty k) :
  forall n m,
    n = length l1 ->
    m = length l2 ->
    fold_left (inlineSingle_pos (l1 ++ l2)) (seq 0 (n + m)) a =
    fold_left (inlineSingle_pos l2) (seq 0 m) (fold_left (inlineSingle_pos l1) (seq 0 n) a).
Proof.
  intros.
  assert (n <= length (l1 ++ l2)) as P0.
  { rewrite app_length; lia. }
  rewrite H, H0, <- app_length.
  rewrite (seq_app' _ P0), fold_left_app, app_length, H, minus_plus, plus_O_n.
  rewrite inlineSome_pos_app_r, inlineSome_pos_app_l; auto.
Qed.

Lemma SameKeys_inlineSingle_Flat meths1 meths2 n :
  map fst (inlineSingle_Flat_pos meths1 meths2 n) = map fst meths2.
Proof.
  unfold inlineSingle_Flat_pos; destruct nth_error; auto.
  apply inline_preserves_keys_Meth.
Qed.

Lemma SameKeys_inlineSome_Flat xs :
  forall meths1 meths2,
    map fst (fold_left (inlineSingle_Flat_pos meths1) xs meths2) = map fst meths2.
Proof.
  induction xs; simpl; auto; intros.
  rewrite IHxs, SameKeys_inlineSingle_Flat; reflexivity.
Qed.

Lemma SameKindAttrs_inlineSingle_Flat meths1 meths2 n :
  getKindAttr (inlineSingle_Flat_pos meths1 meths2 n) = getKindAttr meths2.
Proof.
  unfold inlineSingle_Flat_pos; destruct nth_error; auto.
  apply inline_preserves_KindAttrs_Meth.
Qed.

Lemma SameKindAttrs_inlineSome_Flat xs :
  forall meths1 meths2,
    getKindAttr (fold_left (inlineSingle_Flat_pos meths1) xs meths2) = getKindAttr meths2.
Proof.
  induction xs; simpl; auto; intros.
  rewrite IHxs, SameKindAttrs_inlineSingle_Flat; reflexivity.
Qed.

Lemma UpdOrMeths_RegsT_app (uml1 uml2 : UpdOrMeths) :
  UpdOrMeths_RegsT (uml1 ++ uml2) = UpdOrMeths_RegsT uml1 ++ UpdOrMeths_RegsT uml2.
Proof.
  induction uml1; simpl; auto.
  destruct a; simpl; auto.
  rewrite IHuml1; reflexivity.
Qed.

Lemma UpdOrMeths_MethsT_app (uml1 uml2 : UpdOrMeths) :
  UpdOrMeths_MethsT (uml1 ++ uml2) = UpdOrMeths_MethsT uml1 ++ UpdOrMeths_MethsT uml2.
Proof.
  induction uml1; simpl; auto.
  destruct a; simpl; auto.
  rewrite IHuml1; reflexivity.
Qed.

Lemma SemCompActionEEquivWMap (k : Kind) (ea : EActionT type k):
  forall o calls retl bexpr v' v expr1 expr2,
    SemRegMapExpr expr1 v ->
    SemRegMapExpr expr2 v ->
    SemCompActionT (EcompileAction o ea bexpr expr1) v' calls retl ->
    SemCompActionT (EcompileAction o ea bexpr expr2) v' calls retl.
Proof.
  induction ea; intros; simpl in *; eauto.
  - inv H2; EqDep_subst; [econstructor 1 | econstructor 2]; eauto.
  - inv H2; EqDep_subst; econstructor; eauto.
  - inv H2; EqDep_subst; econstructor; eauto.
  - inv H2; EqDep_subst; econstructor; eauto.
  - inv H2; EqDep_subst; econstructor; eauto.
  - inv H1; simpl in *; EqDep_subst; rewrite unifyWO in *.
    inv HSemCompActionT_a; EqDep_subst.
    econstructor; eauto.
    inv HRegMapWf.
    repeat econstructor; auto.
    inv H1; EqDep_subst; [econstructor 2| econstructor 3]; eauto;
      erewrite SemRegExprVals; eauto.
  - inv H2; simpl in *; EqDep_subst.
    inv HSemCompActionT; simpl in *; EqDep_subst.
    inv HSemCompActionT0; simpl in *; EqDep_subst.
    inv HSemCompActionT_cont; simpl in *; EqDep_subst.
    inv HSemCompActionT_cont0; simpl in *; EqDep_subst.
    repeat (econstructor; eauto).
  - inv H1; EqDep_subst; econstructor; eauto.
  - inv H1; EqDep_subst; econstructor; eauto.
    inv HRegMapWf; constructor; auto.
    erewrite SemRegExprVals; eauto.
  - inv H2; EqDep_subst; econstructor; eauto.
    rewrite (SemRegExprVals H0 HWriteMap); assumption.
  - inv H1; EqDep_subst;[econstructor 10 | econstructor 11]; eauto; inv HUpdate; inv H1;
      EqDep_subst; econstructor; eauto.
    + econstructor 2; eauto.
      erewrite SemRegExprVals; eauto.
    + econstructor 3; eauto.
      erewrite SemRegExprVals; eauto.
    + econstructor 2; eauto.
      erewrite SemRegExprVals; eauto.
    + econstructor 3; eauto.
      erewrite SemRegExprVals; eauto.
  - inv H1; EqDep_subst; inv HWriteMap; inv H1; EqDep_subst.
    + repeat (econstructor; eauto).
      erewrite SemRegExprVals; eauto.
    + do 2 (econstructor; eauto).
      econstructor 3; eauto.
      erewrite SemRegExprVals; eauto.
    + do 3 (econstructor; eauto).
      erewrite SemRegExprVals; eauto.
    + do 2 (econstructor; eauto).
      econstructor 3; eauto.
      erewrite SemRegExprVals; eauto.
  - inv H2; EqDep_subst;[econstructor 14 | econstructor 15]; eauto;
      rewrite (SemRegExprVals H0 HWriteMap); eauto.
Qed.

Lemma SemCompActionEEquivBexpr (k : Kind) (ea : EActionT type k):
  forall o calls retl expr1 v' (bexpr1 bexpr2 : Bool @# type),
    evalExpr bexpr1  = evalExpr bexpr2  ->
    SemCompActionT (EcompileAction o ea bexpr1 expr1) v' calls retl ->
    SemCompActionT (EcompileAction o ea bexpr2 expr1) v' calls retl.
Proof.
  induction ea; intros; simpl in *; eauto.
  - inv H1; EqDep_subst; [econstructor 1| econstructor 2]; eauto.
  - inv H1; EqDep_subst; econstructor; eauto.
  - inv H1; EqDep_subst; econstructor; eauto.
  - inv H1; EqDep_subst; econstructor; eauto.
  - inv H1; EqDep_subst; econstructor; eauto.
  - inv H0; simpl in *; EqDep_subst.
    econstructor; eauto.
    rewrite (unifyWO val_a) in HSemCompActionT_a.
    inv HSemCompActionT_a; EqDep_subst.
    econstructor; eauto.
    inv HRegMapWf; destruct regMap_a.
    split; auto.
    destruct (bool_dec (evalExpr bexpr2) true).
    inv H0; EqDep_subst.
    + econstructor 2; eauto.
    + congruence.
    + inv H0; EqDep_subst.
      * congruence.
      * econstructor 3; eauto.
  - inv H1; simpl in *; EqDep_subst.
    inv HSemCompActionT; simpl in *; EqDep_subst.
    inv HSemCompActionT0; simpl in *; EqDep_subst.
    inv HSemCompActionT_cont; EqDep_subst.
    inv HSemCompActionT_cont0; simpl in *; EqDep_subst.
    do 3 econstructor.
    + eapply IHea1 with (bexpr1 := (Var type (SyntaxKind Bool)
                                        (evalExpr bexpr1 && evalExpr e))); eauto.
      simpl; rewrite H0; reflexivity.
    + reflexivity.
    + econstructor.
      * eapply IHea2 with (bexpr1 := (Var type (SyntaxKind Bool)
                                          (evalExpr (bexpr2 && ! e)%kami_expr))); eauto.
        simpl; rewrite <- H0; eauto.
      * reflexivity.
      * econstructor; simpl.
        eapply H; eauto.
  - inv H0; EqDep_subst.
    econstructor; eauto.
  - inv H1; EqDep_subst.
    econstructor; eauto.
  - inv H0; EqDep_subst.
    econstructor; eauto.
    + unfold WfRegMapExpr in *; dest; split; auto.
      inv H0; EqDep_subst.
      * econstructor; rewrite H in *; eauto.
      * econstructor 3; rewrite H in *; eauto.
    + econstructor 11; eauto.
      unfold WfRegMapExpr in *; dest; split; auto.
      inv H0; EqDep_subst.
      * econstructor; rewrite H in *; eauto.
      * econstructor 3; rewrite H in *; eauto.
  - inv H0; EqDep_subst.
    econstructor; eauto.
    + unfold WfRegMapExpr in *; dest; split; auto.
      inv H0; EqDep_subst.
      * econstructor; rewrite H in *; eauto.
      * econstructor 3; rewrite H in *; eauto.
    + econstructor 13; eauto.
      unfold WfRegMapExpr in *; dest; split; auto.
      inv H0; EqDep_subst.
      * econstructor; rewrite H in *; eauto.
      * econstructor 3; rewrite H in *; eauto.
  - inv H1; EqDep_subst; [econstructor | econstructor 15]; eauto.
Qed.

Lemma SemCompActionEquivBexpr (k : Kind) (a : ActionT type k):
  forall o calls retl expr1 v' (bexpr1 bexpr2 : Bool @# type),
    evalExpr bexpr1  = evalExpr bexpr2  ->
    SemCompActionT (compileAction o a bexpr1 expr1) v' calls retl ->
    SemCompActionT (compileAction o a bexpr2 expr1) v' calls retl.
Proof.
  induction a; intros; simpl in *; eauto.
  - inv H1; EqDep_subst; [econstructor 1| econstructor 2]; eauto.
  - inv H1; EqDep_subst; econstructor; eauto.
  - inv H1; EqDep_subst; econstructor; eauto.
  - inv H1; EqDep_subst; econstructor; eauto.
  - inv H1; EqDep_subst; econstructor; eauto.
  - inv H0; simpl in *; EqDep_subst.
    econstructor; eauto.
    rewrite (unifyWO val_a) in HSemCompActionT_a.
    inv HSemCompActionT_a; EqDep_subst.
    econstructor; eauto.
    inv HRegMapWf; destruct regMap_a.
    split; auto.
    destruct (bool_dec (evalExpr bexpr2) true).
    inv H0; EqDep_subst.
    + econstructor 2; eauto.
    + congruence.
    + inv H0; EqDep_subst.
      * congruence.
      * econstructor 3; eauto.
  - inv H1; simpl in *; EqDep_subst.
    inv HSemCompActionT; simpl in *; EqDep_subst.
    inv HSemCompActionT0; simpl in *; EqDep_subst.
    inv HSemCompActionT_cont; EqDep_subst.
    inv HSemCompActionT_cont0; simpl in *; EqDep_subst.
    do 3 econstructor.
    + eapply IHa1 with (bexpr1 := (Var type (SyntaxKind Bool)
                                       (evalExpr (bexpr2 && e)%kami_expr))); eauto.
      simpl; rewrite <- H0; eauto.
    + reflexivity.
    + econstructor.
      * eapply IHa2 with (bexpr1 := (Var type (SyntaxKind Bool)
                                         (evalExpr (bexpr2 && ! e)%kami_expr)));eauto.
        simpl; rewrite <-H0; eauto.
      * reflexivity.
      * econstructor; simpl.
        eapply H; eauto.
  - inv H0; EqDep_subst.
    econstructor; eauto.
Qed.

Lemma EpredFalse_UpdsNil k ea :
  forall (bexpr: Bool @# type) o u regMap1 regMap2 calls val
         (HNbexpr : evalExpr bexpr = false) rexpr (HRegMap : SemRegMapExpr rexpr regMap1),
    @SemCompActionT k (EcompileAction (o, u) ea bexpr rexpr) regMap2 calls val ->
    regMap1 = regMap2 /\ calls = nil.
Proof.
  induction ea; intros.
  - inv H0; EqDep_subst;[congruence|eauto].
  - inv H0; EqDep_subst; eauto.
  - inv H0; EqDep_subst; eauto.
    specialize (IHea _ _ _ _ _ _ _ HNbexpr _ HRegMap HSemCompActionT_a); dest.
    rewrite H0 in HRegMap.
    specialize (H _ _ _ _ _ _ _ _ HNbexpr _ (SemVarRegMap _) HSemCompActionT_cont); dest.
    split; subst; auto.
  - inv H0; EqDep_subst; eauto.
  - inv H0; EqDep_subst; eauto.
  - inv H; simpl in *; EqDep_subst; eauto.
    rewrite (unifyWO val_a) in HSemCompActionT_a.
    inv HSemCompActionT_a; EqDep_subst.
    inv HRegMapWf; inv H; EqDep_subst;[congruence|].
    specialize (IHea _ _ _ _ _ _ _ HNbexpr _ (SemVarRegMap _) HSemCompActionT_cont); dest.
    rewrite (SemRegExprVals HRegMap HSemRegMap); auto.
  - inv H0; simpl in *; EqDep_subst.
    inv HSemCompActionT; simpl in *; EqDep_subst.
    inv HSemCompActionT0; simpl in *; EqDep_subst.
    inv HSemCompActionT_cont; EqDep_subst.
    inv HSemCompActionT_cont0; EqDep_subst.
    apply Eqdep.EqdepTheory.inj_pair2 in H4; subst; simpl in *.
    assert (forall (b : Expr type (SyntaxKind Bool)),
               (evalExpr (Var type (SyntaxKind Bool) (evalExpr bexpr && evalExpr b)) = false)).
    { intros; simpl; rewrite HNbexpr; auto. }
    specialize (IHea1 _ _ _ _ _ _ _ (H0 e) _ HRegMap HSemCompActionT_a); dest.
    specialize (IHea2 _ _ _ _ _ _ _ (H0 (!e)%kami_expr) _ (SemVarRegMap _) HSemCompActionT_a0); dest.
    specialize (H _ _ _ _ _ _ _ _ HNbexpr _ (SemVarRegMap _) HSemCompActionT); dest.
    subst; auto.
  - inv H; EqDep_subst; eauto.
  - inv H; EqDep_subst.
    inv HRegMapWf.
    rewrite (SemRegExprVals HRegMap H); auto.
  - inv H0; EqDep_subst; eauto;
      eapply H with (rexpr := VarRegMap type writeMapTy); eauto;
        assert (sth: regMap1 = writeMapTy) by
          (eapply SemRegExprVals; eauto);
        subst;
        econstructor.
  - inv H; EqDep_subst; eauto; unfold WfRegMapExpr in *; dest;
      inv H; EqDep_subst; [rewrite HNbexpr in *; discriminate| | rewrite HNbexpr in *; discriminate | ];
        specialize (IHea _ _ _ _ _ _ _ HNbexpr _ (SemVarRegMap _) HSemCompActionT); dest; subst;
          rewrite (SemRegExprVals HSemRegMap HRegMap); split; auto.
  - inv H; EqDep_subst; eauto; unfold WfRegMapExpr in *; dest;
      inv H; EqDep_subst; [rewrite HNbexpr in *; discriminate| | rewrite HNbexpr in *; discriminate | ];
        specialize (IHea _ _ _ _ _ _ _ HNbexpr _ (SemVarRegMap _) HSemCompActionT); dest; subst;
          rewrite (SemRegExprVals HSemRegMap HRegMap); split; auto.
  - inv H0; EqDep_subst; eauto;
      eapply H with (rexpr := VarRegMap type writeMapTy); eauto; unfold WfRegMapExpr in *; dest;
        assert (sth: regMap1 = writeMapTy) by
          (eapply SemRegExprVals; eauto);
        subst;
        econstructor.
Qed.

Lemma predFalse_UpdsNil k a:
  forall (bexpr: Bool @# type) o u regMap1 regMap2 calls val
         (HNbexpr : evalExpr bexpr = false) rexpr (HRegMap : SemRegMapExpr rexpr regMap1),
    @SemCompActionT k (compileAction (o, u) a bexpr rexpr) regMap2 calls val ->
    regMap1 = regMap2 /\ calls = nil.
Proof.
  induction a; intros.
  - inv H0; EqDep_subst;[congruence|eauto].
  - inv H0; EqDep_subst; eauto.
  - inv H0; EqDep_subst; eauto.
    specialize (IHa _ _ _ _ _ _ _ HNbexpr _ HRegMap HSemCompActionT_a); dest.
    rewrite H0 in HRegMap.
    specialize (H _ _ _ _ _ _ _ _ HNbexpr _ (SemVarRegMap _) HSemCompActionT_cont); dest.
    split; subst; auto.
  - inv H0; EqDep_subst; eauto.
  - inv H0; EqDep_subst; eauto.
  - inv H; simpl in *; EqDep_subst; eauto.
    rewrite (unifyWO val_a) in HSemCompActionT_a.
    inv HSemCompActionT_a; EqDep_subst.
    inv HRegMapWf; inv H; EqDep_subst;[congruence|].
    specialize (IHa _ _ _ _ _ _ _ HNbexpr _ (SemVarRegMap _) HSemCompActionT_cont); dest.
    rewrite (SemRegExprVals HRegMap HSemRegMap); auto.
  - inv H0; simpl in *; EqDep_subst.
    inv HSemCompActionT; simpl in *; EqDep_subst.
    inv HSemCompActionT0; simpl in *; EqDep_subst.
    inv HSemCompActionT_cont; EqDep_subst.
    inv HSemCompActionT_cont0; EqDep_subst.
    apply Eqdep.EqdepTheory.inj_pair2 in H4; subst; simpl in *.
    assert (forall (b : Expr type (SyntaxKind Bool)),
               (evalExpr (Var type (SyntaxKind Bool) (evalExpr bexpr && evalExpr b)) = false)).
    { intros; simpl; rewrite HNbexpr; auto. }
    specialize (IHa1 _ _ _ _ _ _ _ (H0 e) _ HRegMap HSemCompActionT_a); dest.
    specialize (IHa2 _ _ _ _ _ _ _ (H0 (!e)%kami_expr) _ (SemVarRegMap _) HSemCompActionT_a0); dest.
    specialize (H _ _ _ _ _ _ _ _ HNbexpr _ (SemVarRegMap _) HSemCompActionT); dest.
    subst; auto.
  - inv H; EqDep_subst; eauto.
  - inv H; EqDep_subst.
    inv HRegMapWf.
    rewrite (SemRegExprVals HRegMap H); auto.
Qed.

Lemma ESameOldAction (k : Kind) (ea : EActionT type k) :
  forall oInit uInit writeMap old upds wOld wUpds calls retl bexpr
         (HSemRegMap : SemRegMapExpr writeMap (wOld, wUpds)),
    @SemCompActionT k (EcompileAction (oInit, uInit) ea bexpr writeMap) (old, upds) calls retl ->
    wOld = old.
Proof.
  induction ea; intros; simpl in *.
  - inv H0; EqDep_subst; simpl in *; eapply H; eauto.
  - inv H0; EqDep_subst; simpl in *.
    eapply H; eauto.
  - inv H0; EqDep_subst; simpl in *.
    destruct regMap_a.
    specialize (H _ _ _ _ _ _ _ _ _ _ _ (SemVarRegMap _) HSemCompActionT_cont); subst.
    specialize (IHea _ _ _ _ _ _ _ _ _ _ HSemRegMap HSemCompActionT_a); assumption.
  - inv H0; EqDep_subst; simpl in *.
    eapply H; eauto.
  - inv H0; EqDep_subst; simpl in *.
    eapply H; eauto.
  - inv H; simpl in *; EqDep_subst.
    rewrite (unifyWO val_a) in HSemCompActionT_a.
    inv HSemCompActionT_a; EqDep_subst.
    destruct regMap_a; unfold WfRegMapExpr in *; dest.
    inv H; EqDep_subst.
    + specialize (IHea _ _ _ _ _ _ _ _ _ _ (SemVarRegMap _) HSemCompActionT_cont).
      specialize (SemRegExprVals HSemRegMap HSemRegMap0) as TMP; inv TMP.
      reflexivity.
    + specialize (IHea  _ _ _ _ _ _ _ _ _ _ (SemVarRegMap _) HSemCompActionT_cont).
      specialize (SemRegExprVals HSemRegMap HSemRegMap0) as TMP; inv TMP.
      reflexivity.
  - inv H0; simpl in *; EqDep_subst.
    inv HSemCompActionT; simpl in *; EqDep_subst.
    inv HSemCompActionT0; simpl in *; EqDep_subst.
    inv HSemCompActionT_cont; EqDep_subst.
    inv HSemCompActionT_cont0; simpl in *; EqDep_subst.
    destruct regMap_a, regMap_a0.
    specialize (H _ _ _ _ _ _ _ _ _ _ _ (SemVarRegMap _) HSemCompActionT).
    simpl in *.
    specialize (IHea1 _ _ _ _ _ _ _ _ _ _ HSemRegMap HSemCompActionT_a).
    specialize (IHea2 _ _ _ _ _ _ _ _ _ _ (SemVarRegMap _) HSemCompActionT_a0).
    subst; reflexivity.
  - inv H; EqDep_subst; simpl in *.
    eapply IHea; eauto.
  - inv H; EqDep_subst.
    unfold WfRegMapExpr in *; dest.
    specialize (SemRegExprVals H HSemRegMap) as TMP; inv TMP.
    reflexivity.
  - inv H0; EqDep_subst.
    eapply H with (writeMap := VarRegMap type writeMapTy); eauto;
    assert (sth: writeMapTy = (wOld, wUpds)) by
        (eapply SemRegExprVals; eauto);
    subst;
    econstructor.
  - inv H; EqDep_subst; unfold WfRegMapExpr in *; destruct regMapVal; dest;
      specialize (IHea _ _ _ _ _ _ _ _ _ _ (SemVarRegMap _) HSemCompActionT); subst;
        inv H; EqDep_subst; specialize (SemRegExprVals HSemRegMap HSemRegMap0) as TMP; inv TMP; reflexivity.
  - inv H; EqDep_subst; unfold WfRegMapExpr in *; destruct regMapVal; dest;
      specialize (IHea _ _ _ _ _ _ _ _ _ _ (SemVarRegMap _) HSemCompActionT); subst;
        inv H; EqDep_subst; specialize (SemRegExprVals HSemRegMap HSemRegMap0) as TMP; inv TMP; reflexivity.
  - inv H0; EqDep_subst;
    eapply H with (writeMap := VarRegMap type writeMapTy); eauto;
    assert (sth: writeMapTy = (wOld, wUpds)) by
        (eapply SemRegExprVals; eauto);
    subst;
    econstructor.
Qed.

Lemma EEquivActions k ea:
  forall writeMap o old upds oInit uInit
         (HoInitNoDups : NoDup (map fst oInit))
         (HuInitNoDups : forall u, In u uInit -> NoDup (map fst u))
         (HPriorityUpds : PriorityUpds oInit uInit o)
         (HConsistent : getKindAttr o = getKindAttr old)
         (WfMap : WfRegMapExpr writeMap (old, upds)),
  forall calls retl upds',
    @SemCompActionT k (EcompileAction (oInit, uInit) ea (Const type true) writeMap) upds' calls retl ->
    (forall u, In u (snd upds') -> NoDup (map fst u) /\ SubList (getKindAttr u) (getKindAttr old)) /\
    exists uml,
      upds' = (old, match (UpdOrMeths_RegsT uml) with
                    |nil => upds
                    |_ :: _ => (hd nil upds ++ (UpdOrMeths_RegsT uml)) :: tl upds
                    end) /\
      calls = (UpdOrMeths_MethsT uml) /\
      ESemAction o ea uml retl.
Proof.
  induction ea; subst; intros; simpl in *.
  - inv H0; EqDep_subst;[|discriminate].
    specialize (H _ _ _ _ _ _ _ HoInitNoDups HuInitNoDups HPriorityUpds HConsistent WfMap _ _ _ HSemCompActionT); dest; split; auto.
    exists (umMeth (meth, existT SignT s (evalExpr e, ret))::x); repeat split; simpl; subst; auto.
    econstructor; eauto.
  - inv H0; EqDep_subst.
    specialize (H _ _ _ _ _ _ _ HoInitNoDups HuInitNoDups HPriorityUpds HConsistent WfMap _ _ _ HSemCompActionT); dest; split; auto.
    exists x; repeat split; auto.
    econstructor; eauto.
  - inv H0; EqDep_subst.
    specialize (IHea _ _ _ _ _ _ HoInitNoDups HuInitNoDups HPriorityUpds HConsistent WfMap _ _ _ HSemCompActionT_a); dest.
    assert (WfRegMapExpr (VarRegMap type regMap_a) regMap_a) as WfMap0.
    { unfold WfRegMapExpr; split;[econstructor|].
      destruct regMap_a; inv H1; intros.
      apply (H0 _ H1).
    }
    rewrite H1 in *.
    specialize (H _ _ _ _ _ _ _ HoInitNoDups HuInitNoDups HPriorityUpds HConsistent WfMap0 _ _ _ HSemCompActionT_cont); dest.
    split; auto.
    exists (x++x0); rewrite UpdOrMeths_RegsT_app, UpdOrMeths_MethsT_app; repeat split; auto.
    + destruct (UpdOrMeths_RegsT x0); simpl in *; auto.
      * rewrite app_nil_r; assumption.
      * destruct (UpdOrMeths_RegsT x); simpl in *; auto.
        rewrite app_comm_cons, app_assoc; assumption.
    + subst; auto.
    + econstructor; eauto.
      rewrite H4 in H; simpl in *.
      clear - H.
      destruct (UpdOrMeths_RegsT x0), (UpdOrMeths_RegsT x); eauto using DisjKey_nil_r, DisjKey_nil_l; simpl in *.
      specialize (H _ (or_introl _ eq_refl)); simpl in *; dest.
      repeat rewrite map_app in H.
      intro k.
      destruct (In_dec string_dec k (map fst (p0::r0))); auto.
      right; intro.
      destruct (NoDup_app_Disj string_dec _ _ H k); auto.
      apply H2; rewrite in_app_iff; right; auto.
  - inv H0; EqDep_subst.
    specialize (H _ _ _ _ _ _ _ HoInitNoDups HuInitNoDups HPriorityUpds HConsistent WfMap _ _ _ HSemCompActionT); dest; split; auto.
    exists x; repeat split; auto.
    econstructor; eauto.
  - inv H0; EqDep_subst.
    specialize (H _ _ _ _ _ _ _ HoInitNoDups HuInitNoDups HPriorityUpds HConsistent WfMap _ _ _ HSemCompActionT); dest; split; auto.
    exists x.
    repeat split; simpl; auto.
    econstructor; eauto.
    inv HReadMap.
    apply (PriorityUpds_Equiv HoInitNoDups HuInitNoDups HUpdatedRegs HPriorityUpds); auto.
  - inv H; simpl in *; EqDep_subst.
    rewrite (unifyWO val_a) in HSemCompActionT_a.
    inv HSemCompActionT_a; EqDep_subst.
    destruct HRegMapWf, WfMap, regMap_a.
    inv H;[|discriminate]; EqDep_subst.
    specialize (SemRegExprVals H1 HSemRegMap) as P0; inv P0.
    assert (WfRegMapExpr (VarRegMap type (r0, (hd nil upds0 ++ (r, existT (fullType type) k (evalExpr e)) :: nil) :: tl upds0))
                         (r0, (hd nil upds0 ++ (r, existT (fullType type) k (evalExpr e)) :: nil) :: tl upds0)) as WfMap0.
    { split; auto. constructor. }
    specialize (IHea _ _ _ _ _ _ HoInitNoDups HuInitNoDups HPriorityUpds HConsistent WfMap0 _ _ _ HSemCompActionT_cont);
      dest; simpl in *; split; auto.
    exists ((umUpd (r, existT (fullType type) k (evalExpr e))):: x); repeat split; auto.
    + simpl; destruct (UpdOrMeths_RegsT x); simpl in *; auto.
      rewrite <- app_assoc in H3. rewrite <-app_comm_cons in H3.
      simpl in H3; auto.
    + simpl; econstructor; eauto.
      * rewrite H3 in H.
        destruct (UpdOrMeths_RegsT x); simpl in *; rewrite HConsistent; eapply H; simpl; eauto;
          repeat rewrite map_app, in_app_iff; [right | left]; simpl; auto.
      * repeat intro.
        rewrite H3 in H.
        destruct (UpdOrMeths_RegsT x); simpl in *; auto.
        destruct H7; subst; simpl in *; specialize (H _ (or_introl eq_refl)); dest; repeat rewrite map_app, NoDup_app_iff in H; simpl in *; dest.
        -- apply (H7 r); clear.
           rewrite in_app_iff; simpl; right; left; reflexivity.
           left; reflexivity.
        -- apply (H8 r); clear - H7.
           ++ rewrite in_app_iff; right; left; reflexivity.
           ++ right; rewrite in_map_iff; exists (r, v); split; auto.
  - inv H0; simpl in *; EqDep_subst.
    inv HSemCompActionT; simpl in *; EqDep_subst.
    inv HSemCompActionT0; simpl in *; EqDep_subst.
    inv HSemCompActionT_cont; EqDep_subst.
    inv HSemCompActionT_cont0; EqDep_subst.
    remember (evalExpr e) as P0.
    apply Eqdep.EqdepTheory.inj_pair2 in H4.
    rewrite H4 in *.
    clear H4; simpl in *.
    rewrite HeqP0 in HSemCompActionT_a, HSemCompActionT_a0.
    destruct P0; rewrite <- HeqP0 in *; simpl in *.
    + assert (forall b, (evalExpr (Var type (SyntaxKind Bool) b) = (evalExpr (Const type b)))) as Q0; auto.
      specialize (SemCompActionEEquivBexpr _ _ _ _ _ (Q0 false) HSemCompActionT_a0) as Q1.
      specialize (SemCompActionEEquivBexpr _ _ _ _ _ (Q0 true) HSemCompActionT_a) as Q2.
      specialize (IHea1 _ _ _ _ _ _ HoInitNoDups HuInitNoDups HPriorityUpds HConsistent WfMap _ _ _ Q2); dest.
      assert (evalExpr (Const type false) = false) as Q3; auto.
      destruct (EpredFalse_UpdsNil _ _ _ _ Q3 (SemVarRegMap regMap_a) Q1).
      assert (WfRegMapExpr (VarRegMap type regMap_a0) regMap_a0) as P7.
      { unfold WfRegMapExpr; split; [constructor|]. subst; eauto. }
      rewrite <- H4 in P7 at 2.
      rewrite H1 in P7.
      specialize (H _ _ _ _ _ _ _ HoInitNoDups HuInitNoDups HPriorityUpds HConsistent P7 _ _ _ HSemCompActionT); dest.
      split; auto.
      exists (x ++ x0); rewrite UpdOrMeths_RegsT_app, UpdOrMeths_MethsT_app; repeat split; auto.
      * destruct (UpdOrMeths_RegsT x0); simpl; auto.
        -- rewrite app_nil_r; auto.
        --  destruct (UpdOrMeths_RegsT x); simpl in *; auto.
            rewrite app_comm_cons, app_assoc; assumption.
      * subst; reflexivity.
      * econstructor; eauto.
        rewrite H6 in H; destruct (UpdOrMeths_RegsT x), (UpdOrMeths_RegsT x0); intro; simpl in *; auto.
        clear - H.
        specialize (H _ (or_introl _ (eq_refl))); dest.
        rewrite map_app in H.
        destruct (NoDup_app_Disj string_dec _ _ H k0); auto.
        left; intro; apply H1.
        rewrite map_app, in_app_iff; auto.
    + assert (forall b, (evalExpr (Var type (SyntaxKind Bool) b) =
                         (evalExpr (Const type b)))) as Q0; auto.
      remember WfMap as WfMap0.
      inv WfMap0.
      assert (evalExpr (Var type (SyntaxKind Bool) false) = false) as Q1; auto.
      destruct (EpredFalse_UpdsNil _ _ _ _ Q1 H0 HSemCompActionT_a).
      assert (WfRegMapExpr (VarRegMap type regMap_a) (old, upds)) as WfMap0.
      { rewrite <- H2.
        clear - WfMap.
        unfold WfRegMapExpr in *; dest; repeat split;[constructor| |]; eapply H0; eauto.
      }
      specialize (SemCompActionEEquivBexpr _ _ _ _ _ (Q0 true) HSemCompActionT_a0) as Q2.
      specialize (IHea2 _ _ _ _ _ _ HoInitNoDups HuInitNoDups HPriorityUpds HConsistent WfMap0 _ _ _ Q2); dest.
      assert (WfRegMapExpr (VarRegMap type regMap_a0) regMap_a0) as P7.
      { unfold WfRegMapExpr; split; [constructor|]. subst; eauto. }
      rewrite  H5 in P7 at 2.
      specialize (H _ _ _ _ _ _ _ HoInitNoDups HuInitNoDups HPriorityUpds HConsistent P7 _ _ _ HSemCompActionT); dest.
      split; auto.
      exists (x ++ x0); rewrite UpdOrMeths_RegsT_app, UpdOrMeths_MethsT_app; repeat split; auto.
      * destruct (UpdOrMeths_RegsT x0); simpl; auto.
        -- rewrite app_nil_r; auto.
        --  destruct (UpdOrMeths_RegsT x); simpl in *; auto.
            rewrite app_comm_cons, app_assoc; assumption.
      * subst; reflexivity.
      * econstructor 8; eauto.
        rewrite H8 in H; destruct (UpdOrMeths_RegsT x), (UpdOrMeths_RegsT x0); intro; simpl in *; auto.
        clear - H.
        specialize (H _ (or_introl _ (eq_refl))); dest.
        rewrite map_app in H.
        destruct (NoDup_app_Disj string_dec _ _ H k0); auto.
        left; intro; apply H1.
        rewrite map_app, in_app_iff; auto.
  - inv H; EqDep_subst.
    specialize (IHea _ _ _ _ _ _ HoInitNoDups HuInitNoDups HPriorityUpds HConsistent WfMap _ _ _ HSemCompActionT); dest; split; auto.
    exists x.
    repeat split; auto.
    econstructor; eauto.
  - inv H; EqDep_subst.
    inv WfMap; inv HRegMapWf.
    specialize (SemRegExprVals H H1) as TMP; subst; simpl in *.
    split; auto.
    exists nil.
    repeat split; auto.
    constructor; auto.
  - inv H0; EqDep_subst.
    apply (SemCompActionEEquivWMap _ _ _ (SemVarRegMap _) HWriteMap) in HSemCompActionT.
    specialize (H _ _ _ _ _ _ _ HoInitNoDups HuInitNoDups HPriorityUpds HConsistent WfMap _ _ _ HSemCompActionT); dest.
    split; auto.
    exists x.
    repeat split; auto.
    econstructor; eauto.
    inv HReadMap.
    apply (PriorityUpds_Equiv HoInitNoDups HuInitNoDups HUpdatedRegs HPriorityUpds); auto.
  - inv H; EqDep_subst; destruct regMapVal; simpl in *.
    + unfold WfRegMapExpr in *; dest.
      inv H; EqDep_subst; [|discriminate].
      specialize (SemRegExprVals H1 HSemRegMap) as TMP; inv TMP.
      assert (WfRegMapExpr (VarRegMap type
                                      (r,
                                       (hd [] upds0 ++
                                           [(dataArray,
                                             existT (fullType type) (SyntaxKind (Array idxNum Data))
                                                    (evalExpr
                                                       (fold_left
                                                          (fun (newArr : Expr type (SyntaxKind (Array idxNum Data))) (i : Fin.t num) =>
                                                             (IF ReadArrayConst mask0 i then newArr @[ idx + Const type ($(proj1_sig (Fin.to_nat i)))%word <- ReadArrayConst val i] else newArr)%kami_expr)
                                                          (getFins num) (Var type (SyntaxKind (Array idxNum Data)) regVal))))]) :: tl upds0))
                           (r,
                            (hd [] upds0 ++
                                [(dataArray,
                                  existT (fullType type) (SyntaxKind (Array idxNum Data))
                                         (evalExpr
                                            (fold_left
                                               (fun (newArr : Expr type (SyntaxKind (Array idxNum Data))) (i : Fin.t num) =>
                                                  (IF ReadArrayConst mask0 i then newArr @[ idx + Const type ($(proj1_sig (Fin.to_nat i)))%word <- ReadArrayConst val i] else newArr)%kami_expr)
                                               (getFins num) (Var type (SyntaxKind (Array idxNum Data)) regVal))))]) :: tl upds0)) as P0.
      { unfold WfRegMapExpr in *; dest; split; auto; constructor. }
      specialize (IHea _ _ _ _ _ _ HoInitNoDups HuInitNoDups HPriorityUpds HConsistent P0 _ _ _ HSemCompActionT); dest; split; auto.
      exists (umUpd (dataArray,
                   existT (fullType type) (SyntaxKind (Array idxNum Data))
                          (evalExpr
                             (fold_left
                                (fun (newArr : Expr type (SyntaxKind (Array idxNum Data))) (i : Fin.t num) =>
                                   (IF ReadArrayConst mask0 i then newArr @[ idx + Const type ($(proj1_sig (Fin.to_nat i)))%word <- ReadArrayConst val i] else newArr)%kami_expr)
                                (getFins num) (Var type (SyntaxKind (Array idxNum Data)) regVal))))::x).
      repeat split; auto.
      * simpl in *.
        clear - H3.
        destruct (UpdOrMeths_RegsT x); auto.
        rewrite <- app_assoc in H3; simpl in *; assumption.
      * econstructor; eauto.
        -- inv HReadMap.
           apply (PriorityUpds_Equiv HoInitNoDups HuInitNoDups HUpdatedRegs HPriorityUpds); auto.
        -- rewrite H3 in H.
           clear - H.
           destruct (UpdOrMeths_RegsT x); repeat intro; auto.
           specialize (H _ (or_introl eq_refl)).
           simpl in H; repeat rewrite map_app in H; simpl in *.
           rewrite NoDup_app_iff in H; dest; apply (H3 dataArray); destruct H0; subst; simpl; auto.
           ++ rewrite in_app_iff; right; simpl; left; auto.
           ++ rewrite in_app_iff; right; simpl; left; auto.
           ++ right; rewrite in_map_iff; exists (dataArray, v); auto.
    + unfold WfRegMapExpr in *; dest.
      inv H; EqDep_subst; [|discriminate].
      specialize (SemRegExprVals H1 HSemRegMap) as TMP; inv TMP.
      assert (WfRegMapExpr (VarRegMap type
                                      (r,
                                       (hd [] upds0 ++
                                           [(dataArray,
                                             existT (fullType type) (SyntaxKind (Array idxNum Data))
                                                    (evalExpr
                                                       (fold_left
                                                          (fun (newArr : Expr type (SyntaxKind (Array idxNum Data))) (i : Fin.t num) =>
                                                             (newArr @[ idx + Const type ($(proj1_sig (Fin.to_nat i)))%word <- ReadArrayConst val i])%kami_expr) (getFins num)
                                                          (Var type (SyntaxKind (Array idxNum Data)) regVal))))]) :: tl upds0))
                           (r,
                            (hd [] upds0 ++
                                [(dataArray,
                                  existT (fullType type) (SyntaxKind (Array idxNum Data))
                                         (evalExpr
                                            (fold_left
                                               (fun (newArr : Expr type (SyntaxKind (Array idxNum Data))) (i : Fin.t num) =>
                                                  (newArr @[ idx + Const type ($(proj1_sig (Fin.to_nat i)))%word <- ReadArrayConst val i])%kami_expr) (getFins num)
                                               (Var type (SyntaxKind (Array idxNum Data)) regVal))))]) :: tl upds0)) as P0.
      { unfold WfRegMapExpr in *; dest; split; auto; constructor. }
      specialize (IHea _ _ _ _ _ _ HoInitNoDups HuInitNoDups HPriorityUpds HConsistent P0 _ _ _ HSemCompActionT); dest; split; auto.
      exists (umUpd (dataArray,
                   existT (fullType type) (SyntaxKind (Array idxNum Data))
                          (evalExpr
                             (fold_left
                                (fun (newArr : Expr type (SyntaxKind (Array idxNum Data))) (i : Fin.t num) =>
                                   (newArr @[ idx + Const type ($(proj1_sig (Fin.to_nat i)))%word <- ReadArrayConst val i])%kami_expr) (getFins num)
                                (Var type (SyntaxKind (Array idxNum Data)) regVal))))::x).
      repeat split; auto.
      * simpl in *.
        clear - H3.
        destruct (UpdOrMeths_RegsT x); auto.
        rewrite <- app_assoc in H3; simpl in *; assumption.
      * econstructor 13; eauto.
        -- inv HReadMap.
           apply (PriorityUpds_Equiv HoInitNoDups HuInitNoDups HUpdatedRegs HPriorityUpds); auto.
        -- rewrite H3 in H.
           clear - H.
           destruct (UpdOrMeths_RegsT x); repeat intro; auto.
           specialize (H _ (or_introl eq_refl)).
           simpl in H; repeat rewrite map_app in H; simpl in *.
           rewrite NoDup_app_iff in H; dest; apply (H3 dataArray); destruct H0; subst; simpl; auto.
           ++ rewrite in_app_iff; right; simpl; left; auto.
           ++ rewrite in_app_iff; right; simpl; left; auto.
           ++ right; rewrite in_map_iff; exists (dataArray, v); auto.
  - inv H; EqDep_subst.
    + unfold WfRegMapExpr in *; dest.
      inv H; EqDep_subst; [|discriminate].
      specialize (SemRegExprVals H1 HSemRegMap) as TMP; inv TMP.
      assert (WfRegMapExpr (VarRegMap type
                                      (old0,
                                       (hd [] upds0 ++
                                           [(readReg,
                                             existT (fullType type) (SyntaxKind (Bit (Nat.log2_up idxNum))) (evalExpr (Var type (SyntaxKind (Bit (Nat.log2_up idxNum))) (evalExpr idx))))])
                                         :: tl upds0))
                           (old0,
                            (hd [] upds0 ++
                                [(readReg,
                                  existT (fullType type) (SyntaxKind (Bit (Nat.log2_up idxNum))) (evalExpr (Var type (SyntaxKind (Bit (Nat.log2_up idxNum))) (evalExpr idx))))])
                              :: tl upds0)) as P0.
      { unfold WfRegMapExpr in *; dest; split; auto; constructor. }
      specialize (IHea _ _ _ _ _ _ HoInitNoDups HuInitNoDups HPriorityUpds HConsistent P0 _ _ _ HSemCompActionT); dest; split; auto.
      exists (umUpd (readReg, existT (fullType type) (SyntaxKind (Bit (Nat.log2_up idxNum))) (evalExpr (Var type (SyntaxKind (Bit (Nat.log2_up idxNum))) (evalExpr idx))))::x).
      repeat split; auto.
      * simpl in *.
        clear - H3.
        destruct (UpdOrMeths_RegsT x); auto.
        rewrite <- app_assoc in H3; simpl in *; assumption.
      * econstructor; eauto.
        -- rewrite H3 in H.
           rewrite HConsistent.
           clear - H.
           simpl in *.
           destruct (UpdOrMeths_RegsT x); simpl in *; specialize (H _ (or_introl eq_refl)); dest;
             apply H0; repeat rewrite map_app, in_app_iff; [right| left; right]; left; auto.
        -- rewrite H3 in H.
           clear - H.
           simpl in *.
           destruct (UpdOrMeths_RegsT x); simpl in *; specialize (H _ (or_introl eq_refl)); dest; repeat intro; auto.
           repeat rewrite map_app in H; simpl in *.
           rewrite NoDup_app_iff in H; dest.
           apply (H3 readReg); destruct H1; subst; simpl; auto.
           ++ rewrite in_app_iff; right; simpl; left; auto.
           ++ rewrite in_app_iff; right; simpl; left; auto.
           ++ right; rewrite in_map_iff; exists (readReg, v); auto.
    + unfold WfRegMapExpr in *; dest.
      inv H; EqDep_subst; [|discriminate].
      specialize (SemRegExprVals H1 HSemRegMap) as TMP; inv TMP.
      assert (WfRegMapExpr (VarRegMap type
                                      (old0,
                                       (hd [] upds0 ++
                                           [(readReg,
                                             existT (fullType type) (SyntaxKind (Array num Data))
                                                    (evalExpr
                                                       (BuildArray
                                                          (fun i : Fin.t num =>
                                                             (Var type (SyntaxKind (Array idxNum Data)) regV @[
                                                                    Var type (SyntaxKind (Bit (Nat.log2_up idxNum))) (evalExpr idx) + Const type ($(proj1_sig (Fin.to_nat i)))%word])%kami_expr))))])
                                         :: tl upds0))
                           (old0,
                            (hd [] upds0 ++
                                [(readReg,
                                  existT (fullType type) (SyntaxKind (Array num Data))
                                         (evalExpr
                                            (BuildArray
                                               (fun i : Fin.t num =>
                                                  (Var type (SyntaxKind (Array idxNum Data)) regV @[
                                                         Var type (SyntaxKind (Bit (Nat.log2_up idxNum))) (evalExpr idx) + Const type ($(proj1_sig (Fin.to_nat i)))%word])%kami_expr))))])
                              :: tl upds0)) as P0.
      { unfold WfRegMapExpr in *; dest; split; auto; constructor. }
      specialize (IHea _ _ _ _ _ _ HoInitNoDups HuInitNoDups HPriorityUpds HConsistent P0 _ _ _ HSemCompActionT); dest; split; auto.
      exists (umUpd (readReg, existT (fullType type) (SyntaxKind (Array num Data))
                                   (evalExpr
                                      (BuildArray
                                         (fun i : Fin.t num =>
                                            (Var type (SyntaxKind (Array idxNum Data)) regV @[
                                                   Var type (SyntaxKind (Bit (Nat.log2_up idxNum))) (evalExpr idx) + Const type ($(proj1_sig (Fin.to_nat i)))%word])%kami_expr))))::x).
      repeat split; auto.
      * simpl in *.
        clear - H3.
        destruct (UpdOrMeths_RegsT x); auto.
        rewrite <- app_assoc in H3; simpl in *; assumption.
      * econstructor 15; eauto.
        -- rewrite H3 in H.
           rewrite HConsistent.
           clear - H.
           simpl in *.
           destruct (UpdOrMeths_RegsT x); simpl in *; specialize (H _ (or_introl eq_refl)); dest;
             apply H0; repeat rewrite map_app, in_app_iff; [right| left; right]; left; auto.
        -- inv HReadMap.
           apply (PriorityUpds_Equiv HoInitNoDups HuInitNoDups HUpdatedRegs HPriorityUpds); auto.
        -- rewrite H3 in H.
           clear - H.
           simpl in *.
           destruct (UpdOrMeths_RegsT x); simpl in *; specialize (H _ (or_introl eq_refl)); dest; repeat intro; auto.
           repeat rewrite map_app in H; simpl in *.
           rewrite NoDup_app_iff in H; dest.
           apply (H3 readReg); destruct H1; subst; simpl; auto.
           ++ rewrite in_app_iff; right; simpl; left; auto.
           ++ rewrite in_app_iff; right; simpl; left; auto.
           ++ right; rewrite in_map_iff; exists (readReg, v); auto.
  - inv H0; EqDep_subst.
    + apply (SemCompActionEEquivWMap _ _ _ (SemVarRegMap _) HWriteMap) in HSemCompActionT.
      specialize (H _ _ _ _ _ _ _ HoInitNoDups HuInitNoDups HPriorityUpds HConsistent WfMap _ _ _ HSemCompActionT); dest.
      split; auto.
      exists x.
      repeat split; auto.
      econstructor; eauto.
      * inv HReadMap.
        apply (PriorityUpds_Equiv HoInitNoDups HuInitNoDups HUpdatedRegs HPriorityUpds); auto.
      * inv HReadMap.
        apply (PriorityUpds_Equiv HoInitNoDups HuInitNoDups HUpdatedRegs HPriorityUpds); auto.
    + apply (SemCompActionEEquivWMap _ _ _ (SemVarRegMap _) HWriteMap) in HSemCompActionT.
      specialize (H _ _ _ _ _ _ _ HoInitNoDups HuInitNoDups HPriorityUpds HConsistent WfMap _ _ _ HSemCompActionT); dest.
      split; auto.
      exists x.
      repeat split; auto.
      econstructor 17; eauto.
      * inv HReadMap.
        apply (PriorityUpds_Equiv HoInitNoDups HuInitNoDups HUpdatedRegs HPriorityUpds); auto.
Qed.

Lemma ESemAction_NoDup_Upds k (ea : EActionT type k) :
  forall o uml retl,
    ESemAction o ea uml retl ->
    NoDup (map fst (UpdOrMeths_RegsT uml)).
Proof.
  induction ea; intros.
  - inv H0; EqDep_subst; simpl; eauto.
  - inv H0; EqDep_subst; simpl; eauto.
  - inv H0; EqDep_subst; simpl; eauto.
    rewrite UpdOrMeths_RegsT_app, map_app, NoDup_app_iff; repeat split; repeat intro; eauto.
    + specialize (HDisjRegs a); firstorder fail.
    + specialize (HDisjRegs a); firstorder fail.
  - inv H0; EqDep_subst; simpl; eauto.
  - inv H0; EqDep_subst; simpl; eauto.
  - inv H; EqDep_subst; simpl.
    constructor; eauto.
    intro; rewrite in_map_iff in H; dest; destruct x; subst; simpl in *.
    eapply HDisjRegs; eauto.
  - inv H0; EqDep_subst; rewrite UpdOrMeths_RegsT_app, map_app, NoDup_app_iff;
      repeat split; repeat intro; eauto; specialize (HDisjRegs a); firstorder fail.
  - inv H; EqDep_subst; simpl; eauto.
  - inv H; EqDep_subst; simpl; constructor.
  - inv H0; EqDep_subst; simpl; eauto.
  - inv H; EqDep_subst; simpl; constructor; eauto; intro;
      rewrite in_map_iff in H; dest; destruct x; subst; simpl in *; eapply HDisjRegs; eauto.
  - inv H; EqDep_subst; simpl; constructor; eauto; intro;
      rewrite in_map_iff in H; dest; destruct x; subst; simpl in *; eapply HDisjRegs; eauto.
  - inv H0; EqDep_subst; eauto.
Qed.


Lemma ESemAction_SubList_Upds k (ea : EActionT type k) :
  forall o uml retl,
    ESemAction o ea uml retl ->
    SubList (getKindAttr (UpdOrMeths_RegsT uml)) (getKindAttr o).
Proof.
  induction ea; intros.
  - inv H0; EqDep_subst; simpl; eauto.
  - inv H0; EqDep_subst; simpl; eauto.
  - inv H0; EqDep_subst; simpl; eauto.
    rewrite UpdOrMeths_RegsT_app, map_app, SubList_app_l_iff; split; eauto.
  - inv H0; EqDep_subst; simpl; eauto.
  - inv H0; EqDep_subst; simpl; eauto.
  - inv H; EqDep_subst; simpl.
    repeat intro; inv H; auto.
    eapply IHea; eauto.
  - inv H0; EqDep_subst; simpl; eauto;
      rewrite UpdOrMeths_RegsT_app, map_app, SubList_app_l_iff;
      split; eauto.
  - inv H; EqDep_subst; simpl; eauto.
  - inv H; EqDep_subst; simpl; repeat intro; contradiction.
  - inv H0; EqDep_subst; simpl; eauto.
  - inv H; EqDep_subst; simpl; eauto; repeat intro; inv H.
    + rewrite in_map_iff;
        exists (dataArray, existT (fullType type) (SyntaxKind (Array idxNum Data)) regV);
        split; auto.
    + eapply IHea; eauto.
    + rewrite in_map_iff;
        exists (dataArray, existT (fullType type) (SyntaxKind (Array idxNum Data)) regV);
        split; auto.
    + eapply IHea; eauto.
  - inv H; EqDep_subst; simpl; eauto; repeat intro; inv H; auto; eapply IHea; eauto.
  - inv H0; EqDep_subst; eauto.
Qed.

Lemma Extension_Compiles1  {k : Kind} (a : ActionT type k) :
  forall o calls retl expr v' bexpr,
    SemCompActionT (compileAction o a bexpr expr) v' calls retl ->
    SemCompActionT (EcompileAction o (Action_EAction a) bexpr expr) v' calls retl.
Proof.
  induction a; simpl; intros; auto.
  - inv H0; EqDep_subst; [econstructor| econstructor 2]; eauto.
  - inv H0; EqDep_subst; econstructor; auto.
  - inv H0; EqDep_subst; econstructor; eauto.
  - inv H0; EqDep_subst; econstructor; eauto.
  - inv H0; EqDep_subst; econstructor; eauto.
  - inv H; simpl in *; EqDep_subst; econstructor; eauto.
  - inv H0; simpl in *; EqDep_subst.
    inv HSemCompActionT; simpl in *; EqDep_subst.
    inv HSemCompActionT0; simpl in *; EqDep_subst.
    inv HSemCompActionT_cont; EqDep_subst.
    inv HSemCompActionT_cont0; simpl in *; EqDep_subst.
    repeat econstructor; eauto.
  - inv H; EqDep_subst; econstructor; eauto.
Qed.

Lemma Extension_Compiles2 {k : Kind} (a : ActionT type k) :
  forall o calls retl expr v' bexpr,
    SemCompActionT (EcompileAction o (Action_EAction a) bexpr expr) v' calls retl ->
    SemCompActionT (compileAction o a bexpr expr) v' calls retl.
Proof.
  induction a; simpl; intros; auto.
  - inv H0; EqDep_subst; [econstructor| econstructor 2]; eauto.
  - inv H0; EqDep_subst; econstructor; auto.
  - inv H0; EqDep_subst; econstructor; eauto.
  - inv H0; EqDep_subst; econstructor; eauto.
  - inv H0; EqDep_subst; econstructor; eauto.
  - inv H; simpl in *; EqDep_subst; econstructor; eauto.
  - inv H0; simpl in *; EqDep_subst.
    inv HSemCompActionT; simpl in *; EqDep_subst.
    inv HSemCompActionT0; simpl in *; EqDep_subst.
    inv HSemCompActionT_cont; EqDep_subst.
    inv HSemCompActionT_cont0; simpl in *; EqDep_subst.
    repeat econstructor; eauto.
  - inv H; EqDep_subst; econstructor; eauto.
Qed.

Corollary Extension_Compiles_iff  {k : Kind} (a : ActionT type k) :
  forall o calls retl expr v' bexpr,
    SemCompActionT (EcompileAction o (Action_EAction a) bexpr expr) v' calls retl <->
    SemCompActionT (compileAction o a bexpr expr) v' calls retl.
Proof.
  split; intro; eauto using Extension_Compiles1, Extension_Compiles2.
Qed.

Lemma FalseSemCompAction_Ext k (a : ActionT type k) :
  forall writeMap o old upds oInit uInit (bexpr : Bool @# type) m
         (HPriorityUpds : PriorityUpds oInit uInit o)
         (HConsistent : getKindAttr o = getKindAttr old)
         (WfMap : WfRegMapExpr writeMap (old, upds))
         (HRegConsist : getKindAttr o = getKindAttr (getRegisters m))
         (HWf : WfActionT (getRegisters m) a)
         (HFalse : evalExpr bexpr = false),
  exists retl,
    @SemCompActionT k (compileAction (oInit, uInit) a bexpr writeMap) (old, upds) nil retl.
Proof.
  induction a; simpl in *; intros.
  - inv HWf; EqDep_subst.
    specialize (H _ _ _ _ _ _ _ _ _ HPriorityUpds HConsistent WfMap HRegConsist (H2 (evalConstT (getDefaultConst (snd s)))) HFalse); dest.
    exists x.
    econstructor 2; eauto.
  - inv HWf; EqDep_subst.
    specialize (H _ _ _ _ _ _ _ _ _ HPriorityUpds HConsistent WfMap HRegConsist (H2 (evalExpr e)) HFalse); dest.
    exists x.
    econstructor; eauto.
  - inv HWf; EqDep_subst.
    specialize (IHa _ _ _ _ _ _ _ _ HPriorityUpds HConsistent WfMap HRegConsist H3 HFalse); dest.
    assert (WfRegMapExpr (VarRegMap type (old, upds)) (old, upds)) as P0.
    { unfold WfRegMapExpr in *; dest; split; auto. constructor. }
    specialize (H _ _ _ _ _ _ _ _ _ HPriorityUpds HConsistent P0 HRegConsist (H5 x) HFalse); dest.
    exists x0.
    econstructor; eauto.
    reflexivity.
  - inv HWf; EqDep_subst.
    specialize (H _ _ _ _ _ _ _ _ _ HPriorityUpds HConsistent WfMap HRegConsist (H2 (evalConstFullT (getDefaultConstFullKind k))) HFalse); dest.
    exists x.
    econstructor; eauto.
  - inv HWf; EqDep_subst.
    change (fun x0 : FullKind => RegInitValT x0) with RegInitValT in H5.
    rewrite <- HRegConsist in H5.
    rewrite in_map_iff in H5; dest; inv H0.
    destruct x, s0; simpl in *.
    specialize (H _ _ _ _ _ _ _ _ _ HPriorityUpds HConsistent WfMap HRegConsist (H3 f) HFalse); dest.
    exists x0.
    econstructor; eauto.
    constructor.
  - inv HWf; EqDep_subst.
    assert (WfRegMapExpr (VarRegMap type (old, upds)) (old, upds)) as P0.
    { unfold WfRegMapExpr in *; dest; split; auto; constructor. }
    specialize (IHa _ _ _ _ _ _ _ _ HPriorityUpds HConsistent P0 HRegConsist H2 HFalse); dest.
    exists x.
    econstructor; eauto.
    + econstructor; eauto.
      unfold WfRegMapExpr in *; dest; split; auto.
      * econstructor 3; auto.
    + reflexivity.
  - inv HWf; EqDep_subst.
    remember (evalExpr e) as e_val.
    assert (WfRegMapExpr (VarRegMap type (old, upds)) (old, upds)) as P0.
    { unfold WfRegMapExpr in *; dest; split; auto; constructor. }
    assert (evalExpr (bexpr && e)%kami_expr = false) as P1.
    { simpl; rewrite HFalse, andb_false_l; reflexivity. }
    assert (evalExpr (bexpr && !e)%kami_expr = false) as P2.
    { simpl; rewrite HFalse, andb_false_l; reflexivity. }
    specialize (IHa1 _ _ _ _ _ _ _ _ HPriorityUpds HConsistent WfMap HRegConsist H7 P1); dest.
    specialize (IHa2 _ _ _ _ _ _ _ _ HPriorityUpds HConsistent P0 HRegConsist H8 P2); dest.
    destruct e_val.
    + specialize (H _ _ _ _ _ _ _ _ _ HPriorityUpds HConsistent P0 HRegConsist (H4 x) HFalse); dest.
      exists x1.
      do 2 econstructor; eauto.
      econstructor; eauto using SemCompActionEquivBexpr; [reflexivity|].
      econstructor; eauto using SemCompActionEquivBexpr; [reflexivity|].
      econstructor; simpl; rewrite <- Heqe_val.
      assumption.
    + specialize (H _ _ _ _ _ _ _ _ _ HPriorityUpds HConsistent P0 HRegConsist (H4 x0) HFalse); dest.
      exists x1.
      do 2 econstructor; eauto.
      econstructor; eauto using SemCompActionEquivBexpr; [reflexivity|].
      econstructor; eauto using SemCompActionEquivBexpr; [reflexivity|].
      econstructor; simpl; rewrite <- Heqe_val.
      assumption.
  - inv HWf; EqDep_subst.
    specialize (IHa _ _ _ _ _ _ _ _ HPriorityUpds HConsistent WfMap HRegConsist H1 HFalse); dest.
    exists x.
    econstructor; eauto.
  - inv HWf; EqDep_subst.
    exists (evalExpr e).
    econstructor; eauto.
Qed.

Lemma ActionsEEquivWeak k a:
  forall writeMap o old upds oInit uInit m
         (HoInitNoDups : NoDup (map fst oInit))
         (HuInitNoDups : forall u, In u uInit -> NoDup (map fst u))
         (HPriorityUpds : PriorityUpds oInit uInit o)
         (HConsistent : getKindAttr o = getKindAttr old)
         (WfMap : WfRegMapExpr writeMap (old, upds))
         (HRegConsist : getKindAttr o = getKindAttr (getRegisters m))
         (HWf : WfActionT (getRegisters m) a),
  forall uml retl upds' calls,
    upds' = (old, match (UpdOrMeths_RegsT uml) with
                  |nil => upds
                  |_ :: _ => (hd nil upds ++ (UpdOrMeths_RegsT uml)) :: tl upds
                  end) ->
    calls = (UpdOrMeths_MethsT uml) ->
    DisjKey (hd nil upds) (UpdOrMeths_RegsT uml) ->
    ESemAction o (Action_EAction a) uml retl ->
    @SemCompActionT k (EcompileAction (oInit, uInit) (Action_EAction a) (Const type true) writeMap) upds' calls retl.
Proof.
  induction a; intros; subst; simpl in *.
  - inv H3; inv HWf; EqDep_subst; simpl.
    econstructor; eauto.
  - inv H3; inv HWf; EqDep_subst; simpl.
    econstructor; eauto.
  - specialize (ESemAction_NoDup_Upds H3) as P0;
      specialize (ESemAction_SubList_Upds H3) as P1.
    inv H3; inv HWf; EqDep_subst; rewrite UpdOrMeths_RegsT_app, UpdOrMeths_MethsT_app.
    econstructor; eauto.
    eapply IHa; eauto.
    + intro k0; specialize (H2 k0).
      rewrite UpdOrMeths_RegsT_app, map_app, in_app_iff in H2.
      destruct H2; auto.
    + eapply H; eauto.
      * unfold WfRegMapExpr; repeat split; [constructor| |]; unfold WfRegMapExpr in *; dest;
          rewrite UpdOrMeths_RegsT_app in *; destruct (UpdOrMeths_RegsT newUml); simpl in *.
        -- apply (H3 _ H0).
        -- destruct H0; subst; [rewrite map_app|]; simpl.
           ++ rewrite NoDup_app_iff; repeat split; repeat intro; auto.
              ** destruct upds; [constructor| simpl; apply (H3 _ (or_introl eq_refl))].
              ** rewrite map_app in P0; inv P0.
                 rewrite in_app_iff in H6.
                 rewrite NoDup_app_iff in H7; dest.
                 constructor; [firstorder fail|]; auto.
              ** specialize (H2 a1); simpl in *; rewrite map_app, in_app_iff in H2.
                 clear - H2 H0 H5.
                 firstorder fail.
              ** specialize (H2 a1); simpl in *; rewrite map_app, in_app_iff in H2.
                 clear - H2 H0 H5.
                 firstorder fail.
           ++ apply H3; clear - H0; destruct upds; simpl in *; auto.
        -- apply (H3 _ H0).
        -- destruct H0; subst; [rewrite map_app|]; simpl.
           ++ rewrite SubList_app_l_iff; split; repeat intro.
              ** destruct upds; simpl in *;
                   [contradiction| apply (H3 _ (or_introl eq_refl)); assumption].
              ** rewrite HConsistent in P1; apply P1; simpl in *.
                 rewrite map_app, in_app_iff.
                 clear - H0; firstorder fail.
           ++ eapply H3; destruct upds; simpl in *; eauto.
      * clear.
        destruct (UpdOrMeths_RegsT newUml); simpl; auto.
        destruct (UpdOrMeths_RegsT newUmlCont); simpl;
          [rewrite app_nil_r| rewrite <-app_assoc]; auto.
      * destruct (UpdOrMeths_RegsT newUml); simpl; auto.
        -- intro k0; specialize (H2 k0).
           rewrite UpdOrMeths_RegsT_app, map_app, in_app_iff in H2.
           clear - H2; firstorder fail.
        -- intro k0; specialize (H2 k0); specialize (HDisjRegs k0).
           clear - H2 HDisjRegs.
           rewrite UpdOrMeths_RegsT_app, map_app, in_app_iff in *; firstorder fail.
  - inv H3; inv HWf; EqDep_subst; econstructor; eauto.
  - inv H3; inv HWf; EqDep_subst; econstructor; eauto.
    constructor.
  - inv H2; inv HWf; EqDep_subst.
    unfold WfRegMapExpr in *; dest.
    econstructor; eauto.
    + econstructor; eauto.
      unfold WfRegMapExpr; split; eauto.
      * econstructor; eauto.
      * simpl; intros.
        destruct H2; subst; split.
        -- rewrite map_app,  NoDup_app_iff; repeat split; repeat intro; auto.
           ++ destruct upds; simpl; [constructor| apply (H0 _ (or_introl eq_refl))].
           ++ simpl; constructor; [intro; contradiction| constructor].
           ++ destruct H4; auto; subst.
              specialize (H1 r); simpl in *.
              clear - H1 H2; firstorder fail.
           ++ destruct H2; auto; subst.
              specialize (H1 r); simpl in *.
              clear - H1 H4; firstorder fail.
        -- rewrite map_app, SubList_app_l_iff; split; simpl.
           ++ repeat intro.
              destruct upds; [contradiction| apply (H0 _ (or_introl eq_refl))]; auto.
           ++ repeat intro; destruct H2;[subst |contradiction].
              rewrite HConsistent in HRegVal; assumption.
        -- destruct upds; [contradiction| apply (H0 _ (or_intror H2))].
        -- destruct upds; [contradiction| apply (H0 _ (or_intror H2))].
    + reflexivity.
    + simpl; eapply IHa; eauto.
      * split; [constructor| intros]; split.
        -- inv H2; simpl in *; [rewrite map_app, NoDup_app_iff; repeat split; repeat intro|].
           ++ destruct upds; [constructor| simpl; apply (H0 _ (or_introl eq_refl))].
           ++ simpl; repeat constructor; auto.
           ++ specialize (H1 a0); clear - H1 H2 H4; firstorder fail.
           ++ specialize (H1 a0); clear - H1 H2 H4; firstorder fail.
           ++ destruct upds; [inv H4| apply (H0 _ (or_intror _ H4))].
        -- inv H2; repeat intro; simpl in *.
           ++ rewrite map_app, in_app_iff in H2; simpl in H2.
              destruct H2; [ destruct upds; [contradiction|]| destruct H2; [|contradiction]];
                subst.
              ** apply (H0 _ (or_introl _ (eq_refl))); assumption.
              ** rewrite HConsistent in HRegVal; assumption.
           ++ destruct upds; [contradiction| apply (H0 _ (or_intror _ H4)); assumption].
      * simpl; destruct (UpdOrMeths_RegsT newUml); auto.
        rewrite <-app_assoc; reflexivity.
      * intro k0; simpl; rewrite map_app, in_app_iff.
        specialize (H1 k0); simpl in *.
        clear - H1 HDisjRegs.
        destruct H1; auto.
        destruct (string_dec r k0); subst.
        -- right; intro.
           rewrite in_map_iff in H0; dest; destruct x; subst; simpl in *.
           apply (HDisjRegs s0); assumption.
        -- left; intro; firstorder fail.
  - inv H3; inv HWf; EqDep_subst; do 2 econstructor;[econstructor|].
    + assert (evalExpr (Const type true) =
              evalExpr (Var type (SyntaxKind Bool)
                            (evalExpr (Const type true && e)%kami_expr))) as P0; auto.
      eapply SemCompActionEEquivBexpr; eauto.
      eapply IHa1 with (old := old) (o := o); auto.
      * apply WfMap.
      * apply HRegConsist.
      * assumption.
      * instantiate (1 := newUml1).
        intro; specialize (H2 k0); clear - H2; rewrite UpdOrMeths_RegsT_app, map_app, in_app_iff in H2; firstorder fail.
      * apply HEAction.
    + rewrite UpdOrMeths_MethsT_app; reflexivity.
    + assert (evalExpr (Const type true && !e)%kami_expr = false) as P0.
      { simpl; rewrite HTrue; reflexivity. }
      assert (WfRegMapExpr (VarRegMap type (old, match UpdOrMeths_RegsT newUml1 with
                                                 | [] => upds
                                                 | _ :: _ => (hd [] upds ++ UpdOrMeths_RegsT newUml1) :: tl upds
                                                 end))
                           (old, match UpdOrMeths_RegsT newUml1 with
                                 | [] => upds
                                 | _ :: _ => (hd [] upds ++ UpdOrMeths_RegsT newUml1) :: tl upds
                                 end)) as P1.
      { unfold WfRegMapExpr in *; dest; split; auto; [constructor|].
        intros; split.
        - specialize (ESemAction_NoDup_Upds HEAction) as P1.
          rewrite UpdOrMeths_RegsT_app in H2.
          destruct (UpdOrMeths_RegsT newUml1).
          + apply H1; auto.
          + inv H3; [| destruct upds; [contradiction| apply H1; right; assumption]].
            rewrite map_app, NoDup_app_iff; repeat split; auto.
            * destruct upds;[constructor| apply H1; left; reflexivity].
            * repeat intro; specialize (H2 a); rewrite map_app, in_app_iff in H2;clear - H2 H3 H4; firstorder fail.
            * repeat intro; specialize (H2 a); rewrite map_app, in_app_iff in H2;clear - H2 H3 H4; firstorder fail.
        - specialize (ESemAction_SubList_Upds HEAction) as P1.
          destruct (UpdOrMeths_RegsT newUml1).
          + apply H1; auto.
          + inv H3; [|destruct upds; [contradiction| apply H1; right; assumption]].
            repeat intro; rewrite map_app, in_app_iff in *; inv H3;[| rewrite HConsistent in *; auto].
            destruct upds; [contradiction|].
            apply (H1 r0 (in_eq _ _)); assumption.
      }
      specialize (FalseSemCompAction_Ext _ _ HPriorityUpds HConsistent P1 HRegConsist H13 P0) as P2; dest.
      rewrite <- Extension_Compiles_iff in H0.
      econstructor.
      * eapply SemCompActionEEquivBexpr with (bexpr1 := (Const type true && ! e)%kami_expr); eauto.
      * reflexivity.
      * rewrite UpdOrMeths_RegsT_app.
        econstructor; simpl; rewrite HTrue.
        eapply H; eauto.
        -- destruct (UpdOrMeths_RegsT newUml1); simpl; auto.
           destruct (UpdOrMeths_RegsT newUml2); [rewrite app_nil_r | rewrite app_comm_cons, app_assoc]; simpl; auto.
        -- rewrite UpdOrMeths_RegsT_app in *.
           destruct (UpdOrMeths_RegsT newUml1); simpl in *; auto.
           clear - H2 HDisjRegs.
           intro k; specialize (H2 k); specialize (HDisjRegs k); simpl in *; rewrite map_app, in_app_iff in *.
           firstorder fail.
    + assert (evalExpr (Const type true && e)%kami_expr = false) as P0.
      { simpl; rewrite HFalse; reflexivity. }
      specialize (FalseSemCompAction_Ext _ _ HPriorityUpds HConsistent WfMap HRegConsist H12 P0) as P2; dest.
      rewrite <- Extension_Compiles_iff in H0.
      econstructor 8; eauto.
      * eapply SemCompActionEEquivBexpr with (bexpr1 := (Const type true && e)%kami_expr);
          eauto.
      * reflexivity.
      * rewrite UpdOrMeths_RegsT_app, UpdOrMeths_MethsT_app.
        assert (WfRegMapExpr (VarRegMap type (old, upds)) (old, upds)) as P1.
        { unfold WfRegMapExpr in *; dest; split; auto; constructor. }
        econstructor; simpl.
        -- assert (evalExpr (Const type true) = evalExpr (Var type (SyntaxKind Bool)
                                                              (negb (evalExpr e)))) as P2.
           { simpl; rewrite HFalse; auto. }
           apply (SemCompActionEEquivBexpr _ _ _ _ _ P2).
           eapply IHa2 with (o := o) (old := old) (upds := upds) (uml := newUml1); eauto.
           clear - H2; intro k; specialize (H2 k); rewrite UpdOrMeths_RegsT_app, map_app, in_app_iff in H2.
           firstorder fail.
        -- reflexivity.
        -- econstructor; simpl; rewrite HFalse.
           eapply H with (upds := match UpdOrMeths_RegsT newUml1 with
                               | [] => upds
                               | _ :: _ => (hd [] upds ++ UpdOrMeths_RegsT newUml1) :: tl upds
                               end); eauto.
           ++ rewrite UpdOrMeths_RegsT_app in *.
              specialize (ESemAction_NoDup_Upds HEAction) as P3.
              specialize (ESemAction_SubList_Upds HEAction) as P4.
              unfold WfRegMapExpr in *; dest; split; [constructor| intros; split].
              ** destruct (UpdOrMeths_RegsT newUml1);[apply H6; assumption| inv H7; [| apply H6; destruct upds;[contradiction| right; assumption]]].
                 rewrite map_app, NoDup_app_iff; repeat split; repeat intro; auto.
                 --- destruct upds; [constructor| apply H6; left; reflexivity].
                 --- clear - H2 H7 H8; specialize (H2 a); rewrite map_app, in_app_iff in H2.
                     firstorder fail.
                 --- clear - H2 H7 H8; specialize (H2 a); rewrite map_app, in_app_iff in H2.
                     firstorder fail.
              ** destruct (UpdOrMeths_RegsT newUml1);[apply H6; assumption| inv H7; [| apply H6; destruct upds;[contradiction| right; assumption]]].
                 rewrite HConsistent in P4.
                 repeat intro; rewrite map_app, in_app_iff in H7; inv H7.
                 --- destruct upds; [contradiction|].
                     apply (H6 r0 (in_eq _ _)); assumption.
                 --- apply P4; assumption.
           ++ rewrite UpdOrMeths_RegsT_app in *.
              destruct (UpdOrMeths_RegsT newUml1); simpl in *; auto.
              destruct (UpdOrMeths_RegsT newUml2); simpl in *; [rewrite app_nil_r| rewrite <-app_assoc, app_comm_cons; simpl];auto.
           ++ rewrite UpdOrMeths_RegsT_app in *.
              destruct (UpdOrMeths_RegsT newUml1); simpl in *; auto.
              clear - H2 HDisjRegs.
              intro k; specialize (H2 k); specialize (HDisjRegs k); simpl in *; rewrite map_app, in_app_iff in *.
              firstorder fail.
  - inv H2; inv HWf; EqDep_subst; econstructor; eauto.
  - inv H2; inv HWf; EqDep_subst; econstructor; eauto.
Qed.

Corollary ECompCongruence k (ea : EActionT type k) (a : ActionT type k) :
  forall writeMap o old upds oInit uInit m
         (HoInitNoDups : NoDup (map fst oInit))
         (HuInitNoDups : forall u, In u uInit -> NoDup (map fst u))
         (HPriorityUpds : PriorityUpds oInit uInit o)
         (HConsistent : getKindAttr o = getKindAttr old)
         (WfMap : WfRegMapExpr writeMap (old, upds))
         (HRegConsist : getKindAttr o = getKindAttr (getRegisters m))
         (HWf : WfActionT (getRegisters m) a),
    (forall uml retl, ESemAction o ea uml retl -> ESemAction o (Action_EAction a) uml retl) ->
    forall upds' calls retl, 
      @SemCompActionT k (EcompileAction (oInit, uInit) ea (Const type true) writeMap) upds' calls retl ->
      @SemCompActionT k (EcompileAction (oInit, uInit) (Action_EAction a) (Const type true) writeMap) upds' calls retl.
Proof.
  intros.
  apply (EEquivActions _ HoInitNoDups HuInitNoDups HPriorityUpds HConsistent WfMap) in H0; dest.
  specialize (H _ _ H3).
  eapply ActionsEEquivWeak; eauto.
  rewrite H1 in H0; simpl in *.
  destruct (UpdOrMeths_RegsT x); [intro; right; intro; contradiction|].
  specialize (H0 _ (or_introl eq_refl)); dest; rewrite map_app, NoDup_app_iff in H0; dest.
  intro; specialize (H6 k0); specialize (H7 k0).
  destruct (in_dec string_dec k0 (map fst (hd [] upds))); auto.
Qed.

Lemma EquivActions k a:
  forall
    writeMap o old upds oInit uInit
    (HoInitNoDups : NoDup (map fst oInit))
    (HuInitNoDups : forall u, In u uInit -> NoDup (map fst u))
    (HPriorityUpds : PriorityUpds oInit uInit o)
    (HConsistent : getKindAttr o = getKindAttr old)
    (WfMap : WfRegMapExpr writeMap (old, upds)),
  forall calls retl upds',
    @SemCompActionT k (compileAction (oInit, uInit) a (Const type true) writeMap) upds' calls retl ->
    (forall u, In u (snd upds') -> NoDup (map fst u) /\ SubList (getKindAttr u) (getKindAttr old)) /\
    exists newRegs readRegs,
      upds' = (old, match newRegs with
                    |nil => upds
                    |_ :: _ => (hd nil upds ++ newRegs) :: tl upds
                    end) /\
      SemAction o a readRegs newRegs calls retl.
Proof.
  induction a; subst; intros; simpl in *.
  - inv H0; EqDep_subst;[|discriminate].
    specialize (H _ _ _ _ _ _ _ HoInitNoDups HuInitNoDups HPriorityUpds HConsistent WfMap _ _ _ HSemCompActionT); dest; split; auto.
    exists x, x0; split; auto.
    econstructor; eauto.
  - inv H0; EqDep_subst.
    specialize (H _ _ _ _ _ _ _ HoInitNoDups HuInitNoDups HPriorityUpds HConsistent WfMap _ _ _ HSemCompActionT); dest; split; auto.
    exists x, x0; split; auto.
    econstructor; eauto.
  - inv H0; EqDep_subst.
    specialize (IHa _ _ _ _ _ _ HoInitNoDups HuInitNoDups HPriorityUpds HConsistent WfMap _ _ _ HSemCompActionT_a); dest.
    assert (WfRegMapExpr (VarRegMap type regMap_a) regMap_a) as WfMap0.
    { unfold WfRegMapExpr; split;[econstructor|].
      destruct regMap_a; inv H1; intros.
      apply (H0 _ H1).
    }
    rewrite H1 in *.
    specialize (H _ _ _ _ _ _ _ HoInitNoDups HuInitNoDups HPriorityUpds HConsistent WfMap0 _ _ _ HSemCompActionT_cont); dest.
    split; auto.
    exists (x++x1), (x0++x2); split.
    + destruct x1; simpl in *; auto.
      * rewrite app_nil_r; assumption.
      * destruct x; simpl in *; auto.
        rewrite app_comm_cons, app_assoc; assumption.
    + econstructor; eauto.
      rewrite H3 in H; simpl in *.
      clear - H.
      destruct x, x1; eauto using DisjKey_nil_r, DisjKey_nil_l; simpl in *.
      specialize (H _ (or_introl _ eq_refl)); simpl in *; dest.
      repeat rewrite map_app in H.
      intro k.
      destruct (In_dec string_dec k (map fst (p0::x1))); auto.
      left; intro.
      destruct (NoDup_app_Disj string_dec _ _ H k); auto.
      apply H2; rewrite in_app_iff; right; auto.
  - inv H0; EqDep_subst.
    specialize (H _ _ _ _ _ _ _ HoInitNoDups HuInitNoDups HPriorityUpds HConsistent WfMap _ _ _ HSemCompActionT); dest; split; auto.
    exists x, x0; split; auto.
    econstructor; eauto.
  - inv H0; EqDep_subst.
    specialize (H _ _ _ _ _ _ _ HoInitNoDups HuInitNoDups HPriorityUpds HConsistent WfMap _ _ _ HSemCompActionT); dest; split; auto.
    exists x, ((r, existT _ k regVal) :: x0).
    split; auto.
    econstructor; eauto.
    inv HReadMap.
    apply (PriorityUpds_Equiv HoInitNoDups HuInitNoDups HUpdatedRegs HPriorityUpds); auto.
  - inv H; simpl in *; EqDep_subst.
    rewrite (unifyWO val_a) in HSemCompActionT_a.
    inv HSemCompActionT_a; EqDep_subst.
    destruct HRegMapWf, WfMap, regMap_a.
    inv H;[|discriminate]; EqDep_subst.
    specialize (SemRegExprVals H1 HSemRegMap) as P0; inv P0.
    assert (WfRegMapExpr (VarRegMap type (r0, (hd nil upds0 ++ (r, existT (fullType type) k (evalExpr e)) :: nil) :: tl upds0))
                         (r0, (hd nil upds0 ++ (r, existT (fullType type) k (evalExpr e)) :: nil) :: tl upds0)) as WfMap0.
    { split; auto. constructor. }
    specialize (IHa _ _ _ _ _ _ HoInitNoDups HuInitNoDups HPriorityUpds HConsistent WfMap0 _ _ _ HSemCompActionT_cont);
      dest; simpl in *; split; auto.
    exists ((r, existT (fullType type) k (evalExpr e)) :: nil ++ x), x0; split.
    + destruct x; simpl in *; auto.
      rewrite <- app_assoc in H3. rewrite <-app_comm_cons in H3.
      simpl in H3; auto.
    + rewrite H3 in H; simpl in *; destruct x; econstructor; eauto; simpl in *; specialize (H _ (or_introl _ eq_refl)); dest.
      * rewrite map_app, <-HConsistent in H6; simpl in *.
        apply (H6 (r, k)).
        rewrite in_app_iff; right; left; reflexivity.
      * repeat intro; inv H7.
      * rewrite map_app, <-HConsistent in H6; simpl in *.
        apply (H6 (r, k)).
        rewrite map_app; repeat rewrite in_app_iff; simpl; auto.
      * repeat intro.
        repeat rewrite map_app in H; simpl in *.
        destruct H7; subst; destruct (NoDup_app_Disj string_dec _ _ H r) as [P0|P0]; apply P0.
        -- rewrite in_app_iff; simpl; auto.
        -- simpl; auto.
        -- rewrite in_app_iff; simpl; auto.
        -- simpl; right; rewrite in_map_iff.
           exists (r, v); simpl; auto.
  - inv H0; simpl in *; EqDep_subst.
    inv HSemCompActionT; simpl in *; EqDep_subst.
    inv HSemCompActionT0; simpl in *; EqDep_subst.
    inv HSemCompActionT_cont; EqDep_subst.
    inv HSemCompActionT_cont0; EqDep_subst.
    remember (evalExpr e) as P0.
    apply Eqdep.EqdepTheory.inj_pair2 in H4.
    rewrite H4 in *.
    clear H4; simpl in *.
    destruct P0; rewrite <- HeqP0 in *; simpl in *.
    + assert (evalExpr (Var type (SyntaxKind Bool) true) = evalExpr (Const type true)) as P4; auto.
      assert (evalExpr (Var type (SyntaxKind Bool) false) = false) as P5; auto.
      specialize (SemCompActionEquivBexpr _ _ _ _ _ P4 HSemCompActionT_a) as P6.
      specialize (IHa1 _ _ _ _ _ _ HoInitNoDups HuInitNoDups HPriorityUpds HConsistent WfMap _ _ _ P6); dest.
      destruct (predFalse_UpdsNil _ _ _ _ P5 (SemVarRegMap regMap_a) HSemCompActionT_a0).
      assert (WfRegMapExpr (VarRegMap type regMap_a0) regMap_a0) as P7.
      { unfold WfRegMapExpr; split; [constructor|]. subst; eauto. }
      rewrite <- H3 in P7 at 2.
      rewrite H1 in P7.
      specialize (H _ _ _ _ _ _ _ HoInitNoDups HuInitNoDups HPriorityUpds HConsistent P7 _ _ _ HSemCompActionT); dest.
      split; auto.
      exists (x++x1), (x0++x2).
      destruct x; simpl; split; auto.
      * rewrite H4.
        econstructor; eauto.
        apply DisjKey_nil_l.
      * destruct x1; [rewrite app_nil_r|]; simpl in *; auto.
        rewrite <-app_assoc, <-app_comm_cons in H5; assumption.
      * rewrite H4; simpl.
        econstructor; eauto.
        rewrite H5 in H; simpl in *.
        clear - H.
        destruct x1; simpl in *; [apply DisjKey_nil_r|].
        specialize (H _ (or_introl _ (eq_refl))); dest.
        rewrite map_app in H.
        intro.
        destruct (NoDup_app_Disj string_dec _ _ H k); auto.
        left; intro; apply H1.
        rewrite map_app, in_app_iff; auto.
    + assert (evalExpr (Var type (SyntaxKind Bool) true) = evalExpr (Const type true)) as P4; auto.
      assert (evalExpr (Var type (SyntaxKind Bool) false) = false) as P5; auto.
      specialize (SemCompActionEquivBexpr _ _ _ _ _ P4 HSemCompActionT_a0) as P6.
      remember WfMap as WfMap0.
      inv WfMap0.
      destruct (predFalse_UpdsNil _ _ _ _ P5 H0 HSemCompActionT_a).
      assert (WfRegMapExpr (VarRegMap type regMap_a) (old, upds)) as WfMap0.
      { rewrite <- H2.
        clear - WfMap.
        unfold WfRegMapExpr in *; dest; repeat split;[constructor| |]; eapply H0; eauto.
      }
      specialize (IHa2 _ _ _ _ _ _ HoInitNoDups HuInitNoDups HPriorityUpds HConsistent WfMap0 _ _ _ P6); dest.
      assert (WfRegMapExpr (VarRegMap type regMap_a0) regMap_a0) as P7.
      { unfold WfRegMapExpr; split; [constructor|]. subst; eauto. }
      rewrite  H5 in P7 at 2.
      specialize (H _ _ _ _ _ _ _ HoInitNoDups HuInitNoDups HPriorityUpds HConsistent P7 _ _ _ HSemCompActionT); dest.
      split; auto.
      exists (x++x1), (x0++x2).
      destruct x; simpl; split; auto.
      * rewrite H3; simpl.
        econstructor 8; eauto.
        apply DisjKey_nil_l.
      * destruct x1;[rewrite app_nil_r|]; simpl in *; auto.
        rewrite <-app_assoc, <-app_comm_cons in H7; assumption.
      * rewrite H3; simpl.
        econstructor 8; eauto.
        rewrite H7 in H; simpl in *.
        clear - H.
        destruct x1; simpl in *; [apply DisjKey_nil_r|].
        specialize (H _ (or_introl _ (eq_refl))); dest.
        rewrite map_app in H.
        intro.
        destruct (NoDup_app_Disj string_dec _ _ H k); auto.
        left; intro; apply H1.
        rewrite map_app, in_app_iff; auto.
  - inv H; EqDep_subst.
    specialize (IHa _ _ _ _ _ _ HoInitNoDups HuInitNoDups HPriorityUpds HConsistent WfMap _ _ _ HSemCompActionT); dest; split; auto.
    exists x, x0.
    split; auto.
    econstructor; eauto.
  - inv H; EqDep_subst.
    inv WfMap; inv HRegMapWf.
    specialize (SemRegExprVals H H1) as TMP; subst; simpl in *.
    split; auto.
    exists nil, nil.
    split; auto.
    constructor; auto.
Qed.

Lemma SameOldAction (k : Kind) (a : ActionT type k) :
  forall oInit uInit writeMap old upds wOld wUpds calls retl bexpr
         (HSemRegMap : SemRegMapExpr writeMap (wOld, wUpds)),
    @SemCompActionT k (compileAction (oInit, uInit) a bexpr writeMap) (old, upds) calls retl ->
    wOld = old.
Proof.
  induction a; intros; simpl in *.
  - inv H0; EqDep_subst; simpl in *; eapply H; eauto.
  - inv H0; EqDep_subst; simpl in *.
    eapply H; eauto.
  - inv H0; EqDep_subst; simpl in *.
    destruct regMap_a.
    specialize (H _ _ _ _ _ _ _ _ _ _ _ (SemVarRegMap _) HSemCompActionT_cont); subst.
    specialize (IHa _ _ _ _ _ _ _ _ _ _ HSemRegMap HSemCompActionT_a); assumption.
  - inv H0; EqDep_subst; simpl in *.
    eapply H; eauto.
  - inv H0; EqDep_subst; simpl in *.
    eapply H; eauto.
  - inv H; simpl in *; EqDep_subst.
    rewrite (unifyWO val_a) in HSemCompActionT_a.
    inv HSemCompActionT_a; EqDep_subst.
    destruct regMap_a; unfold WfRegMapExpr in *; dest.
    inv H; EqDep_subst.
    + specialize (IHa _ _ _ _ _ _ _ _ _ _ (SemVarRegMap _) HSemCompActionT_cont).
      specialize (SemRegExprVals HSemRegMap HSemRegMap0) as TMP; inv TMP.
      reflexivity.
    + specialize (IHa  _ _ _ _ _ _ _ _ _ _ (SemVarRegMap _) HSemCompActionT_cont).
      specialize (SemRegExprVals HSemRegMap HSemRegMap0) as TMP; inv TMP.
      reflexivity.
  - inv H0; simpl in *; EqDep_subst.
    inv HSemCompActionT; simpl in *; EqDep_subst.
    inv HSemCompActionT0; simpl in *; EqDep_subst.
    inv HSemCompActionT_cont; EqDep_subst.
    inv HSemCompActionT_cont0; simpl in *; EqDep_subst.
    destruct regMap_a, regMap_a0.
    specialize (H _ _ _ _ _ _ _ _ _ _ _ (SemVarRegMap _) HSemCompActionT).
    simpl in *.
    specialize (IHa1 _ _ _ _ _ _ _ _ _ _ HSemRegMap HSemCompActionT_a).
    specialize (IHa2 _ _ _ _ _ _ _ _ _ _ (SemVarRegMap _) HSemCompActionT_a0).
    subst; reflexivity.
  - inv H; EqDep_subst; simpl in *.
    eapply IHa; eauto.
  - inv H; EqDep_subst.
    unfold WfRegMapExpr in *; dest.
    specialize (SemRegExprVals H HSemRegMap) as TMP; inv TMP.
    reflexivity.
Qed.

Lemma SameOldActions o la:
  forall old upds calls retl,
    @SemCompActionT Void (compileActions (o, nil) (rev la)) (old, upds)  calls retl ->
    o = old.
Proof.
  induction la; simpl in *; intros.
  rewrite (unifyWO retl) in H.
  inv H; EqDep_subst.
  inv HRegMapWf.
  inv H.
  reflexivity.
  - unfold compileActions in *; simpl in *.
    setoid_rewrite <- fold_left_rev_right in IHla.
    rewrite <- fold_left_rev_right in *.
    rewrite rev_app_distr, rev_involutive in *; simpl in *.
    rewrite (unifyWO retl) in H.
    inv H; simpl in *; EqDep_subst.
    rewrite (unifyWO WO) in HSemCompActionT_cont.
    inv HSemCompActionT_cont; simpl in *; EqDep_subst.
    rewrite (unifyWO val_a0) in HSemCompActionT_a0.
    inv HSemCompActionT_a0; EqDep_subst.
    destruct regMap_a.
    specialize (IHla _ _ _ _ HSemCompActionT_a); subst.
    destruct regMap_a0.
    inv HRegMapWf; inv H; inv HSemRegMap.
    apply (SameOldAction _ _ _ _ (SemVarRegMap _) HSemCompActionT_cont0).
Qed.

Lemma SameOldLoop (m : BaseModule) o:
  forall rules old upds calls retl,
    @SemCompActionT Void (compileRules type (o, nil) (rev rules)) (old, upds) calls retl ->
    o = old.
Proof.
  induction rules; simpl in *; intros.
  - rewrite (unifyWO retl) in H.
    inv H; EqDep_subst.
    inv HRegMapWf.
    inv H.
    reflexivity.
  - unfold compileRules, compileActions in *; simpl in *.
    setoid_rewrite <- fold_left_rev_right in IHrules.
    rewrite map_app, <- fold_left_rev_right, map_rev in *.
    simpl in *.
    rewrite rev_app_distr, rev_involutive in *; simpl in *.
    rewrite (unifyWO retl) in H.
    inv H; EqDep_subst.
    apply Eqdep.EqdepTheory.inj_pair2 in H4; subst; simpl in *.
    destruct regMap_a.
    specialize (IHrules _ _ _ _ HSemCompActionT_a); subst.
    rewrite (unifyWO WO) in HSemCompActionT_cont.
    inv HSemCompActionT_cont; simpl in *; EqDep_subst.
    rewrite (unifyWO val_a0) in HSemCompActionT_a0.
    inv HSemCompActionT_a0; simpl in *; EqDep_subst.
    destruct regMap_a; inv HRegMapWf; inv H; inv HSemRegMap.
    apply (SameOldAction _ _ _ _ (SemVarRegMap _) HSemCompActionT_cont0).
Qed.

Lemma EquivLoop (m : BaseModule) o:
  forall rules upds calls retl ls
         (HoInitNoDups : NoDup (map fst o))
         (HTrace : Trace m o ls)
         (HNoSelfCalls : NoSelfCallBaseModule m),
    SubList rules (getRules m) ->
    @SemCompActionT Void (compileRules type (o, nil) (rev rules)) (o, upds) calls retl ->
    (forall u, In u upds -> (NoDup (map fst u)) /\ SubList (getKindAttr u) (getKindAttr o)) /\
    exists o' (ls' : list (list FullLabel)),
      PriorityUpds o upds o' /\
      upds = (map getLabelUpds ls') /\
      (map Rle (map fst rules)) = getLabelExecs (concat ls') /\
      calls = concat (map getLabelCalls (rev ls')) /\
      Trace m o' (ls' ++ ls).
Proof.
  induction rules; simpl in *; intros.
  - rewrite (unifyWO retl) in H0.
    inv H0; EqDep_subst.
    unfold WfRegMapExpr in *; dest.
    inv H0; split; auto.
    exists o, nil; repeat split; auto.
    constructor.
  - unfold compileRules, compileActions in *; simpl in *.
    rewrite map_app in *.
    rewrite <- fold_left_rev_right in *.
    rewrite map_rev in *.
    simpl in *.
    rewrite rev_app_distr in H0.
    rewrite rev_involutive in *.
    simpl in *.
    rewrite (unifyWO retl) in H0.
    inv H0; simpl in *; EqDep_subst.
    destruct (SubList_cons H) as [TMP P0]; clear TMP.
    destruct regMap_a.
    rewrite (unifyWO WO) in HSemCompActionT_cont.
    inv HSemCompActionT_cont; simpl in *; EqDep_subst.
    rewrite (unifyWO val_a0) in HSemCompActionT_a0.
    inv HSemCompActionT_a0; simpl in *; EqDep_subst.
    destruct regMap_a.
    specialize HRegMapWf as HRegMapWf0.
    inv HRegMapWf; inv H0; inv HSemRegMap.
    specialize (SameOldAction _ _ _ _ (SemVarRegMap _) HSemCompActionT_cont0) as TMP; subst.
    specialize (IHrules _ _ _ _ HoInitNoDups HTrace HNoSelfCalls P0 HSemCompActionT_a); dest.
    rewrite <-CompactPriorityUpds_iff in H2; auto.
    assert (forall u, In u (nil :: upds0) -> NoDup (map fst u)) as P1.
    { intros.
      destruct (H1 _ H8); auto.
    }
    assert (WfRegMapExpr (VarRegMap type (o, nil :: upds0)) (o, nil::upds0)) as P2.
    { clear - HRegMapWf0.
      unfold WfRegMapExpr in *; dest; split; auto.
      constructor.
    }
    specialize (EquivActions _ HoInitNoDups P1 H2 (eq_sym (prevPrevRegsTrue H2))
                             P2 HSemCompActionT_cont0) as TMP; dest.
    split; auto; simpl in *.
    assert (upds = (x1::upds0)) as P4.
    { inv H9. destruct x1; auto. }
    clear H9; subst.
    exists (doUpdRegs x1 x), (((x1, (Rle (fst a), calls_cont0))::nil)::x0).
    unfold getLabelCalls, getLabelUpds in *; simpl in *.
    rewrite app_nil_r.
    repeat split; auto.
    + econstructor 2 with (u := x1); auto.
      * rewrite CompactPriorityUpds_iff in H2; auto.
        apply H2.
      * specialize (H8 _ (or_introl eq_refl)); dest.
        rewrite (prevPrevRegsTrue H2).
        apply getKindAttr_doUpdRegs; eauto.
        -- rewrite <- (getKindAttr_map_fst _ _ (prevPrevRegsTrue H2)).
           assumption.
        -- intros.
           rewrite <- (prevPrevRegsTrue H2).
           apply H5.
           rewrite in_map_iff.
           exists (s, v); simpl; split; auto.
      * repeat intro.
        rewrite (getKindAttr_map_fst _ _ (prevPrevRegsTrue H2)) in HoInitNoDups.
        specialize (H8 _ (or_introl eq_refl)); dest.
        rewrite (prevPrevRegsTrue H2) in H8.
        specialize (doUpdRegs_UpdRegs _ (HoInitNoDups) _ H8) as P4.
        unfold UpdRegs in P4; dest.
        specialize (H11 _ _ H3); dest.
        destruct H11; dest.
        -- inv H11; auto.
           inv H13.
        -- right; split; auto.
           intro; apply H11.
           exists x1; split; simpl; auto.
    + apply f_equal; assumption.
    + repeat rewrite map_app; simpl.
      repeat rewrite concat_app; simpl.
      repeat rewrite app_nil_r.
      reflexivity.
    + destruct a; simpl in *.
      econstructor 2.
      * apply H7.
      * enough (Step m x ((x1, (Rle s, calls_cont0))::nil)) as P3.
        { apply P3. }
        econstructor.
        -- econstructor 2; eauto; specialize (Trace_sameRegs HTrace) as TMP; simpl in *.
           ++ rewrite <- TMP, (prevPrevRegsTrue H2); reflexivity.
           ++ apply H; left; simpl; reflexivity.
           ++ rewrite <- TMP, (prevPrevRegsTrue H2).
              apply SubList_map, (SemActionReadsSub H10).
           ++ specialize (H8 _ (or_introl eq_refl)); dest.
              rewrite <- TMP, (prevPrevRegsTrue H2).
              apply (SemActionUpdSub H10).
           ++ intros; inv H3.
           ++ intros; inv H3.
           ++ econstructor.
              rewrite <- TMP.
              apply (eq_sym (prevPrevRegsTrue H2)).
        -- unfold MatchingExecCalls_Base; intros.
           specialize (getNumExecs_nonneg f [(x1, (Rle s, calls_cont0))]) as P3.
           unfold getNumCalls; simpl.
           rewrite getNumFromCalls_app; simpl.
           erewrite NoSelfCallRule_Impl; eauto.
           ++ apply H; apply in_eq.
           ++ apply H10.
      * simpl.
        apply doUpdRegs_enuf; auto.
        -- apply getKindAttr_doUpdRegs; auto.
           ++ rewrite <-(getKindAttr_map_fst _ _ (prevPrevRegsTrue H2)); assumption.
           ++ intros.
              specialize (H8 _ (or_introl (eq_refl))); dest.
              rewrite <-(prevPrevRegsTrue H2).
              apply H8.
              rewrite in_map_iff.
              exists (s0, v); auto.
      * reflexivity.
Qed.

Corollary EquivLoop' {m : BaseModule} {o ls rules upds calls retl}
          (HTrace : Trace m o ls) (HRegsWf : NoDup (map fst (getRegisters m)))
          (HNoSelfCalls : NoSelfCallBaseModule m) (HValidSch : SubList rules (getRules m)):
  @SemCompActionT Void (compileRules type (o, nil) rules) (o, upds) calls retl ->
  (forall u, In u upds -> (NoDup (map fst u)) /\ SubList (getKindAttr u) (getKindAttr o)) /\
  exists o' (ls' : list (list FullLabel)),
    PriorityUpds o upds o' /\
    upds = (map getLabelUpds ls') /\
    (map Rle (map fst (rev rules))) = getLabelExecs (concat ls') /\
    calls = concat (map getLabelCalls (rev ls')) /\
    Trace m o' (ls' ++ ls).
Proof.
  specialize (Trace_NoDup HTrace HRegsWf) as HoInitNoDups.
  rewrite <- (rev_involutive rules) at 1.
  assert (SubList (rev rules) (getRules m)) as P0.
  { repeat intro; apply HValidSch; rewrite in_rev; assumption. }
  eapply EquivLoop; eauto.
Qed.

Lemma PriorityUpds_glue upds1 :
  forall o1 o1',
    (forall u, In u upds1 -> SubList (getKindAttr u) (getKindAttr o1)) ->
    PriorityUpds o1 upds1 o1' ->
    forall upds2 o2 o2', 
      (forall u, In u upds2 -> SubList (getKindAttr u) (getKindAttr o2)) ->
      PriorityUpds o2 upds2 o2' ->
      DisjKey o1 o2 ->
      PriorityUpds (o1++o2) (upds1++upds2) (o1'++o2').
Proof.
  induction upds1.
  - simpl.
    induction upds2; intros.
    + inv H2; inv H0; [constructor 1 |discriminate| |discriminate]; discriminate.
    + inv H2; inv H0; inv HFullU;[|discriminate].
      econstructor 2.
      * eapply IHupds2; eauto.
        intros; eapply H1.
        right; assumption.
      * repeat rewrite map_app; rewrite currRegsTCurr.
        reflexivity.
        
      * intros.
        rewrite in_app_iff in H0; destruct H0.
        -- right; split.
           ++ intro.
              specialize (H1 _ (or_introl eq_refl)).
              rewrite in_map_iff in H2; dest; subst.
              specialize (H1 _ (in_map (fun x => (fst x, projT1 (snd x))) _ _ H4)).
              destruct (H3 (fst x)).
              ** apply H2.
                 rewrite in_map_iff.
                 exists (fst x, v); split; auto.
              ** apply H2.
                 apply (in_map fst) in H1; simpl in *.
                 rewrite fst_getKindAttr in H1; assumption.
           ++ rewrite in_app_iff; left ; assumption.
        -- destruct (Hcurr _ _ H0); [left; apply H2|right; dest; split; auto].
           rewrite in_app_iff; right; assumption.
      * reflexivity.
  - intros; simpl.
    inv H0; inv HFullU.
    econstructor 2 with (prevUpds := prevUpds ++ upds2) (u := u) (prevRegs := prevRegs ++ o2').
    + eapply IHupds1; eauto.
      intros; apply (H _ (or_intror H0)).
    + repeat rewrite map_app; rewrite currRegsTCurr, (prevPrevRegsTrue H2).
      reflexivity.
    + intros; rewrite in_app_iff in H0.
      destruct H0.
      * specialize (Hcurr _ _ H0).
        destruct Hcurr; auto.
        dest; right; split; auto.
        rewrite in_app_iff; left; assumption.
      * right; split.
        -- intro.
           rewrite in_map_iff in H4; dest; subst.
           specialize (H _ (or_introl eq_refl)
                         _ (in_map (fun x => (fst x, projT1 (snd x))) _ _ H5)).
           apply (in_map fst) in H0; simpl in *.
           apply (in_map fst) in H; rewrite fst_getKindAttr in H; simpl in *.
           destruct (H3 (fst x)); eauto.
           rewrite  (getKindAttr_map_fst _ _ (prevPrevRegsTrue H2)) in H4; contradiction.
        -- rewrite in_app_iff; auto.
    + reflexivity.
Qed.          

Lemma PriorityUpds_exist o (HNoDup : NoDup (map fst o)):
  forall upds
         (HUpdsCorrect : forall u, In u upds
                                   -> SubList (getKindAttr u) (getKindAttr o))
         (HNoDupUpds : forall u, In u upds -> NoDup (map fst u)),
  exists o',
    PriorityUpds o upds o'.
Proof.
  induction upds.
  - exists o.
    constructor.
  - intros.
    assert (forall u, In u upds -> SubList (getKindAttr u) (getKindAttr o)) as P0.
    { intros; apply HUpdsCorrect; simpl; eauto. }
    assert (forall u, In u upds -> NoDup (map fst u)) as P1.
    { intros; specialize (HNoDupUpds _ (or_intror H)); assumption. }
    specialize (IHupds P0 P1); dest.
    exists (doUpdRegs a x).
    rewrite (getKindAttr_map_fst _ _ (prevPrevRegsTrue H)) in HNoDup.
    rewrite (prevPrevRegsTrue H) in HUpdsCorrect.
    specialize (doUpdRegs_UpdRegs _ HNoDup _
                                  (HUpdsCorrect _ (or_introl eq_refl))) as P2.
    unfold UpdRegs in P2; dest.
    econstructor; auto.
    + apply H.
    + rewrite (prevPrevRegsTrue H).
      assumption.
    + intros.
      specialize (H1 _ _ H2).
      destruct H1; dest.
      * destruct H1; subst; auto.
        contradiction.
      * right; split; auto.
        intro; apply H1.
        exists a; split; auto.
        left; reflexivity.
Qed.

Section ESemAction_meth_collector.
  
  Variable f : DefMethT.
  Variable o : RegsT.
  
  Inductive ESemAction_meth_collector : UpdOrMeths -> UpdOrMeths -> Prop :=
  | NilUml : ESemAction_meth_collector nil nil
  | ConsUpd  um uml uml' newUml newUml' upd
             (HUpd : um = umUpd upd)
             (HDisjRegs : key_not_In (fst upd) (UpdOrMeths_RegsT newUml))
             (HUmlCons : uml' = um :: uml)
             (HnewUmlCons : newUml' = um :: newUml)
             (HCollector : ESemAction_meth_collector uml newUml):
      ESemAction_meth_collector uml' newUml'
  | ConsCallsNStr um uml uml' newUml newUml' meth
                  (HMeth : um = umMeth meth)
                  (HIgnore : fst meth <> fst f)
                  (HUmlCons : uml' = um :: uml)
                  (HnewUmlCons : newUml' = um :: newUml)
                  (HCollector : ESemAction_meth_collector uml newUml):
      ESemAction_meth_collector uml' newUml'
  | ConsWrCallsNSgn um uml uml' newUml newUml' meth
                    (HMeth : um = umMeth meth)
                    (HIgnore : projT1 (snd meth) <> projT1 (snd f))
                    (HUmlCons : uml' = um :: uml)
                    (HnewUmlCons : newUml' = um :: newUml)
                    (HCollector : ESemAction_meth_collector uml newUml):
      ESemAction_meth_collector uml' newUml'
  | ConsWrFCalls  um fUml uml uml' newUml newUml' argV retV
                  (HMeth : um = umMeth (fst f, (existT _ (projT1 (snd f)) (argV, retV))))
                  (HESemAction : ESemAction o (Action_EAction (projT2 (snd f) type argV)) fUml retV)
                  (HDisjRegs : DisjKey (UpdOrMeths_RegsT fUml) (UpdOrMeths_RegsT newUml))
                  (HUmlCons : uml' = um :: uml)
                  (HnewUmlApp : newUml' = fUml ++ newUml)
                  (HCollector : ESemAction_meth_collector uml newUml):
      ESemAction_meth_collector uml' newUml'.

  Lemma ESemActionMC_Upds_SubList (uml : UpdOrMeths) :
    forall newUml,
      ESemAction_meth_collector uml newUml ->
      SubList (UpdOrMeths_RegsT uml) (UpdOrMeths_RegsT newUml).
  Proof.
    induction uml; repeat intro.
    - inv H0.
    - simpl in H0.
      destruct a.
      + inv H; inv HUmlCons; simpl.
        inv H0; auto.
        right; eapply IHuml; eauto.
      + inv H; inv HUmlCons; simpl; auto.
        * eapply IHuml; eauto.
        * eapply IHuml; eauto.
        * rewrite UpdOrMeths_RegsT_app, in_app_iff; right.
          eapply IHuml; eauto.
  Qed.
  
  Lemma ESemAction_meth_collector_break (uml1 : UpdOrMeths) :
    forall uml2 newUml,
      ESemAction_meth_collector (uml1 ++ uml2) newUml ->
      exists newUml1 newUml2,
        newUml = newUml1 ++ newUml2 /\
        DisjKey (UpdOrMeths_RegsT newUml1) (UpdOrMeths_RegsT newUml2) /\
        ESemAction_meth_collector uml1 newUml1 /\
        ESemAction_meth_collector uml2 newUml2.
  Proof.
    induction uml1; simpl; intros.
    - exists nil, newUml; simpl; repeat split; auto.
      + intro k; auto.
      + constructor.
    - inv H; inv HUmlCons;  specialize (IHuml1 _ _ HCollector); dest.
      + exists (umUpd upd :: x), x0; subst; repeat split; auto.
        * rewrite UpdOrMeths_RegsT_app in HDisjRegs.
          apply key_not_In_app in HDisjRegs; dest.
          intro k; simpl.
          destruct (string_dec (fst upd) k); subst.
          -- right; intro.
             rewrite in_map_iff in H4; dest.
             apply (H3 (snd x1)); destruct x1; simpl in *; rewrite <- H4; auto.
          -- destruct (H0 k); auto.
             left; intro; destruct H5; auto.
        * econstructor; auto.
          rewrite UpdOrMeths_RegsT_app in HDisjRegs.
          apply key_not_In_app in HDisjRegs; dest; auto.
      + exists (umMeth meth :: x), x0; subst; repeat split; auto.
        econstructor 3; eauto.
      + exists (umMeth meth :: x), x0; subst; repeat split; auto.
        econstructor 4; eauto.
      + exists (fUml ++ x), x0; subst; repeat split; eauto using app_assoc.
        * intro k; specialize (HDisjRegs k); specialize (H0 k).
          rewrite UpdOrMeths_RegsT_app, map_app, in_app_iff in *.
          firstorder fail.
        * econstructor 5; auto.
          -- assumption.
          -- intro k; destruct (HDisjRegs k); auto.
             right; intro; apply H.
             rewrite UpdOrMeths_RegsT_app, map_app, in_app_iff; auto.
  Qed.

  Lemma ESemAction_meth_collector_stitch (uml1 : UpdOrMeths) :
    forall uml2 newUml1 newUml2
           (HDisjRegs : DisjKey (UpdOrMeths_RegsT newUml1) (UpdOrMeths_RegsT newUml2)),
      ESemAction_meth_collector uml1 newUml1 ->
      ESemAction_meth_collector uml2 newUml2 ->
      ESemAction_meth_collector (uml1 ++ uml2) (newUml1 ++ newUml2).
  Proof.
    induction uml1; simpl; intros.
    - inv H; simpl; auto; discriminate.
    - inv H; simpl; inv HUmlCons.
      + econstructor; auto.
        * specialize (HDisjRegs (fst upd)); simpl in *; destruct HDisjRegs; [exfalso; apply H; left; reflexivity|].
          repeat intro.
          rewrite UpdOrMeths_RegsT_app, in_app_iff in H1.
          destruct H1.
          -- eapply HDisjRegs0; eauto.
          -- apply H; rewrite in_map_iff; exists (fst upd, v); split; auto.
        * eapply IHuml1; eauto.
          repeat intro; specialize (HDisjRegs k); simpl in *.
          clear - HDisjRegs.
          firstorder fail.
      + econstructor 3; auto.
        assumption.
      + econstructor 4; auto.
        assumption.
      + econstructor 5.
        * reflexivity.
        * apply HESemAction.
        * instantiate (1 := newUml ++ newUml2).
          intro k.
          specialize (HDisjRegs k); specialize (HDisjRegs0 k).
          clear - HDisjRegs HDisjRegs0.
          rewrite UpdOrMeths_RegsT_app, map_app, in_app_iff in *.
          firstorder fail.
        * reflexivity.
        * rewrite app_assoc; reflexivity.
        * eapply IHuml1; eauto.
          intro k.
          specialize (HDisjRegs k).
          clear - HDisjRegs.
          rewrite UpdOrMeths_RegsT_app, map_app, in_app_iff in *.
          firstorder fail.
  Qed.

End ESemAction_meth_collector.

(* Section WriteInline. *)
Hint Rewrite unifyWO : _word_zero.



Lemma Extension_inlineWrites {k : Kind} (ea : EActionT type k) :
  forall o uml retv rf,
    ESemAction o ea uml retv ->
    forall newUml,
      ESemAction_meth_collector (getRegFileWrite rf) o uml newUml ->
      ESemAction o (inlineWriteFile rf ea) newUml retv.
Proof.
  induction ea; simpl; intros; destruct rf.
  - inv H0; EqDep_subst.
    inv H1;[discriminate | | | ]; remember (String.eqb _ _) as strb; destruct strb;
      symmetry in Heqstrb; inv HUmlCons; try rewrite String.eqb_eq in Heqstrb;
        try rewrite String.eqb_neq in Heqstrb; subst;
          try (destruct rfIsWrMask, Signature_dec); subst; simpl in *; try congruence;
            EqDep_subst.
    + econstructor; eauto.
    + econstructor; eauto.
    + econstructor; eauto.
    + econstructor; eauto.
    + autorewrite with _word_zero in *; inv HESemAction0; simpl in *; EqDep_subst.
      autorewrite with _word_zero in *; inv HESemAction1; simpl in *; EqDep_subst.
      do 2 econstructor; auto; rewrite (Eqdep.EqdepTheory.UIP_refl _ _ e0).
      -- apply HRegVal.
      -- instantiate (1 := (newUml ++ newUml0)).
         do 2 (apply f_equal2; auto; apply f_equal).
         clear.
         rewrite <- (rev_involutive (getFins rfNum)).
         repeat rewrite <- fold_left_rev_right; simpl.
         rewrite (rev_involutive).
         induction (rev (getFins rfNum)); simpl; auto.
         rewrite IHl; auto.
      -- repeat intro.
         specialize (HDisjRegs rfDataArray); simpl in *.
         rewrite UpdOrMeths_RegsT_app, in_app_iff in H0.
         destruct H0.
         ++ eapply HDisjRegs0; eauto.
         ++ destruct HDisjRegs; eauto.
            apply H1; rewrite in_map_iff; exists (rfDataArray, v); split; auto.
      -- autorewrite with _word_zero in *; inv HESemAction0; simpl in *; EqDep_subst.
         rewrite (unifyWO retV) in HESemAction; simpl in *.
         eapply H; simpl; eauto.
    + autorewrite with _word_zero in *; inv HESemAction0; simpl in *; EqDep_subst.
      autorewrite with _word_zero in *; inv HESemAction1; simpl in *; EqDep_subst.
      econstructor; auto; econstructor 13; auto; rewrite (Eqdep.EqdepTheory.UIP_refl _ _ e0).
      -- apply HRegVal.
      -- instantiate (1 := (newUml ++ newUml0)).
         do 2 (apply f_equal2; auto; apply f_equal).
         clear.
         rewrite <- (rev_involutive (getFins rfNum)).
         repeat rewrite <- fold_left_rev_right; simpl.
         rewrite (rev_involutive).
         induction (rev (getFins rfNum)); simpl; auto.
         rewrite IHl; auto.
      -- repeat intro.
         specialize (HDisjRegs rfDataArray); simpl in *.
         rewrite UpdOrMeths_RegsT_app, in_app_iff in H0.
         destruct H0.
         ++ eapply HDisjRegs0; eauto.
         ++ destruct HDisjRegs; eauto.
            apply H1; rewrite in_map_iff; exists (rfDataArray, v); split; auto.
      -- autorewrite with _word_zero in *; inv HESemAction0; simpl in *; EqDep_subst.
         rewrite (unifyWO retV) in HESemAction; simpl in *.
         eapply H; simpl; eauto.
  - inv H0; simpl in *; EqDep_subst; econstructor; eauto.
  - inv H0; simpl in *; EqDep_subst.
    + specialize (ESemAction_meth_collector_break _ _ H1) as TMP; dest.
      econstructor.
      * instantiate (1 := x0); instantiate (1 := x); auto.
      * eapply IHea; eauto.
      * eapply H; eauto.
      * assumption.
  - inv H0; simpl in *; EqDep_subst; econstructor; eauto.
  - inv H0; simpl in *; EqDep_subst; econstructor; eauto.
  -inv H; simpl in *; EqDep_subst.
   inv H0; [ | discriminate | discriminate | discriminate].
   inv HUmlCons; econstructor; auto.
   + simpl in *; auto.
   + eapply IHea; eauto.
  - inv H0; simpl in *; EqDep_subst; specialize (ESemAction_meth_collector_break _ _ H1) as TMP; dest.
    + econstructor; eauto.
    + econstructor 8; eauto.
  - inv H; simpl in *; EqDep_subst; econstructor; eauto.
  - inv H; simpl in *; EqDep_subst; econstructor; eauto.
    inv H0; auto; discriminate.
  - inv H0; simpl in *; EqDep_subst; econstructor; eauto.
  - inv H; simpl in *; EqDep_subst.
    + inv H0; inv HUmlCons.
      econstructor; eauto.
    + inv H0; inv HUmlCons.
      econstructor 13; eauto.
  - inv H; simpl in *; EqDep_subst.
    + inv H0; inv HUmlCons.
      econstructor; auto.
      * simpl in *; eauto.
      * eapply IHea; eauto.
    + inv H0; inv HUmlCons.
      econstructor 15; auto.
      * apply HRegVal2.
      * instantiate (1 := newUml1).
        simpl in *; eauto.
      * reflexivity.
      * eapply IHea; eauto.
  - inv H0; simpl in *; EqDep_subst.
    + econstructor; eauto.
    + econstructor 17; eauto.
Qed.

Lemma inlineWrites_Extension {k : Kind} (ea : EActionT type k):
  forall rf o newUml retv,
    ESemAction o (inlineWriteFile rf ea) newUml retv ->
    exists uml,
      ESemAction_meth_collector (getRegFileWrite rf) o uml newUml /\
      ESemAction o ea uml retv.
Proof.
  induction ea; simpl in *; intro rf; remember rf as rf'; destruct rf'; intros.
  - remember (String.eqb _ _) as strb; symmetry in Heqstrb.
    destruct strb; try rewrite String.eqb_eq in *; try rewrite String.eqb_neq in *;
      [destruct rfIsWrMask; destruct Signature_dec |].
    + revert Heqrf'.
      inv H0; simpl in *; EqDep_subst.
      inv HESemAction; simpl in *; EqDep_subst.
      * specialize (H _ _ _ _ _ HESemAction0); dest; inv H9.
        intro.
        exists (umMeth (meth, existT SignT (WriteRqMask (Nat.log2_up rfIdxNum) rfNum rfData, Void) (evalExpr e, WO))::x); split.
        -- econstructor 5; auto.
           ++ econstructor; eauto.
              econstructor; simpl; auto.
              ** rewrite in_map_iff.
                 exists (rfDataArray, existT _ (SyntaxKind (Array rfIdxNum rfData)) regV); split; auto.
              ** instantiate (1 := nil); repeat intro; auto.
              ** econstructor; eauto.
           ++ intro; simpl.
              destruct (string_dec rfDataArray k).
              ** right; instantiate (1 := newUml0).
                 intro; rewrite in_map_iff in H1; dest; destruct x0; simpl in *; subst.
                 eapply HDisjRegs; eauto.
              ** left; intro; destruct H1; subst; eauto.
           ++ simpl.
              do 2 (apply f_equal2; auto; apply f_equal).
              clear.
              rewrite <- (rev_involutive (getFins rfNum)).
              repeat rewrite <- fold_left_rev_right; simpl.
              rewrite (rev_involutive).
              induction (rev (getFins rfNum)); simpl; auto.
              rewrite IHl; auto.
           ++ assumption.
        -- econstructor; eauto.
      * discriminate.
    + inv H0; simpl in *; EqDep_subst.
      * specialize (H _ _ _ _ _ HESemAction); dest.
        exists (umMeth (meth, existT SignT s (evalExpr e, mret))::x); split.
        -- econstructor 4; simpl; eauto.
           intro; destruct s; simpl in *; auto.
        -- econstructor; eauto.
    + revert Heqrf'.
      inv H0; EqDep_subst.
      inv HESemAction; simpl in *; EqDep_subst; [discriminate|].
      * specialize (H _ _ _ _ _ HESemAction0); dest; inv H9.
        intro.
        exists (umMeth (meth, existT SignT (WriteRq (Nat.log2_up rfIdxNum) (Array rfNum rfData), Void) (evalExpr e, WO))::x); split.
        -- econstructor 5; auto.
           ++ econstructor; eauto.
              econstructor; simpl; auto.
              ** rewrite in_map_iff.
                 exists (rfDataArray, existT _ (SyntaxKind (Array rfIdxNum rfData)) regV); split; auto.
              ** instantiate (1 := nil); repeat intro; auto.
              ** econstructor; eauto.
           ++ intro; simpl.
              destruct (string_dec rfDataArray k).
              ** right; instantiate (1 := newUml0).
                 intro; rewrite in_map_iff in H1; dest; destruct x0; simpl in *; subst.
                 eapply HDisjRegs; eauto.
              ** left; intro; destruct H1; subst; eauto.
           ++ simpl.
              do 2 (apply f_equal2; auto; apply f_equal).
              clear.
              rewrite <- (rev_involutive (getFins rfNum)).
              repeat rewrite <- fold_left_rev_right; simpl.
              rewrite (rev_involutive).
              induction (rev (getFins rfNum)); simpl; auto.
              rewrite IHl; auto.
           ++ assumption.
        -- econstructor; eauto.
    + inv H0; simpl in *; EqDep_subst.
      * specialize (H _ _ _ _ _ HESemAction); dest.
        exists (umMeth (meth, existT SignT s (evalExpr e, mret))::x); split.
        -- econstructor 4; simpl; eauto.
           intro; destruct s; simpl in *; auto.
        -- econstructor; eauto.
    + inv H0; simpl in *; EqDep_subst.
      * specialize (H _ _ _ _ _ HESemAction); dest.
        exists (umMeth (meth, existT SignT s (evalExpr e, mret))::x); split.
        -- econstructor 3; simpl; eauto.
           intro; destruct s; simpl in *; auto.
        -- econstructor; eauto.
  - inv H0; EqDep_subst.
    specialize (H _ _ _ _ _ HESemAction); dest.
    exists x; split; auto.
    econstructor; eauto.
  - inv H0; EqDep_subst.
    specialize (H _ _ _ _ _ HESemActionCont); dest.
    specialize (IHea _ _ _ _ HESemAction); dest.
    exists (x0 ++ x); split; auto.
    apply ESemAction_meth_collector_stitch; auto.
    econstructor.
    + instantiate (1 := x); instantiate (1 := x0).
      intro k0.
      specialize (HDisjRegs k0).
      specialize (ESemActionMC_Upds_SubList H) as P0.
      specialize (ESemActionMC_Upds_SubList H1) as P1.
      clear - P0 P1 HDisjRegs.
      destruct HDisjRegs;[left | right]; intro; apply H; rewrite in_map_iff in *; dest;
        exists x1; split; auto.
    + apply H2.
    + assumption.
    + reflexivity.
  - inv H0; EqDep_subst.
    specialize (H _ _ _ _ _ HESemAction); dest.
    exists x; split; auto.
    econstructor; eauto.
  - inv H0; EqDep_subst.
    specialize (H _ _ _ _ _ HESemAction); dest.
    exists x; split; auto.
    econstructor; eauto.
  - inv H; EqDep_subst.
    specialize (IHea _ _ _ _ HESemAction); dest.
    exists (umUpd (r, existT (fullType type) k (evalExpr e))::x); split; auto.
    + econstructor; auto.
      * simpl; assumption.
    + econstructor; auto.
      repeat intro; eapply HDisjRegs.
      apply (ESemActionMC_Upds_SubList H _ H1).
  - inv H0; EqDep_subst.
    + specialize (IHea1 _ _ _ _ HEAction); dest.
      specialize (H _ _ _ _ _ HESemAction); dest.
      exists (x ++ x0); split; auto.
      * apply ESemAction_meth_collector_stitch; auto.
      * econstructor; auto.
        -- intro k0.
           specialize (HDisjRegs k0).
           specialize (ESemActionMC_Upds_SubList H) as P0.
           specialize (ESemActionMC_Upds_SubList H0) as P1.
           clear - P0 P1 HDisjRegs.
           destruct HDisjRegs; [left | right]; intro; apply H; rewrite in_map_iff in *; dest;
             exists x1; split; auto.
        -- apply H1.
        -- assumption.
    + specialize (IHea2 _ _ _ _ HEAction); dest.
      specialize (H _ _ _ _ _ HESemAction); dest.
      exists (x ++ x0); split; auto.
      * apply ESemAction_meth_collector_stitch; auto.
      * econstructor 8; auto.
        -- intro k0.
           specialize (HDisjRegs k0).
           specialize (ESemActionMC_Upds_SubList H) as P0.
           specialize (ESemActionMC_Upds_SubList H0) as P1.
           clear - P0 P1 HDisjRegs.
           destruct HDisjRegs; [left | right]; intro; apply H; rewrite in_map_iff in *; dest;
             exists x1; split; auto.
        -- apply H1.
        -- assumption.
  - inv H; EqDep_subst.
    specialize (IHea _ _ _ _ HESemAction); dest.
    exists x; split; auto.
    econstructor; eauto.
  - inv H; EqDep_subst.
    exists nil; split; auto.
    + constructor.
    + econstructor; eauto.
  - inv H0; EqDep_subst.
    specialize (H _ _ _ _ _ HESemAction); dest.
    exists x; split; auto.
    econstructor; eauto.
  - inv H; EqDep_subst.
    + specialize (IHea _ _ _ _ HESemAction); dest.
      exists (umUpd (dataArray,
                   existT (fullType type) (SyntaxKind (Array idxNum Data))
                          (evalExpr
                             (fold_left
                                (fun (newArr : Expr type (SyntaxKind (Array idxNum Data))) (i : Fin.t num) =>
                                   (IF ReadArrayConst mask0 i
                                    then newArr @[ idx + Const type ($(proj1_sig (Fin.to_nat i)))%word <-
                                                               ReadArrayConst val i] else newArr)%kami_expr) 
                                (getFins num) (Var type (SyntaxKind (Array idxNum Data)) regV))))::x); split; auto.
      * econstructor; eauto; simpl.
        assumption.
      * econstructor; eauto.
        repeat intro.
        eapply HDisjRegs.
        specialize (ESemActionMC_Upds_SubList H) as P0.
        apply (P0 _ H1).
    + specialize (IHea _ _ _ _ HESemAction); dest.
      exists (umUpd (dataArray,
                   existT (fullType type) (SyntaxKind (Array idxNum Data))
                          (evalExpr
                             (fold_left
                                (fun (newArr : Expr type (SyntaxKind (Array idxNum Data))) (i : Fin.t num) =>
                                   (newArr @[ idx + Const type ($(proj1_sig (Fin.to_nat i)))%word <-
                                                          ReadArrayConst val i])%kami_expr) (getFins num)
                                (Var type (SyntaxKind (Array idxNum Data)) regV))))::x); split; auto.
      * econstructor; eauto; simpl.
        assumption.
      * econstructor 13; eauto.
        repeat intro.
        eapply HDisjRegs.
        specialize (ESemActionMC_Upds_SubList H) as P0.
        apply (P0 _ H1).
  - inv H; EqDep_subst.
    + specialize (IHea _ _ _ _ HESemAction); dest.
      exists (umUpd (readReg,
                   existT (fullType type) (SyntaxKind (Bit (Nat.log2_up idxNum))) (evalExpr idx)) :: x); split; auto.
      * econstructor; eauto.
        simpl; assumption.
      * econstructor; auto.
        repeat intro.
        eapply HDisjRegs.
        specialize (ESemActionMC_Upds_SubList H) as P0.
        apply (P0 _ H1).
    + specialize (IHea _ _ _ _ HESemAction); dest.
      exists (umUpd (readReg,
                   existT (fullType type) (SyntaxKind (Array num Data))
                          (evalExpr
                             (BuildArray
                                (fun i : Fin.t num =>
                                   (Var type (SyntaxKind (Array idxNum Data)) regV @[
                                          Var type (SyntaxKind (Bit (Nat.log2_up idxNum))) (evalExpr idx) +
                                          Const type ($(proj1_sig (Fin.to_nat i)))%word])%kami_expr)))) :: x); split; auto.
      * econstructor; simpl in *; auto.
        -- assumption.
      * econstructor 15; auto.
        -- assumption.
        -- repeat intro.
           eapply HDisjRegs.
           specialize (ESemActionMC_Upds_SubList H) as P0.
           apply (P0 _ H1).
  - inv H0; EqDep_subst.
    + specialize (H _ _ _ _ _ HESemAction); dest.
      exists x ; split; auto.
      econstructor; eauto.
    + specialize (H _ _ _ _ _ HESemAction); dest.
      exists x; split; auto.
      econstructor 17; eauto.
Qed.

Corollary inlineWrites_congruence {k : Kind} (ea1 ea2 : EActionT type k) :
  (forall o uml retv,
      ESemAction o ea1 uml retv ->
      ESemAction o ea2 uml retv) ->
  forall o newUml retv rf,
    ESemAction o (inlineWriteFile rf ea1) newUml retv ->
    ESemAction o (inlineWriteFile rf ea2) newUml retv.
Proof.
  intros.
  specialize (inlineWrites_Extension _ _ H0) as TMP; dest.
  specialize (H _ _ _ H2).
  apply (Extension_inlineWrites _ H H1).
Qed.

Lemma WrInline_inlines {k : Kind} (a : ActionT type k) :
  forall rf o uml retv,
    ESemAction o (Action_EAction (inlineSingle a (getRegFileWrite rf))) uml retv ->
    ESemAction o (inlineWriteFile rf (Action_EAction a)) uml retv.
Proof.
  induction a; intros; auto; simpl; destruct rf; subst; simpl in *.
  - destruct String.eqb, rfIsWrMask;
      [destruct Signature_dec | destruct Signature_dec | | ]; simpl in *.
    + inv H0; EqDep_subst.
      inv HESemAction; EqDep_subst.
      inv HESemAction0; EqDep_subst.
      inv HESemAction; EqDep_subst.
      do 2 econstructor; auto.
      * apply HRegVal.
      * instantiate (1 := (newUml0 ++ newUmlCont)); simpl.
        do 2 (apply f_equal2; auto; apply f_equal).
        clear.
        rewrite <- (rev_involutive (getFins rfNum)).
        repeat rewrite <- fold_left_rev_right; simpl.
        rewrite (rev_involutive).
        induction (rev (getFins rfNum)); simpl; auto.
        rewrite IHl; auto.
      * repeat intro; simpl in *.
        rewrite UpdOrMeths_RegsT_app, in_app_iff in H0.
        specialize (HDisjRegs rfDataArray); simpl in *.
        destruct HDisjRegs; [apply H1; auto|].
        specialize (HDisjRegs0 v0); destruct H0; auto.
        apply H1; rewrite in_map_iff.
        exists (rfDataArray, v0); split; auto.
      * inv HESemAction0; EqDep_subst; simpl; eauto.
    + inv H0; EqDep_subst.
      econstructor; eauto.
    +  inv H0; EqDep_subst.
       inv HESemAction; EqDep_subst.
       inv HESemAction0; EqDep_subst.
       inv HESemAction; EqDep_subst.
       econstructor; auto; econstructor 13; auto.
       * apply HRegVal.
       * instantiate (1 := (newUml0 ++ newUmlCont)); simpl.
         do 2 (apply f_equal2; auto; apply f_equal).
         clear.
         rewrite <- (rev_involutive (getFins rfNum)).
         repeat rewrite <- fold_left_rev_right; simpl.
         rewrite (rev_involutive).
         induction (rev (getFins rfNum)); simpl; auto.
         rewrite IHl; auto.
       * repeat intro; simpl in *.
         rewrite UpdOrMeths_RegsT_app, in_app_iff in H0.
         specialize (HDisjRegs rfDataArray); simpl in *.
         destruct HDisjRegs; [apply H1; auto|].
         specialize (HDisjRegs0 v0); destruct H0; auto.
         apply H1; rewrite in_map_iff.
         exists (rfDataArray, v0); split; auto.
       * inv HESemAction0; EqDep_subst; simpl; eauto.
    + inv H0; EqDep_subst.
      econstructor; eauto.
    + inv H0; EqDep_subst.
      econstructor; eauto.
    + inv H0; EqDep_subst.
      econstructor; eauto.
  - inv H0; EqDep_subst; econstructor; eauto.
  - inv H0; EqDep_subst; econstructor; eauto.
  - inv H0; EqDep_subst; econstructor; eauto.
  - inv H0; EqDep_subst; econstructor; eauto.
  - inv H; EqDep_subst; econstructor; eauto.
  - inv H0; EqDep_subst.
    + econstructor; eauto.
    + econstructor 8; eauto.
  - inv H; EqDep_subst; econstructor; eauto.
  - inv H; EqDep_subst; econstructor; eauto.
Qed.

Lemma inline_WrInlines {k : Kind} (a : ActionT type k) rf :
  forall o uml retv,
    ESemAction o (inlineWriteFile rf (Action_EAction a)) uml retv ->
    ESemAction o (Action_EAction (inlineSingle a (getRegFileWrite rf))) uml retv.
Proof.
  induction a; intros; auto; simpl; destruct rf; subst; simpl in *.
  - destruct String.eqb, rfIsWrMask;
      [destruct Signature_dec | destruct Signature_dec | | ]; simpl in *.
    + inv H0; EqDep_subst.
      inv HESemAction; EqDep_subst; inv H9.
      econstructor; simpl; auto.
      * instantiate (1 := newUml).
        instantiate (1 := (umUpd
                             (rfDataArray,
                              existT (fullType type) (SyntaxKind (Array rfIdxNum rfData))
                                     (evalExpr
                                        (fold_left
                                           (fun (newArr : Expr type (SyntaxKind (Array rfIdxNum rfData))) (i : Fin.t rfNum) =>
                                              (IF ReadArrayConst (ReadStruct e (Fin.FS (Fin.FS Fin.F1))) i
                                               then newArr @[
                                                             ReadStruct e Fin.F1 + Const type ($(proj1_sig (Fin.to_nat i)))%word <-
                                                                                         ReadArrayConst (ReadStruct e (Fin.FS Fin.F1)) i] else newArr)%kami_expr)
                                           (getFins rfNum) (Var type (SyntaxKind (Array rfIdxNum rfData)) regV))))) :: nil); simpl in *.
        intro k; simpl.
        destruct (string_dec rfDataArray k); [right | left]; intro; auto; subst.
        -- rewrite in_map_iff in *; dest; destruct x; subst; eapply HDisjRegs; eauto.
        -- destruct H0; auto.
      * do 2 econstructor; auto.
        -- apply HRegVal.
        -- econstructor; auto.
           ++ rewrite in_map_iff.
              eexists; split; [| eapply HRegVal]; simpl; reflexivity.
           ++ instantiate (1 := nil); simpl; repeat intro; auto.
           ++ do 2 (apply f_equal2; auto; apply f_equal).
              clear.
              rewrite <- (rev_involutive (getFins rfNum)).
              repeat rewrite <- fold_left_rev_right; simpl.
              rewrite (rev_involutive).
              induction (rev (getFins rfNum)); simpl; auto.
              rewrite IHl; auto.
           ++ econstructor; eauto.
      * eapply H; eauto.
      * simpl; reflexivity.
    + inv H0; EqDep_subst.
      econstructor; eauto.
    + subst.
      inv H0; EqDep_subst.
      inv HESemAction; EqDep_subst; [discriminate |].
      econstructor; simpl; auto.
      * instantiate (1 := newUml).
        instantiate (1 := (umUpd
                             (rfDataArray,
                              existT (fullType type) (SyntaxKind (Array rfIdxNum rfData))
                                     (evalExpr
                                        (fold_left
                                           (fun (newArr : Expr type (SyntaxKind (Array rfIdxNum rfData))) (i : Fin.t rfNum) =>
                                              (newArr @[ ReadStruct e Fin.F1 + Const type ($(proj1_sig (Fin.to_nat i)))%word <-
                                                                                     ReadArrayConst (ReadStruct e (Fin.FS Fin.F1)) i])%kami_expr) 
                                           (getFins rfNum) (Var type (SyntaxKind (Array rfIdxNum rfData)) regV))))) :: nil); simpl in *.
        intro k; simpl.
        destruct (string_dec rfDataArray k); [right | left]; intro; auto; subst.
        -- rewrite in_map_iff in *; dest; destruct x; subst; eapply HDisjRegs; eauto.
        -- destruct H0; auto.
      * do 2 econstructor; auto.
        -- apply HRegVal.
        -- econstructor; auto.
           ++ rewrite in_map_iff.
              eexists; split; [| eapply HRegVal]; simpl; reflexivity.
           ++ instantiate (1 := nil); simpl; repeat intro; auto.
           ++ do 2 (apply f_equal2; auto; apply f_equal).
              clear.
              rewrite <- (rev_involutive (getFins rfNum)).
              repeat rewrite <- fold_left_rev_right; simpl.
              rewrite (rev_involutive).
              induction (rev (getFins rfNum)); simpl; auto.
              rewrite IHl; auto.
           ++ econstructor; eauto.
      * eapply H; eauto.
      * simpl; reflexivity.
    + inv H0; EqDep_subst.
      econstructor; eauto.
    + inv H0; EqDep_subst.
      econstructor; eauto.
    + inv H0; EqDep_subst.
      econstructor; eauto.
  - inv H0; EqDep_subst.
    econstructor; eauto.
  - inv H0; EqDep_subst.
    econstructor; eauto.
  - inv H0; EqDep_subst.
    econstructor; eauto.
  - inv H0; EqDep_subst.
    econstructor; eauto.
  - inv H; EqDep_subst.
    econstructor; eauto.
  - inv H0; EqDep_subst.
    ++ econstructor; eauto.
    ++ econstructor 8; eauto.
  - inv H; EqDep_subst.
    econstructor; eauto.
  - inv H; EqDep_subst.
    econstructor; eauto.
Qed.

(* End WriteInline. *)

(* Section AsyncReadInline. *)

Lemma Extension_inlineAsyncRead {k : Kind} (ea : EActionT type k) :
  forall rf (read : string) (reads : list string)
         (HIsAsync : rfRead rf = Async reads) (HIn : In read reads) o uml retv,
    ESemAction o ea uml retv ->
    forall newUml,
      ESemAction_meth_collector (getAsyncReads rf read) o uml newUml ->
      ESemAction o (inlineAsyncReadFile read rf ea) newUml retv.
Proof.
  destruct rf; simpl in *; destruct rfRead;[| intros; discriminate].
  induction ea; simpl; intros; inv HIsAsync; remember (existsb _ _) as exb;
    symmetry in Heqexb; destruct exb; try rewrite existsb_exists in *; dest;
      try rewrite existsb_nexists_str in *; try rewrite String.eqb_eq in *;
        subst; try congruence.
  - inv H0; EqDep_subst.
    remember (String.eqb _ _) as strb; symmetry in Heqstrb; revert Heqstrb.
    inv H1;[discriminate | | | ]; intro; destruct strb; try rewrite String.eqb_eq in *;
      inv HUmlCons; try (destruct Signature_dec); subst;
        try (simpl in *; congruence); EqDep_subst.
    + econstructor; eauto.
    + econstructor; eauto.
    + econstructor; eauto.
    + rewrite (Eqdep.EqdepTheory.UIP_refl _ _ e0) in *.
      inv HESemAction0; EqDep_subst.
      inv HESemAction1; EqDep_subst.
      econstructor; simpl in *; eauto.
    + rewrite eqb_refl in *; discriminate.
  - inv H0; simpl in *; EqDep_subst; econstructor; eauto.
  - inv H0; simpl in *; EqDep_subst.
    + specialize (ESemAction_meth_collector_break _ _ H1) as TMP; dest.
      econstructor.
      * instantiate (1 := x1); instantiate (1 := x0); auto.
      * eapply IHea; eauto.
      * eapply H; eauto.
      * assumption.
  - inv H0; simpl in *; EqDep_subst; econstructor; eauto.
  - inv H0; simpl in *; EqDep_subst; econstructor; eauto.
  -inv H; simpl in *; EqDep_subst.
   inv H0; [ | discriminate | discriminate | discriminate].
   inv HUmlCons; econstructor; auto.
   + simpl in *; auto.
   + eapply IHea; eauto.
  - inv H0; simpl in *; EqDep_subst; specialize (ESemAction_meth_collector_break _ _ H1) as TMP; dest.
    + econstructor; eauto.
    + econstructor 8; eauto.
  - inv H; simpl in *; EqDep_subst; econstructor; eauto.
  - inv H; simpl in *; EqDep_subst; econstructor; eauto.
    inv H0; auto; discriminate.
  - inv H0; simpl in *; EqDep_subst; econstructor; eauto.
  - inv H; simpl in *; EqDep_subst.
    + inv H0; inv HUmlCons.
      econstructor; eauto.
    + inv H0; inv HUmlCons.
      econstructor 13; eauto.
  - inv H; simpl in *; EqDep_subst.
    + inv H0; inv HUmlCons.
      econstructor; auto.
      * simpl in *; eauto.
      * eapply IHea; eauto.
    + inv H0; inv HUmlCons.
      econstructor 15; auto.
      * apply HRegVal2.
      * instantiate (1 := newUml1).
        simpl in *; eauto.
      * reflexivity.
      * eapply IHea; eauto.
  - inv H0; simpl in *; EqDep_subst.
    + econstructor; eauto.
    + econstructor 17; eauto.
Qed.

Lemma inlineAsyncRead_Extension {k : Kind} (ea : EActionT type k):
  forall rf (reads : list string)(HIsAsync : rfRead rf = Async reads)
         (read : string) (HIn : In read reads) o newUml retv,
    ESemAction o (inlineAsyncReadFile read rf ea) newUml retv ->
    exists uml,
      ESemAction_meth_collector (getAsyncReads rf read) o uml newUml /\
      ESemAction o ea uml retv.
Proof.
  induction ea; simpl in *; intros rf; remember rf as rf'; destruct rf'; intros;
    simpl in *; rewrite HIsAsync in *; remember (existsb _ _) as exb;
      symmetry in Heqexb; destruct exb; try rewrite existsb_exists in *; dest;
        try rewrite existsb_nexists_str in *; try rewrite String.eqb_eq in *;
          revert Heqrf' HIsAsync; subst; try congruence.
  - remember (String.eqb _ _) as strb; symmetry in Heqstrb;
      destruct strb; [destruct Signature_dec |].
    + inv H0; EqDep_subst.
      intros.
      assert (Syntax.rfRead rf = Async reads) as P0.
      { rewrite <- Heqrf'; reflexivity. }
      rewrite <- Heqrf' in *.
      specialize (H _ _ _ P0 _ HIn _ _ _ HESemAction); dest.
      exists (umMeth (x, existT SignT (Bit (Nat.log2_up rfIdxNum), Array rfNum rfData) (evalExpr e, (evalExpr
                                                                                                      (BuildArray
                                                                                                         (fun i : Fin.t rfNum =>
                                                                                                            (Var type (SyntaxKind (Array rfIdxNum rfData)) regV @[
                                                                                                                   Var type (SyntaxKind (Bit (Nat.log2_up rfIdxNum))) (evalExpr e) +
                                                                                                                   Const type ($(proj1_sig (Fin.to_nat i)))%word])%kami_expr)))))::x0); split.
      * econstructor 5; auto.
        -- do 2 (econstructor; eauto).
        -- repeat intro; auto.
        -- simpl; reflexivity.
        -- assumption.
      * rewrite String.eqb_eq in *; subst; econstructor; eauto.
    + inv H0; EqDep_subst.
      intros.
      assert (Syntax.rfRead rf = Async reads) as P0.
      { rewrite <- Heqrf'; reflexivity. }
      rewrite <- Heqrf' in *.
      specialize (H _ _ _ P0 _ HIn _ _ _ HESemAction); dest.
      exists (umMeth (meth, existT SignT s (evalExpr e, mret))::x0); split.
      * econstructor 4; simpl; eauto.
        intro; destruct s; simpl in *; auto.
      * econstructor; eauto.
    + inv H0; EqDep_subst.
      intros.
      assert (Syntax.rfRead rf = Async reads) as P0.
      { rewrite <- Heqrf'; reflexivity. }
      rewrite <- Heqrf' in *.
      specialize (H _ _ _ P0 _ HIn _ _ _ HESemAction); dest.
      exists (umMeth (meth, existT SignT s (evalExpr e, mret))::x0); split.
      * econstructor 3; simpl; eauto.
        intro; destruct s; simpl in *; subst; rewrite String.eqb_refl in *; discriminate.
      * econstructor; eauto.
  - inv H0; EqDep_subst.
    intros.
    assert (Syntax.rfRead rf = Async reads) as P0.
    { rewrite <- Heqrf'; reflexivity. }
    rewrite <- Heqrf' in *.
    specialize (H _ _ _ P0 _ HIn _ _ _ HESemAction); dest.
    exists x0; split; auto.
    econstructor; eauto.
  - inv H0; EqDep_subst.
    intros.
    assert (Syntax.rfRead rf = Async reads) as P0.
    { rewrite <- Heqrf'; reflexivity. }
    rewrite <- Heqrf' in *.
    specialize (H _ _ _ P0 _ HIn _ _ _ HESemActionCont); dest.
    specialize (IHea _ _ P0 _ HIn _ _ _ HESemAction); dest.
    exists (x1 ++ x0); split; auto.
    apply ESemAction_meth_collector_stitch; auto.
    econstructor.
    + instantiate (1 := x0); instantiate (1 := x1).
      intro k0.
      specialize (HDisjRegs k0).
      specialize (ESemActionMC_Upds_SubList H) as P1.
      specialize (ESemActionMC_Upds_SubList H2) as P2.
      clear - P1 P2 HDisjRegs.
      destruct HDisjRegs;[left | right]; intro; apply H; rewrite in_map_iff in *; dest;
        exists x; split; auto.
    + apply H3.
    + assumption.
    + reflexivity.
  - inv H0; EqDep_subst.
    intros.
    assert (Syntax.rfRead rf = Async reads) as P0.
    { rewrite <- Heqrf'; reflexivity. }
    rewrite <- Heqrf' in *.
    specialize (H _ _ _ P0 _ HIn _ _ _ HESemAction); dest.
    exists x0; split; auto.
    econstructor; eauto.
  - inv H0; EqDep_subst.
    intros.
    assert (Syntax.rfRead rf = Async reads) as P0.
    { rewrite <- Heqrf'; reflexivity. }
    rewrite <- Heqrf' in *.
    specialize (H _ _ _ P0 _ HIn _ _ _ HESemAction); dest.
    exists x0; split; auto.
    econstructor; eauto.
  - inv H; EqDep_subst.
    intros.
    assert (Syntax.rfRead rf = Async reads) as P0.
    { rewrite <- Heqrf'; reflexivity. }
    rewrite <- Heqrf' in *.
    specialize (IHea _ _ P0 _ HIn _ _ _ HESemAction); dest.
    exists (umUpd (r, existT (fullType type) k (evalExpr e))::x0); split; auto.
    + econstructor; auto.
      * simpl; assumption.
    + econstructor; auto.
      repeat intro; eapply HDisjRegs.
      apply (ESemActionMC_Upds_SubList H _ H2).
  - inv H0; EqDep_subst.
    + intros.
      assert (Syntax.rfRead rf = Async reads) as P0.
      { rewrite <- Heqrf'; reflexivity. }
      rewrite <- Heqrf' in *.
      specialize (IHea1 _ _ P0 _ HIn _ _ _ HEAction); dest.
      specialize (H _ _ _ P0 _ HIn _ _ _ HESemAction); dest.
      exists (x0 ++ x1); split; auto.
      * apply ESemAction_meth_collector_stitch; auto.
      * econstructor; auto.
        -- intro k0.
           specialize (HDisjRegs k0).
           specialize (ESemActionMC_Upds_SubList H) as P1.
           specialize (ESemActionMC_Upds_SubList H0) as P2.
           clear - P1 P2 HDisjRegs.
           destruct HDisjRegs; [left | right]; intro; apply H; rewrite in_map_iff in *; dest;
             exists x; split; auto.
        -- apply H2.
        -- assumption.
    + intros.
      assert (Syntax.rfRead rf = Async reads) as P0.
      { rewrite <- Heqrf'; reflexivity. }
      rewrite <- Heqrf' in *.
      specialize (IHea2 _ _ P0 _ HIn _ _ _ HEAction); dest.
      specialize (H _ _ _ P0 _ HIn _ _ _ HESemAction); dest.
      exists (x0 ++ x1); split; auto.
      * apply ESemAction_meth_collector_stitch; auto.
      * econstructor 8; auto.
        -- intro k0.
           specialize (HDisjRegs k0).
           specialize (ESemActionMC_Upds_SubList H) as P1.
           specialize (ESemActionMC_Upds_SubList H0) as P2.
           clear - P1 P2 HDisjRegs.
           destruct HDisjRegs; [left | right]; intro; apply H; rewrite in_map_iff in *; dest;
             exists x; split; auto.
        -- apply H2.
        -- assumption.
  - inv H; EqDep_subst.
    intros.
    assert (Syntax.rfRead rf = Async reads) as P0.
    { rewrite <- Heqrf'; reflexivity. }
    rewrite <- Heqrf' in *.
    specialize (IHea _ _ P0 _ HIn _ _ _ HESemAction); dest.
    exists x0; split; auto.
    econstructor; eauto.
  - inv H; EqDep_subst.
    exists nil; split; auto.
    + constructor.
    + econstructor; eauto.
  - inv H0; EqDep_subst.
    intros.
    assert (Syntax.rfRead rf = Async reads) as P0.
    { rewrite <- Heqrf'; reflexivity. }
    rewrite <- Heqrf' in *.
    specialize (H _ _ _ P0 _ HIn _ _ _ HESemAction); dest.
    exists x0; split; auto.
    econstructor; eauto.
  - inv H; EqDep_subst.
    + intros.
      assert (Syntax.rfRead rf = Async reads) as P0.
      { rewrite <- Heqrf'; reflexivity. }
      rewrite <- Heqrf' in *.
      specialize (IHea _ _ P0 _ HIn _ _ _ HESemAction); dest.
      exists (umUpd (dataArray,
                   existT (fullType type) (SyntaxKind (Array idxNum Data))
                          (evalExpr
                             (fold_left
                                (fun (newArr : Expr type (SyntaxKind (Array idxNum Data))) (i : Fin.t num) =>
                                   (IF ReadArrayConst mask0 i
                                    then newArr @[ idx + Const type ($(proj1_sig (Fin.to_nat i)))%word <-
                                                               ReadArrayConst val i] else newArr)%kami_expr) 
                                (getFins num) (Var type (SyntaxKind (Array idxNum Data)) regV))))::x0); split; auto.
      * econstructor; eauto; simpl.
        assumption.
      * econstructor; eauto.
        repeat intro.
        eapply HDisjRegs.
        specialize (ESemActionMC_Upds_SubList H) as P1.
        apply (P1 _ H2).
    + intros.
      assert (Syntax.rfRead rf = Async reads) as P0.
      { rewrite <- Heqrf'; reflexivity. }
      rewrite <- Heqrf' in *.
      specialize (IHea _ _ P0 _ HIn _ _ _ HESemAction); dest.
      exists (umUpd (dataArray,
                   existT (fullType type) (SyntaxKind (Array idxNum Data))
                          (evalExpr
                             (fold_left
                                (fun (newArr : Expr type (SyntaxKind (Array idxNum Data))) (i : Fin.t num) =>
                                   (newArr @[ idx + Const type ($(proj1_sig (Fin.to_nat i)))%word <-
                                                          ReadArrayConst val i])%kami_expr) (getFins num)
                                (Var type (SyntaxKind (Array idxNum Data)) regV))))::x0); split; auto.
      * econstructor; eauto; simpl.
        assumption.
      * econstructor 13; eauto.
        repeat intro.
        eapply HDisjRegs.
        specialize (ESemActionMC_Upds_SubList H) as P1.
        apply (P1 _ H2).
  - inv H; EqDep_subst.
    +  intros.
       assert (Syntax.rfRead rf = Async reads) as P0.
       { rewrite <- Heqrf'; reflexivity. }
       rewrite <- Heqrf' in *.
       specialize (IHea _ _ P0 _ HIn _ _ _ HESemAction); dest.
       exists (umUpd (readReg,
                    existT (fullType type) (SyntaxKind (Bit (Nat.log2_up idxNum))) (evalExpr idx)) :: x0); split; auto.
       * econstructor; eauto.
         simpl; assumption.
       * econstructor; auto.
         repeat intro.
         eapply HDisjRegs.
         specialize (ESemActionMC_Upds_SubList H) as P1.
         apply (P1 _ H2).
    + intros.
      assert (Syntax.rfRead rf = Async reads) as P0.
      { rewrite <- Heqrf'; reflexivity. }
      rewrite <- Heqrf' in *.
      specialize (IHea _ _ P0 _ HIn _ _ _ HESemAction); dest.
      exists (umUpd (readReg,
                   existT (fullType type) (SyntaxKind (Array num Data))
                          (evalExpr
                             (BuildArray
                                (fun i : Fin.t num =>
                                   (Var type (SyntaxKind (Array idxNum Data)) regV @[
                                          Var type (SyntaxKind (Bit (Nat.log2_up idxNum))) (evalExpr idx) +
                                          Const type ($(proj1_sig (Fin.to_nat i)))%word])%kami_expr)))) :: x0); split; auto.
      * econstructor; eauto.
        simpl; assumption.
      * econstructor 15; auto.
        -- assumption.
        -- repeat intro.
           eapply HDisjRegs.
           specialize (ESemActionMC_Upds_SubList H) as P1.
           apply (P1 _ H2).
  - inv H0; EqDep_subst.
    + intros.
      assert (Syntax.rfRead rf = Async reads) as P0.
      { rewrite <- Heqrf'; reflexivity. }
      rewrite <- Heqrf' in *.
      specialize (H _ _ _ P0 _ HIn _ _ _ HESemAction); dest.
      exists x0 ; split; auto.
      econstructor; eauto.
    +  intros.
       assert (Syntax.rfRead rf = Async reads) as P0.
       { rewrite <- Heqrf'; reflexivity. }
       rewrite <- Heqrf' in *.
       specialize (H _ _ _ P0 _ HIn _ _ _ HESemAction); dest.
       exists x0 ; split; auto.
       econstructor 17; eauto.
Qed.

Corollary inlineAsyncRead_congruence {k : Kind} (ea1 ea2 : EActionT type k) :
  (forall o uml retv,
      ESemAction o ea1 uml retv ->
      ESemAction o ea2 uml retv) ->
  forall o newUml retv rf (read : string) (reads : list string)
         (HIsAsync : rfRead rf = Async reads) (HIn : In read reads),
    ESemAction o (inlineAsyncReadFile read rf ea1) newUml retv ->
    ESemAction o (inlineAsyncReadFile read rf ea2) newUml retv.
Proof.
  intros.
  specialize (inlineAsyncRead_Extension _ _ HIsAsync _ HIn H0) as TMP; dest.
  specialize (H _ _ _ H2).
  apply (Extension_inlineAsyncRead HIsAsync HIn H H1).
Qed.

Lemma AsyncReadInline_inlines {k : Kind} (a : ActionT type k) :
  forall rf (reads : list string)(HIsAsync : rfRead rf = Async reads)
         (read : string) (HIn : In read reads) o uml retv,
    ESemAction o (Action_EAction (inlineSingle a (getAsyncReads rf read))) uml retv ->
    ESemAction o (inlineAsyncReadFile read rf (Action_EAction a)) uml retv.
Proof.
  induction a; intros; auto; simpl; destruct rf; simpl in *; rewrite HIsAsync in *;
    remember (existsb _ _) as exb; symmetry in Heqexb; destruct exb;
      try rewrite existsb_exists in *; try rewrite existsb_nexists_str in *;
        dest; try rewrite String.eqb_eq in *; subst; try congruence.
  - remember (String.eqb _ _) as strb; symmetry in Heqstrb; destruct strb;
      [rewrite String.eqb_eq in *; destruct Signature_dec
      |rewrite String.eqb_neq in *]; simpl in *.
    + inv H0; EqDep_subst.
      inv HESemAction; EqDep_subst.
      inv HESemAction0; EqDep_subst.
      inv HESemAction; EqDep_subst.
      econstructor; auto.
      * apply HRegVal.
      * eapply H; simpl; eauto.
    + inv H0; EqDep_subst.
      econstructor; eauto.
      eapply H; simpl; eauto.
    + inv H0; EqDep_subst.
      econstructor; auto.
      eapply H; simpl; eauto.
  - inv H0; EqDep_subst; econstructor; eapply H; simpl; eauto.
  - inv H0; EqDep_subst.
    econstructor; eauto.
    + eapply IHa; simpl; eauto.
    + eapply H; simpl; eauto.
  - inv H0; EqDep_subst; econstructor; eapply H; simpl; eauto.
  - inv H0; EqDep_subst; econstructor; eauto; eapply H; simpl; eauto.
  - inv H; EqDep_subst; econstructor; eauto; eapply IHa; simpl; eauto.
  - inv H0; EqDep_subst.
    + econstructor; eauto.
      * eapply IHa1; simpl; eauto.
      * eapply H; simpl; eauto.
    + econstructor 8; eauto.
      * eapply IHa2; simpl; eauto.
      * eapply H; simpl; eauto.
  - inv H; EqDep_subst; econstructor; eapply IHa; simpl; eauto.
Qed.

Lemma inline_AsyncReadInlines {k : Kind} (a : ActionT type k) rf :
  forall (reads : list string)(HIsAsync : rfRead rf = Async reads)
         (read : string) (HIn : In read reads) o uml retv,
    ESemAction o (inlineAsyncReadFile read rf (Action_EAction a)) uml retv ->
    ESemAction o (Action_EAction (inlineSingle a (getAsyncReads rf read))) uml retv.
Proof.
  induction a; intros; auto; simpl; destruct rf; simpl in *; rewrite HIsAsync in *;
    remember (existsb _ _) as exb; symmetry in Heqexb; destruct exb;
      try rewrite existsb_exists in *; try rewrite existsb_nexists_str in *;
        dest; try rewrite String.eqb_eq in *; subst; try congruence.
  - remember (String.eqb _ _) as strb; symmetry in Heqstrb; destruct strb;
      [rewrite String.eqb_eq in *; destruct Signature_dec
      |rewrite String.eqb_neq in *]; simpl in *.
    + inv H0; EqDep_subst.
      econstructor; simpl; auto.
      * instantiate (1 := uml).
        instantiate (1 := nil); simpl in *.
        intro k; simpl; auto.
      * do 2 econstructor; auto.
        -- apply HRegVal.
        -- econstructor; auto.
      * eapply H; eauto.
      * simpl; reflexivity.
    + inv H0; EqDep_subst.
      econstructor; eauto.
    + subst.
      inv H0; EqDep_subst.
      econstructor; simpl; eauto.
  - inv H0; EqDep_subst.
    econstructor; eauto.
  - inv H0; EqDep_subst.
    econstructor; eauto.
  - inv H0; EqDep_subst.
    econstructor; eauto.
  - inv H0; EqDep_subst.
    econstructor; eauto.
  - inv H; EqDep_subst.
    econstructor; eauto.
  - inv H0; EqDep_subst.
    ++ econstructor; eauto.
    ++ econstructor 8; eauto.
  - inv H; EqDep_subst.
    econstructor; eauto.
Qed.

(* End AsyncReadInline. *)
  
(* Section SyncReqInline. *)

Lemma Extension_inlineSyncReq {k : Kind} (ea : EActionT type k) :
  forall rf (isAddr : bool) (read : SyncRead) (reads : list SyncRead)
         (HIsSync : rfRead rf = Sync isAddr reads)
         (HIn : In read reads) o uml retv,
    ESemAction o ea uml retv ->
    forall newUml,
      ESemAction_meth_collector (getSyncReq rf isAddr read) o uml newUml ->
      ESemAction o (inlineSyncReqFile read rf ea) newUml retv.
Proof.
  destruct rf; simpl in *; destruct rfRead;[intros; discriminate|].
  induction ea; simpl; intros; inv HIsSync; remember (existsb _ _ ) as exb;
    symmetry in Heqexb; destruct exb; try rewrite existsb_nexists_sync in *;
      try congruence; destruct read.
  - inv H0; EqDep_subst.
    inv H1;[discriminate | | | ]; remember (String.eqb _ _ ) as strb;
      symmetry in Heqstrb; destruct strb; try rewrite String.eqb_eq in *;
        try rewrite String.eqb_neq in *; inv HUmlCons;
          try (destruct Signature_dec); subst; unfold getSyncReq in *; destruct isAddr0; 
            try (simpl in *; congruence); EqDep_subst.
    + econstructor; eauto.
    + econstructor; eauto.
    + econstructor; eauto.
    + econstructor; eauto.
    + econstructor; eauto.
    + econstructor; eauto.
    + simpl in *.
      rewrite (Eqdep.EqdepTheory.UIP_refl _ _ e0) in *.
      autorewrite with _word_zero in *; inv HESemAction0; EqDep_subst.
      autorewrite with _word_zero in *; inv HESemAction1; EqDep_subst.
      do 2 (econstructor; simpl in *; eauto).
      * repeat intro.
        destruct (HDisjRegs readRegName); apply H2; simpl; auto.
        rewrite in_map_iff; eexists; split; eauto.
        reflexivity.
      * eapply H; eauto.
        rewrite (unifyWO retV) in *; assumption.
    + simpl in *.
      rewrite (Eqdep.EqdepTheory.UIP_refl _ _ e0) in *.
      autorewrite with _word_zero in *; inv HESemAction0; EqDep_subst.
      autorewrite with _word_zero in *; inv HESemAction1; EqDep_subst.
      autorewrite with _word_zero in *; inv HESemActionCont; EqDep_subst.
      inv HESemAction0; EqDep_subst.
      autorewrite with _word_zero in *; inv HESemAction1; EqDep_subst.
      econstructor; simpl in *; eauto.
      econstructor 15; simpl in *; eauto.
      * repeat intro.
        destruct (HDisjRegs readRegName); apply H2; simpl; auto.
        rewrite in_map_iff; eexists; split; eauto.
        reflexivity.
      * eapply H; eauto.
        rewrite (unifyWO retV) in *; assumption.
  - inv H0; simpl in *; EqDep_subst; econstructor; eauto.
  - inv H0; simpl in *; EqDep_subst.
    + specialize (ESemAction_meth_collector_break _ _ H1) as TMP; dest.
      econstructor.
      * instantiate (1 := x0); instantiate (1 := x); auto.
      * eapply IHea; eauto.
      * eapply H; eauto.
      * assumption.
  - inv H0; simpl in *; EqDep_subst; econstructor; eauto.
  - inv H0; simpl in *; EqDep_subst; econstructor; eauto.
  -inv H; simpl in *; EqDep_subst.
   inv H0; [ | discriminate | discriminate | discriminate].
   inv HUmlCons; econstructor; auto.
   + simpl in *; auto.
   + eapply IHea; eauto.
  - inv H0; simpl in *; EqDep_subst; specialize (ESemAction_meth_collector_break _ _ H1) as TMP; dest.
    + econstructor; eauto.
    + econstructor 8; eauto.
  - inv H; simpl in *; EqDep_subst; econstructor; eauto.
  - inv H; simpl in *; EqDep_subst; econstructor; eauto.
    inv H0; auto; discriminate.
  - inv H0; simpl in *; EqDep_subst; econstructor; eauto.
  - inv H; simpl in *; EqDep_subst.
    + inv H0; inv HUmlCons.
      econstructor; eauto.
    + inv H0; inv HUmlCons.
      econstructor 13; eauto.
  - inv H; simpl in *; EqDep_subst.
    + inv H0; inv HUmlCons.
      econstructor; auto.
      * simpl in *; eauto.
      * eapply IHea; eauto.
    + inv H0; inv HUmlCons.
      econstructor 15; auto.
      * apply HRegVal2.
      * instantiate (1 := newUml1).
        simpl in *; eauto.
      * reflexivity.
      * eapply IHea; eauto.
  - inv H0; simpl in *; EqDep_subst.
    + econstructor; eauto.
    + econstructor 17; eauto.
Qed.

Lemma inlineSyncReq_Extension {k : Kind} (ea : EActionT type k):
  forall rf (read : SyncRead) (isAddr : bool) (reads : list SyncRead)
         (HIsSync : rfRead rf = Sync isAddr reads)
         (HIn : In read reads) o newUml retv,
    ESemAction o (inlineSyncReqFile read rf ea) newUml retv ->
    exists uml,
      ESemAction_meth_collector (getSyncReq rf isAddr read) o uml newUml /\
      ESemAction o ea uml retv.
Proof.
  induction ea; simpl in *; intros rf read; remember rf as rf'; remember read as read';
    destruct rf', read'; intros; simpl in *; rewrite HIsSync in *;
      remember (existsb _ _ ) as exb; symmetry in Heqexb; destruct exb;
        try rewrite existsb_nexists_sync in *; try congruence; revert Heqrf' Heqread' HIsSync.
  - remember (String.eqb _ _) as strb; symmetry in Heqstrb; destruct strb;
      [rewrite String.eqb_eq in *; subst; destruct Signature_dec
      |rewrite String.eqb_neq in *].
    +inv H0; EqDep_subst.
     inv HESemAction; EqDep_subst; intros.
     * assert (Syntax.rfRead rf = Sync true reads) as P0.
       { rewrite <- Heqrf'; reflexivity. }
       rewrite <- Heqrf' in *.
       specialize (H _ _ _ _ _ P0 HIn _ _ _ HESemAction0); dest.
       exists (umMeth (meth, existT SignT (Bit (Nat.log2_up rfIdxNum), Void) (evalExpr e, WO))::x); split.
       -- econstructor 5; auto.
          ++ econstructor; auto.
             ** instantiate (1 := nil); simpl; repeat intro; auto.
             ** econstructor; eauto.
          ++ instantiate (1 := newUml0).
             repeat intro; simpl.
             destruct (string_dec readRegName k); subst; [right | left]; intro.
             ** rewrite in_map_iff in H1; dest.
                destruct x0; simpl in *; subst.
                eapply HDisjRegs; eauto.
             ** destruct H1; congruence.
          ++ reflexivity.
          ++ assumption.
       -- econstructor; eauto.
     * assert (Syntax.rfRead rf = Sync false reads) as P0.
       { rewrite <- Heqrf'; reflexivity. }
       rewrite <- Heqrf' in *.
       specialize (H _ _ _ _ _ P0 HIn _ _ _ HESemAction0); dest.
       exists (umMeth (meth, existT SignT (Bit (Nat.log2_up rfIdxNum), Void) (evalExpr e, WO))::x); split.
       -- econstructor 5; auto.
          ++ instantiate (1 :=
                            [umUpd
                               (readRegName,
                                existT (fullType type) (SyntaxKind (Array rfNum rfData))
                                       (evalExpr
                                          (Var type (SyntaxKind (Array rfNum rfData))
                                               (evalExpr
                                                  (BuildArray
                                                     (fun i0 : Fin.t rfNum =>
                                                        (Var type (SyntaxKind (Array rfIdxNum rfData)) regV @[
                                                               Var type (SyntaxKind (Bit (Nat.log2_up rfIdxNum))) (evalExpr e) +
                                                               Const type ($(proj1_sig (Fin.to_nat i0)))%word])%kami_expr))))))]); simpl; repeat intro; auto.
             econstructor; eauto.
             ** instantiate (2 := nil).
                intro; simpl; auto.
             ** do 2 (econstructor; eauto).
             ** econstructor; auto.
                --- instantiate (1 := nil); repeat intro; auto.
                --- econstructor; eauto.
             ** simpl; auto.
          ++ instantiate (1 := newUml0).
             repeat intro; simpl.
             destruct (string_dec readRegName k); subst; [right | left]; intro.
             ** rewrite in_map_iff in H1; dest.
                destruct x0; simpl in *; subst.
                eapply HDisjRegs; eauto.
             ** destruct H1; congruence.
          ++ reflexivity.
          ++ assumption.
       -- econstructor; eauto.
    + inv H0; EqDep_subst.
      intros.
      assert (Syntax.rfRead rf = Sync isAddr reads) as P0.
      { rewrite <- Heqrf'; reflexivity. }
      rewrite <- Heqrf' in *.
      specialize (H _ _ _ _ _ P0 HIn _ _ _ HESemAction); dest.
      exists (umMeth (meth, existT SignT s (evalExpr e, mret))::x); split.
      * econstructor 4; simpl; eauto.
        unfold getSyncReq; destruct isAddr; simpl; auto.
      * econstructor; eauto.
    + inv H0; EqDep_subst.
      intros.
      assert (Syntax.rfRead rf = Sync isAddr reads) as P0.
      { rewrite <- Heqrf'; reflexivity. }
      rewrite <- Heqrf' in *.
      specialize (H _ _ _ _ _ P0 HIn _ _ _ HESemAction); dest.
      exists (umMeth (meth, existT SignT s (evalExpr e, mret))::x); split.
      * econstructor 3; simpl; eauto.
        unfold getSyncReq; destruct isAddr; simpl; auto.
      * econstructor; eauto.
  - inv H0; EqDep_subst.
    intros.
    assert (Syntax.rfRead rf = Sync isAddr reads) as P0.
    { rewrite <- Heqrf'; reflexivity. }
    rewrite <- Heqrf' in *.
    specialize (H _ _ _ _ _ P0 HIn _ _ _ HESemAction); dest.
    exists x; split; auto.
    econstructor; eauto.
  - inv H0; EqDep_subst.
    intros.
    assert (Syntax.rfRead rf = Sync isAddr reads) as P0.
    { rewrite <- Heqrf'; reflexivity. }
    rewrite <- Heqrf' in *.
    specialize (H _ _ _ _ _ P0 HIn _ _ _ HESemActionCont); dest.
    specialize (IHea _ _ _ _ P0 HIn _ _ _ HESemAction); dest.
    exists (x0 ++ x); split; auto.
    apply ESemAction_meth_collector_stitch; auto.
    econstructor.
    + instantiate (1 := x); instantiate (1 := x0).
      intro k0.
      specialize (HDisjRegs k0).
      specialize (ESemActionMC_Upds_SubList H) as P1.
      specialize (ESemActionMC_Upds_SubList H1) as P2.
      clear - P1 P2 HDisjRegs.
      destruct HDisjRegs;[left | right]; intro; apply H; rewrite in_map_iff in *; dest;
        exists x1; split; auto.
    + apply H2.
    + assumption.
    + reflexivity.
  - inv H0; EqDep_subst.
    intros.
    assert (Syntax.rfRead rf = Sync isAddr reads) as P0.
    { rewrite <- Heqrf'; reflexivity. }
    rewrite <- Heqrf' in *.
    specialize (H _ _ _ _ _ P0 HIn _ _ _ HESemAction); dest.
    exists x; split; auto.
    econstructor; eauto.
  - inv H0; EqDep_subst.
    intros.
    assert (Syntax.rfRead rf = Sync isAddr reads) as P0.
    { rewrite <- Heqrf'; reflexivity. }
    rewrite <- Heqrf' in *.
    specialize (H _ _ _ _ _ P0 HIn _ _ _ HESemAction); dest.
    exists x; split; auto.
    econstructor; eauto.
  - inv H; EqDep_subst.
    intros.
    assert (Syntax.rfRead rf = Sync isAddr reads) as P0.
    { rewrite <- Heqrf'; reflexivity. }
    rewrite <- Heqrf' in *.
    specialize (IHea _ _ _ _ P0 HIn _ _ _ HESemAction); dest.
    exists (umUpd (r, existT (fullType type) k (evalExpr e))::x); split; auto.
    + econstructor; auto.
      * simpl; assumption.
    + econstructor; auto.
      repeat intro; eapply HDisjRegs.
      apply (ESemActionMC_Upds_SubList H _ H1).
  - inv H0; EqDep_subst.
    + intros.
      assert (Syntax.rfRead rf = Sync isAddr reads) as P0.
      { rewrite <- Heqrf'; reflexivity. }
      rewrite <- Heqrf' in *.
      specialize (IHea1 _ _ _ _ P0 HIn _ _ _ HEAction); dest.
      specialize (H _ _ _ _ _ P0 HIn _ _ _ HESemAction); dest.
      exists (x ++ x0); split; auto.
      * apply ESemAction_meth_collector_stitch; auto.
      * econstructor; auto.
        -- intro k0.
           specialize (HDisjRegs k0).
           specialize (ESemActionMC_Upds_SubList H) as P1.
           specialize (ESemActionMC_Upds_SubList H0) as P2.
           clear - P1 P2 HDisjRegs.
           destruct HDisjRegs; [left | right]; intro; apply H; rewrite in_map_iff in *; dest;
             exists x1; split; auto.
        -- apply H1.
        -- assumption.
    + intros.
      assert (Syntax.rfRead rf = Sync isAddr reads) as P0.
      { rewrite <- Heqrf'; reflexivity. }
      rewrite <- Heqrf' in *.
      specialize (IHea2 _ _ _ _ P0 HIn _ _ _ HEAction); dest.
      specialize (H _ _ _ _ _ P0 HIn _ _ _ HESemAction); dest.
      exists (x ++ x0); split; auto.
      * apply ESemAction_meth_collector_stitch; auto.
      * econstructor 8; auto.
        -- intro k0.
           specialize (HDisjRegs k0).
           specialize (ESemActionMC_Upds_SubList H) as P1.
           specialize (ESemActionMC_Upds_SubList H0) as P2.
           clear - P1 P2 HDisjRegs.
           destruct HDisjRegs; [left | right]; intro; apply H; rewrite in_map_iff in *; dest;
             exists x1; split; auto.
        -- apply H1.
        -- assumption.
  - inv H; EqDep_subst.
    intros.
    assert (Syntax.rfRead rf = Sync isAddr reads) as P0.
    { rewrite <- Heqrf'; reflexivity. }
    rewrite <- Heqrf' in *.
    specialize (IHea _ _ _ _ P0 HIn _ _ _ HESemAction); dest.
    exists x; split; auto.
    econstructor; eauto.
  - inv H; EqDep_subst.
    exists nil; split; auto.
    + constructor.
    + econstructor; eauto.
  - inv H0; EqDep_subst.
    intros.
    assert (Syntax.rfRead rf = Sync isAddr reads) as P0.
    { rewrite <- Heqrf'; reflexivity. }
    rewrite <- Heqrf' in *.
    specialize (H _ _ _ _ _ P0 HIn _ _ _ HESemAction); dest.
    exists x; split; auto.
    econstructor; eauto.
  - inv H; EqDep_subst.
    + intros.
      assert (Syntax.rfRead rf = Sync isAddr reads) as P0.
      { rewrite <- Heqrf'; reflexivity. }
      rewrite <- Heqrf' in *.
      specialize (IHea _ _ _ _ P0 HIn _ _ _ HESemAction); dest.
      exists (umUpd (dataArray,
                   existT (fullType type) (SyntaxKind (Array idxNum Data))
                          (evalExpr
                             (fold_left
                                (fun (newArr : Expr type (SyntaxKind (Array idxNum Data))) (i : Fin.t num) =>
                                   (IF ReadArrayConst mask0 i
                                    then newArr @[ idx + Const type ($(proj1_sig (Fin.to_nat i)))%word <-
                                                               ReadArrayConst val i] else newArr)%kami_expr) 
                                (getFins num) (Var type (SyntaxKind (Array idxNum Data)) regV))))::x); split; auto.
      * econstructor; eauto; simpl.
        assumption.
      * econstructor; eauto.
        repeat intro.
        eapply HDisjRegs.
        specialize (ESemActionMC_Upds_SubList H) as P1.
        apply (P1 _ H1).
    + intros.
      assert (Syntax.rfRead rf = Sync isAddr reads) as P0.
      { rewrite <- Heqrf'; reflexivity. }
      rewrite <- Heqrf' in *.
      specialize (IHea _ _ _ _ P0 HIn _ _ _ HESemAction); dest.
      exists (umUpd (dataArray,
                   existT (fullType type) (SyntaxKind (Array idxNum Data))
                          (evalExpr
                             (fold_left
                                (fun (newArr : Expr type (SyntaxKind (Array idxNum Data))) (i : Fin.t num) =>
                                   (newArr @[ idx + Const type ($(proj1_sig (Fin.to_nat i)))%word <-
                                                          ReadArrayConst val i])%kami_expr) (getFins num)
                                (Var type (SyntaxKind (Array idxNum Data)) regV))))::x); split; auto.
      * econstructor; eauto; simpl.
        assumption.
      * econstructor 13; eauto.
        repeat intro.
        eapply HDisjRegs.
        specialize (ESemActionMC_Upds_SubList H) as P1.
        apply (P1 _ H1).
  - inv H; EqDep_subst.
    + intros.
      assert (Syntax.rfRead rf = Sync isAddr0 reads) as P0.
      { rewrite <- Heqrf'; reflexivity. }
      rewrite <- Heqrf' in *.
      specialize (IHea _ _ _ _ P0 HIn _ _ _ HESemAction); dest.
      exists (umUpd (readReg,
                   existT (fullType type) (SyntaxKind (Bit (Nat.log2_up idxNum))) (evalExpr idx)) :: x); split; auto.
      * econstructor; eauto.
        simpl; assumption.
      * econstructor; auto.
        repeat intro.
        eapply HDisjRegs.
        specialize (ESemActionMC_Upds_SubList H) as P1.
        apply (P1 _ H1).
    + intros.
      assert (Syntax.rfRead rf = Sync isAddr0 reads) as P0.
      { rewrite <- Heqrf'; reflexivity. }
      rewrite <- Heqrf' in *.
      specialize (IHea _ _ _ _ P0 HIn _ _ _ HESemAction); dest.
      exists (umUpd (readReg,
                   existT (fullType type) (SyntaxKind (Array num Data))
                          (evalExpr
                             (BuildArray
                                (fun i : Fin.t num =>
                                   (Var type (SyntaxKind (Array idxNum Data)) regV @[
                                          Var type (SyntaxKind (Bit (Nat.log2_up idxNum))) (evalExpr idx) +
                                          Const type ($(proj1_sig (Fin.to_nat i)))%word])%kami_expr)))) :: x); split; auto.
      * econstructor; eauto.
        simpl; assumption.
      * econstructor 15; auto.
        -- assumption.
        -- repeat intro.
           eapply HDisjRegs.
           specialize (ESemActionMC_Upds_SubList H) as P1.
           apply (P1 _ H1).
  - inv H0; EqDep_subst.
    + intros.
      assert (Syntax.rfRead rf = Sync isAddr0 reads) as P0.
      { rewrite <- Heqrf'; reflexivity. }
      rewrite <- Heqrf' in *.
      specialize (H _ _ _ _ _ P0 HIn _ _ _ HESemAction); dest.
      exists x ; split; auto.
      econstructor; eauto.
    + intros.
      assert (Syntax.rfRead rf = Sync isAddr0 reads) as P0.
      { rewrite <- Heqrf'; reflexivity. }
      rewrite <- Heqrf' in *.
      specialize (H _ _ _ _ _ P0 HIn _ _ _ HESemAction); dest.
      exists x ; split; auto.
      econstructor 17; eauto.
Qed.

Corollary inlineSyncReq_congruence {k : Kind} (ea1 ea2 : EActionT type k) :
  (forall o uml retv,
      ESemAction o ea1 uml retv ->
      ESemAction o ea2 uml retv) ->
  forall o newUml retv rf (read : SyncRead) (isAddr : bool) (reads : list SyncRead)
         (HIsSync : rfRead rf = Sync isAddr reads)
         (HIn : In read reads),
    ESemAction o (inlineSyncReqFile read rf ea1) newUml retv ->
    ESemAction o (inlineSyncReqFile read rf ea2) newUml retv.
Proof.
  intros.
  specialize (inlineSyncReq_Extension _ _ _ HIsSync HIn H0) as TMP; dest.
  specialize (H _ _ _ H2).
  apply (Extension_inlineSyncReq _ _ HIsSync HIn H H1).
Qed.

Lemma SyncReqInline_inlines {k : Kind} (a : ActionT type k) :
  forall rf (read : SyncRead) (isAddr : bool) (reads : list SyncRead)
         (HIsSync : rfRead rf = Sync isAddr reads)
         (HIn : In read reads) o uml retv,
    ESemAction o (Action_EAction (inlineSingle a (getSyncReq rf isAddr read))) uml retv ->
    ESemAction o (inlineSyncReqFile read rf (Action_EAction a)) uml retv.
Proof.
  induction a; simpl in *; intros rf read; remember rf as rf'; remember read as read';
    destruct rf', read'; intros; simpl in *; rewrite HIsSync in *;
      remember (existsb _ _ ) as exb; symmetry in Heqexb; destruct exb;
        try rewrite existsb_nexists_sync in *; try congruence; revert Heqrf' Heqread' HIsSync.
  - simpl in *; intros; remember (String.eqb _ _) as strb; symmetry in Heqstrb.
    unfold getSyncReq in *; simpl in *; destruct isAddr, strb;
      [simpl in Heqstrb; rewrite Heqstrb in *; destruct Signature_dec
      |rewrite String.eqb_neq in *
      |simpl in Heqstrb; rewrite Heqstrb; destruct Signature_dec
      |simpl in Heqstrb; rewrite Heqstrb in *]; simpl in *.
    + inv H0; EqDep_subst.
      inv HESemAction; EqDep_subst.
      inv HESemAction0; EqDep_subst.
      inv HESemAction; EqDep_subst.
      intros; do 2 (econstructor; auto).
      * instantiate (1 := newUmlCont).
        repeat intro.
        destruct (HDisjRegs readRegName); apply H1; simpl; auto.
        rewrite in_map_iff; exists (readRegName, v); split; auto.
      * reflexivity.
      * eapply H; simpl; eauto.
    + inv H0; EqDep_subst.
      econstructor; eauto.
      eapply H; simpl; eauto.
    + rewrite <- eqb_neq in Heqstrb; rewrite Heqstrb.
      inv H0; EqDep_subst.
      econstructor; auto.
      eapply H; simpl; eauto.
    + inv H0; EqDep_subst.
      inv HESemAction; EqDep_subst.
      inv HESemAction0; EqDep_subst.
      inv HESemAction; EqDep_subst.
      inv HESemActionCont0; EqDep_subst.
      inv HESemAction0; EqDep_subst.
      inv HESemAction; EqDep_subst.
      econstructor; eauto.
      econstructor 15; auto.
      * apply HRegVal.
      * instantiate (1 := newUmlCont).
        repeat intro.
        destruct (HDisjRegs readRegName); apply H1; simpl; auto.
        rewrite in_map_iff; exists (readRegName, v); split; auto.
      * reflexivity.
      * eapply H; simpl; eauto.
    + inv H0; EqDep_subst.
      econstructor; auto.
      eapply H; simpl; eauto.
    + inv H0; EqDep_subst.
      econstructor; auto.
      eapply H; simpl; eauto.
  - inv H0; EqDep_subst; econstructor; eapply H; simpl; eauto.
  - inv H0; EqDep_subst.
    econstructor; eauto.
    + eapply IHa; simpl; eauto.
    + eapply H; simpl; eauto.
  - inv H0; EqDep_subst; econstructor; eapply H; simpl; eauto.
  - inv H0; EqDep_subst; econstructor; eauto; eapply H; simpl; eauto.
  - inv H; EqDep_subst; econstructor; eauto; eapply IHa; simpl; eauto.
  - inv H0; EqDep_subst.
    + econstructor; eauto.
      * eapply IHa1; simpl; eauto.
      * eapply H; simpl; eauto.
    + econstructor 8; eauto.
      * eapply IHa2; simpl; eauto.
      * eapply H; simpl; eauto.
  - inv H; EqDep_subst; econstructor; eapply IHa; simpl; eauto.
Qed.

Lemma inline_SyncReqInlines {k : Kind} (a : ActionT type k) rf :
  forall (read : SyncRead) (isAddr : bool) (reads : list SyncRead)
         (HIsSync : rfRead rf = Sync isAddr reads)
         (HIn : In read reads) o uml retv,
    ESemAction o (inlineSyncReqFile read rf (Action_EAction a)) uml retv ->
    ESemAction o (Action_EAction (inlineSingle a (getSyncReq rf isAddr read))) uml retv.
Proof.
  intros read isAddr; induction a; intros; auto; simpl; destruct rf; subst;
    simpl in *; rewrite HIsSync in *; unfold getSyncReq in *; destruct read;
      remember (existsb _ _ ) as exb; symmetry in Heqexb; destruct exb;
        try rewrite existsb_nexists_sync in *; try congruence.
  - simpl in *; intros; remember (String.eqb _ _) as strb; symmetry in Heqstrb.
    destruct isAddr, strb; simpl in *; rewrite Heqstrb;
      [destruct Signature_dec | | destruct Signature_dec | ]; simpl in *.
    + inv H0; EqDep_subst.
      inv HESemAction; EqDep_subst; [ |discriminate].
      * econstructor; auto.
        -- instantiate (1 := newUml).
           instantiate (1 := [umUpd
                                (readRegName,
                                 existT (fullType type) (SyntaxKind (Bit (Nat.log2_up rfIdxNum)))
                                        (evalExpr (Var type (SyntaxKind (Bit (Nat.log2_up rfIdxNum))) (evalExpr e))))]).
           intro; simpl.
           destruct (string_dec readRegName k); subst; [right |left ]; intro.
           ++ rewrite in_map_iff in H0; dest; destruct x; subst.
              eapply HDisjRegs; eauto.
           ++ destruct H0; auto.
        -- repeat econstructor; eauto.
           repeat intro; auto.
        -- eapply H; eauto.
        -- reflexivity.
    + inv H0; EqDep_subst.
      econstructor; simpl; eauto.
    + inv H0; EqDep_subst.
      econstructor; simpl; eauto.
    + inv H0; EqDep_subst.
      inv HESemAction; EqDep_subst; [discriminate| ].
      * econstructor; auto.
        -- instantiate (1 := newUml).
           instantiate (1 :=
                          [umUpd
                             (readRegName,
                              existT (fullType type) (SyntaxKind (Array rfNum rfData))
                                     (evalExpr
                                        (Var type (SyntaxKind (Array rfNum rfData))
                                             (evalExpr
                                                (BuildArray
                                                   (fun i0 : Fin.t rfNum =>
                                                      (Var type (SyntaxKind (Array rfIdxNum rfData)) regV @[
                                                             Var type (SyntaxKind (Bit (Nat.log2_up rfIdxNum))) (evalExpr e) +
                                                             Const type ($(proj1_sig (Fin.to_nat i0)))%word])%kami_expr))))))]).
           intro; simpl.
           destruct (string_dec readRegName k); subst; [right |left ]; intro.
           ++ rewrite in_map_iff in H0; dest; destruct x; subst.
              eapply HDisjRegs; eauto.
           ++ destruct H0; auto.
        -- repeat econstructor; eauto.
           repeat intro; auto.
        -- eapply H; eauto.
        -- reflexivity.
    + inv H0; EqDep_subst.
      econstructor; simpl; eauto.
    + inv H0; EqDep_subst.
      econstructor; simpl; eauto.
  - inv H0; EqDep_subst.
    econstructor; eauto.
  - inv H0; EqDep_subst.
    econstructor; eauto.
  - inv H0; EqDep_subst.
    econstructor; eauto.
  - inv H0; EqDep_subst.
    econstructor; eauto.
  - inv H; EqDep_subst.
    econstructor; eauto.
  - inv H0; EqDep_subst.
    ++ econstructor; eauto.
    ++ econstructor 8; eauto.
  - inv H; EqDep_subst.
    econstructor; eauto.
Qed.

(* End SyncReqInline. *)

(* Section SyncResInline. *)

Lemma Extension_inlineSyncRes {k : Kind} (ea : EActionT type k) :
  forall rf (isAddr : bool) (read : SyncRead) (reads : list SyncRead)
         (HIsSync : rfRead rf = Sync isAddr reads)
         (HIn : In read reads) o uml retv,
    ESemAction o ea uml retv ->
    forall newUml,
      ESemAction_meth_collector (getSyncRes rf isAddr read) o uml newUml ->
      ESemAction o (inlineSyncResFile read rf ea) newUml retv.
Proof.
  destruct rf; simpl in *; destruct rfRead;[intros; discriminate|].
  induction ea; simpl; intros; inv HIsSync; remember (existsb _ _ ) as exb;
    symmetry in Heqexb; destruct exb; try rewrite existsb_nexists_sync in *;
      try congruence; destruct read.
  - inv H0; EqDep_subst.
    inv H1;[discriminate | | | ]; remember (String.eqb _ _ ) as strb;
      symmetry in Heqstrb; destruct strb; try rewrite String.eqb_eq in *;
        try rewrite String.eqb_neq in *; inv HUmlCons;
          try (destruct Signature_dec); subst; unfold getSyncReq in *; destruct isAddr0; 
            try (simpl in *; congruence); EqDep_subst.
    + econstructor; eauto.
    + econstructor; eauto.
    + econstructor; eauto.
    + econstructor; eauto.
    + econstructor; eauto.
    + econstructor; eauto.
    + rewrite (Eqdep.EqdepTheory.UIP_refl _ _ e0) in *.
      autorewrite with _word_zero in *; inv HESemAction0; EqDep_subst.
      autorewrite with _word_zero in *; inv HESemAction1; EqDep_subst.
      autorewrite with _word_zero in *; inv HESemAction0; EqDep_subst.
      econstructor; eauto.
    + rewrite (Eqdep.EqdepTheory.UIP_refl _ _ e0) in *.
      autorewrite with _word_zero in *; inv HESemAction0; EqDep_subst.
      autorewrite with _word_zero in *; inv HESemAction1; EqDep_subst.
      econstructor 17; simpl in *; eauto.
  - inv H0; simpl in *; EqDep_subst; econstructor; eauto.
  - inv H0; simpl in *; EqDep_subst.
    + specialize (ESemAction_meth_collector_break _ _ H1) as TMP; dest.
      econstructor.
      * instantiate (1 := x0); instantiate (1 := x); auto.
      * eapply IHea; eauto.
      * eapply H; eauto.
      * assumption.
  - inv H0; simpl in *; EqDep_subst; econstructor; eauto.
  - inv H0; simpl in *; EqDep_subst; econstructor; eauto.
  -inv H; simpl in *; EqDep_subst.
   inv H0; [ | discriminate | discriminate | discriminate].
   inv HUmlCons; econstructor; auto.
   + simpl in *; auto.
   + eapply IHea; eauto.
  - inv H0; simpl in *; EqDep_subst; specialize (ESemAction_meth_collector_break _ _ H1) as TMP; dest.
    + econstructor; eauto.
    + econstructor 8; eauto.
  - inv H; simpl in *; EqDep_subst; econstructor; eauto.
  - inv H; simpl in *; EqDep_subst; econstructor; eauto.
    inv H0; auto; discriminate.
  - inv H0; simpl in *; EqDep_subst; econstructor; eauto.
  - inv H; simpl in *; EqDep_subst.
    + inv H0; inv HUmlCons.
      econstructor; eauto.
    + inv H0; inv HUmlCons.
      econstructor 13; eauto.
  - inv H; simpl in *; EqDep_subst.
    + inv H0; inv HUmlCons.
      econstructor; auto.
      * simpl in *; eauto.
      * eapply IHea; eauto.
    + inv H0; inv HUmlCons.
      econstructor 15; auto.
      * apply HRegVal2.
      * instantiate (1 := newUml1).
        simpl in *; eauto.
      * reflexivity.
      * eapply IHea; eauto.
  - inv H0; simpl in *; EqDep_subst.
    + econstructor; eauto.
    + econstructor 17; eauto.
Qed.

Lemma inlineSyncRes_Extension {k : Kind} (ea : EActionT type k):
  forall rf (read : SyncRead) (isAddr : bool) (reads : list SyncRead)
         (HIsSync : rfRead rf = Sync isAddr reads)
         (HIn : In read reads) o newUml retv,
    ESemAction o (inlineSyncResFile read rf ea) newUml retv ->
    exists uml,
      ESemAction_meth_collector (getSyncRes rf isAddr read) o uml newUml /\
      ESemAction o ea uml retv.
Proof.
  induction ea; simpl in *; intros rf read; remember rf as rf'; remember read as read';
    destruct rf', read'; intros; simpl in *; rewrite HIsSync in *;
      remember (existsb _ _ ) as exb; symmetry in Heqexb; destruct exb;
        try rewrite existsb_nexists_sync in *; try congruence; revert Heqrf' Heqread' HIsSync.
  - remember (String.eqb _ _) as strb; symmetry in Heqstrb; destruct strb;
      [rewrite String.eqb_eq in *; subst; destruct Signature_dec
      |rewrite String.eqb_neq in *].
    +inv H0; EqDep_subst; intros.
     * assert (Syntax.rfRead rf = Sync true reads) as P0.
       { rewrite <- Heqrf'; reflexivity. }
       rewrite <- Heqrf' in *.
       specialize (H _ _ _ _ _ P0 HIn _ _ _ HESemAction); dest.
       exists (umMeth (meth, existT SignT (Void, Array rfNum rfData) (WO, (evalExpr
                                                                            (BuildArray
                                                                               (fun i : Fin.t rfNum =>
                                                                                  (Var type (SyntaxKind (Array rfIdxNum rfData)) regVal @[
                                                                                         Var type (SyntaxKind (Bit (Nat.log2_up rfIdxNum))) idx +
                                                                                         Const type ($(proj1_sig (Fin.to_nat i)))%word])%kami_expr)))))::x); split.
       -- econstructor 5; auto.
          ++ simpl; repeat econstructor; eauto.
          ++ intro; left; intro; auto.
          ++ simpl; reflexivity.
          ++ assumption.
       -- econstructor; eauto.
          rewrite (unifyWO (evalExpr e)); simpl; reflexivity.
     * assert (Syntax.rfRead rf = Sync false reads) as P0.
       { rewrite <- Heqrf'; reflexivity. }
       rewrite <- Heqrf' in *.
       specialize (H _ _ _ _ _ P0 HIn _ _ _ HESemAction); dest.
       exists (umMeth (meth, existT SignT (Void, Array rfNum rfData) (WO, regVal))::x); split.
       -- econstructor 5; auto.
          ++ simpl; repeat econstructor; eauto.
          ++ intro; left; intro; auto.
          ++ simpl; reflexivity.
          ++ assumption.
       -- econstructor; eauto.
          rewrite (unifyWO (evalExpr e)); simpl; reflexivity.
    + inv H0; EqDep_subst.
      intros.
      assert (Syntax.rfRead rf = Sync isAddr reads) as P0.
      { rewrite <- Heqrf'; reflexivity. }
      rewrite <- Heqrf' in *.
      specialize (H _ _ _ _ _ P0 HIn _ _ _ HESemAction); dest.
      exists (umMeth (meth, existT SignT s (evalExpr e, mret))::x); split.
      * econstructor 4; simpl; eauto.
        unfold getSyncRes; destruct isAddr; simpl; auto.
      * econstructor; eauto.
    + inv H0; EqDep_subst.
      intros.
      assert (Syntax.rfRead rf = Sync isAddr reads) as P0.
      { rewrite <- Heqrf'; reflexivity. }
      rewrite <- Heqrf' in *.
      specialize (H _ _ _ _ _ P0 HIn _ _ _ HESemAction); dest.
      exists (umMeth (meth, existT SignT s (evalExpr e, mret))::x); split.
      * econstructor 3; simpl; eauto.
        unfold getSyncRes; destruct isAddr; simpl; auto.
      * econstructor; eauto.
  - inv H0; EqDep_subst.
    intros.
    assert (Syntax.rfRead rf = Sync isAddr reads) as P0.
    { rewrite <- Heqrf'; reflexivity. }
    rewrite <- Heqrf' in *.
    specialize (H _ _ _ _ _ P0 HIn _ _ _ HESemAction); dest.
    exists x; split; auto.
    econstructor; eauto.
  - inv H0; EqDep_subst.
    intros.
    assert (Syntax.rfRead rf = Sync isAddr reads) as P0.
    { rewrite <- Heqrf'; reflexivity. }
    rewrite <- Heqrf' in *.
    specialize (H _ _ _ _ _ P0 HIn _ _ _ HESemActionCont); dest.
    specialize (IHea _ _ _ _ P0 HIn _ _ _ HESemAction); dest.
    exists (x0 ++ x); split; auto.
    apply ESemAction_meth_collector_stitch; auto.
    econstructor.
    + instantiate (1 := x); instantiate (1 := x0).
      intro k0.
      specialize (HDisjRegs k0).
      specialize (ESemActionMC_Upds_SubList H) as P1.
      specialize (ESemActionMC_Upds_SubList H1) as P2.
      clear - P1 P2 HDisjRegs.
      destruct HDisjRegs;[left | right]; intro; apply H; rewrite in_map_iff in *; dest;
        exists x1; split; auto.
    + apply H2.
    + assumption.
    + reflexivity.
  - inv H0; EqDep_subst.
    intros.
    assert (Syntax.rfRead rf = Sync isAddr reads) as P0.
    { rewrite <- Heqrf'; reflexivity. }
    rewrite <- Heqrf' in *.
    specialize (H _ _ _ _ _ P0 HIn _ _ _ HESemAction); dest.
    exists x; split; auto.
    econstructor; eauto.
  - inv H0; EqDep_subst.
    intros.
    assert (Syntax.rfRead rf = Sync isAddr reads) as P0.
    { rewrite <- Heqrf'; reflexivity. }
    rewrite <- Heqrf' in *.
    specialize (H _ _ _ _ _ P0 HIn _ _ _ HESemAction); dest.
    exists x; split; auto.
    econstructor; eauto.
  - inv H; EqDep_subst.
    intros.
    assert (Syntax.rfRead rf = Sync isAddr reads) as P0.
    { rewrite <- Heqrf'; reflexivity. }
    rewrite <- Heqrf' in *.
    specialize (IHea _ _ _ _ P0 HIn _ _ _ HESemAction); dest.
    exists (umUpd (r, existT (fullType type) k (evalExpr e))::x); split; auto.
    + econstructor; auto.
      * simpl; assumption.
    + econstructor; auto.
      repeat intro; eapply HDisjRegs.
      apply (ESemActionMC_Upds_SubList H _ H1).
  - inv H0; EqDep_subst.
    + intros.
      assert (Syntax.rfRead rf = Sync isAddr reads) as P0.
      { rewrite <- Heqrf'; reflexivity. }
      rewrite <- Heqrf' in *.
      specialize (IHea1 _ _ _ _ P0 HIn _ _ _ HEAction); dest.
      specialize (H _ _ _ _ _ P0 HIn _ _ _ HESemAction); dest.
      exists (x ++ x0); split; auto.
      * apply ESemAction_meth_collector_stitch; auto.
      * econstructor; auto.
        -- intro k0.
           specialize (HDisjRegs k0).
           specialize (ESemActionMC_Upds_SubList H) as P1.
           specialize (ESemActionMC_Upds_SubList H0) as P2.
           clear - P1 P2 HDisjRegs.
           destruct HDisjRegs; [left | right]; intro; apply H; rewrite in_map_iff in *; dest;
             exists x1; split; auto.
        -- apply H1.
        -- assumption.
    + intros.
      assert (Syntax.rfRead rf = Sync isAddr reads) as P0.
      { rewrite <- Heqrf'; reflexivity. }
      rewrite <- Heqrf' in *.
      specialize (IHea2 _ _ _ _ P0 HIn _ _ _ HEAction); dest.
      specialize (H _ _ _ _ _ P0 HIn _ _ _ HESemAction); dest.
      exists (x ++ x0); split; auto.
      * apply ESemAction_meth_collector_stitch; auto.
      * econstructor 8; auto.
        -- intro k0.
           specialize (HDisjRegs k0).
           specialize (ESemActionMC_Upds_SubList H) as P1.
           specialize (ESemActionMC_Upds_SubList H0) as P2.
           clear - P1 P2 HDisjRegs.
           destruct HDisjRegs; [left | right]; intro; apply H; rewrite in_map_iff in *; dest;
             exists x1; split; auto.
        -- apply H1.
        -- assumption.
  - inv H; EqDep_subst.
    intros.
    assert (Syntax.rfRead rf = Sync isAddr reads) as P0.
    { rewrite <- Heqrf'; reflexivity. }
    rewrite <- Heqrf' in *.
    specialize (IHea _ _ _ _ P0 HIn _ _ _ HESemAction); dest.
    exists x; split; auto.
    econstructor; eauto.
  - inv H; EqDep_subst.
    exists nil; split; auto.
    + constructor.
    + econstructor; eauto.
  - inv H0; EqDep_subst.
    intros.
    assert (Syntax.rfRead rf = Sync isAddr reads) as P0.
    { rewrite <- Heqrf'; reflexivity. }
    rewrite <- Heqrf' in *.
    specialize (H _ _ _ _ _ P0 HIn _ _ _ HESemAction); dest.
    exists x; split; auto.
    econstructor; eauto.
  - inv H; EqDep_subst.
    + intros.
      assert (Syntax.rfRead rf = Sync isAddr reads) as P0.
      { rewrite <- Heqrf'; reflexivity. }
      rewrite <- Heqrf' in *.
      specialize (IHea _ _ _ _ P0 HIn _ _ _ HESemAction); dest.
      exists (umUpd (dataArray,
                   existT (fullType type) (SyntaxKind (Array idxNum Data))
                          (evalExpr
                             (fold_left
                                (fun (newArr : Expr type (SyntaxKind (Array idxNum Data))) (i : Fin.t num) =>
                                   (IF ReadArrayConst mask0 i
                                    then newArr @[ idx + Const type ($(proj1_sig (Fin.to_nat i)))%word <-
                                                               ReadArrayConst val i] else newArr)%kami_expr) 
                                (getFins num) (Var type (SyntaxKind (Array idxNum Data)) regV))))::x); split; auto.
      * econstructor; eauto; simpl.
        assumption.
      * econstructor; eauto.
        repeat intro.
        eapply HDisjRegs.
        specialize (ESemActionMC_Upds_SubList H) as P1.
        apply (P1 _ H1).
    + intros.
      assert (Syntax.rfRead rf = Sync isAddr reads) as P0.
      { rewrite <- Heqrf'; reflexivity. }
      rewrite <- Heqrf' in *.
      specialize (IHea _ _ _ _ P0 HIn _ _ _ HESemAction); dest.
      exists (umUpd (dataArray,
                   existT (fullType type) (SyntaxKind (Array idxNum Data))
                          (evalExpr
                             (fold_left
                                (fun (newArr : Expr type (SyntaxKind (Array idxNum Data))) (i : Fin.t num) =>
                                   (newArr @[ idx + Const type ($(proj1_sig (Fin.to_nat i)))%word <-
                                                          ReadArrayConst val i])%kami_expr) (getFins num)
                                (Var type (SyntaxKind (Array idxNum Data)) regV))))::x); split; auto.
      * econstructor; eauto; simpl.
        assumption.
      * econstructor 13; eauto.
        repeat intro.
        eapply HDisjRegs.
        specialize (ESemActionMC_Upds_SubList H) as P1.
        apply (P1 _ H1).
  - inv H; EqDep_subst.
    + intros.
      assert (Syntax.rfRead rf = Sync isAddr0 reads) as P0.
      { rewrite <- Heqrf'; reflexivity. }
      rewrite <- Heqrf' in *.
      specialize (IHea _ _ _ _ P0 HIn _ _ _ HESemAction); dest.
      exists (umUpd (readReg,
                   existT (fullType type) (SyntaxKind (Bit (Nat.log2_up idxNum))) (evalExpr idx)) :: x); split; auto.
      * econstructor; eauto.
        simpl; assumption.
      * econstructor; auto.
        repeat intro.
        eapply HDisjRegs.
        specialize (ESemActionMC_Upds_SubList H) as P1.
        apply (P1 _ H1).
    + intros.
      assert (Syntax.rfRead rf = Sync isAddr0 reads) as P0.
      { rewrite <- Heqrf'; reflexivity. }
      rewrite <- Heqrf' in *.
      specialize (IHea _ _ _ _ P0 HIn _ _ _ HESemAction); dest.
      exists (umUpd (readReg,
                   existT (fullType type) (SyntaxKind (Array num Data))
                          (evalExpr
                             (BuildArray
                                (fun i : Fin.t num =>
                                   (Var type (SyntaxKind (Array idxNum Data)) regV @[
                                          Var type (SyntaxKind (Bit (Nat.log2_up idxNum))) (evalExpr idx) +
                                          Const type ($(proj1_sig (Fin.to_nat i)))%word])%kami_expr)))) :: x); split; auto.
      * econstructor; eauto.
        simpl; assumption.
      * econstructor 15; auto.
        -- assumption.
        -- repeat intro.
           eapply HDisjRegs.
           specialize (ESemActionMC_Upds_SubList H) as P1.
           apply (P1 _ H1).
  - inv H0; EqDep_subst.
    + intros.
      assert (Syntax.rfRead rf = Sync isAddr0 reads) as P0.
      { rewrite <- Heqrf'; reflexivity. }
      rewrite <- Heqrf' in *.
      specialize (H _ _ _ _ _ P0 HIn _ _ _ HESemAction); dest.
      exists x ; split; auto.
      econstructor; eauto.
    + intros.
      assert (Syntax.rfRead rf = Sync isAddr0 reads) as P0.
      { rewrite <- Heqrf'; reflexivity. }
      rewrite <- Heqrf' in *.
      specialize (H _ _ _ _ _ P0 HIn _ _ _ HESemAction); dest.
      exists x ; split; auto.
      econstructor 17; eauto.
Qed.

Corollary inlineSyncRes_congruence {k : Kind} (ea1 ea2 : EActionT type k) :
  (forall o uml retv,
      ESemAction o ea1 uml retv ->
      ESemAction o ea2 uml retv) ->
  forall o newUml retv rf (read : SyncRead) (isAddr : bool) (reads : list SyncRead)
         (HIsSync : rfRead rf = Sync isAddr reads)
         (HIn : In read reads),
    ESemAction o (inlineSyncResFile read rf ea1) newUml retv ->
    ESemAction o (inlineSyncResFile read rf ea2) newUml retv.
Proof.
  intros.
  specialize (inlineSyncRes_Extension _ _ _ HIsSync HIn H0) as TMP; dest.
  specialize (H _ _ _ H2).
  apply (Extension_inlineSyncRes _ _ HIsSync HIn H H1).
Qed.

Lemma SyncResInline_inlines {k : Kind} (a : ActionT type k) :
  forall rf (read : SyncRead) (isAddr : bool) (reads : list SyncRead)
         (HIsSync : rfRead rf = Sync isAddr reads)
         (HIn : In read reads) o uml retv,
    ESemAction o (Action_EAction (inlineSingle a (getSyncRes rf isAddr read))) uml retv ->
    ESemAction o (inlineSyncResFile read rf (Action_EAction a)) uml retv.
Proof.
  induction a; simpl in *; intros rf read; remember rf as rf'; remember read as read';
    destruct rf', read'; intros; simpl in *; rewrite HIsSync in *;
      remember (existsb _ _ ) as exb; symmetry in Heqexb; destruct exb;
        try rewrite existsb_nexists_sync in *; try congruence; revert Heqrf' Heqread' HIsSync.
  - simpl in *; intros; remember (String.eqb _ _) as strb; symmetry in Heqstrb.
    unfold getSyncReq in *; simpl in *; destruct isAddr, strb; simpl in *; rewrite Heqstrb;
      [destruct Signature_dec | |destruct Signature_dec | ].
    + inv H0; EqDep_subst.
      inv HESemAction; EqDep_subst.
      inv HESemAction0; EqDep_subst.
      inv HESemAction; EqDep_subst.
      inv HESemAction0; EqDep_subst.
      econstructor; eauto.
      eapply H; simpl; eauto.
    + inv H0; EqDep_subst.
      econstructor; eauto.
      eapply H; simpl; eauto.
    + inv H0; EqDep_subst.
      econstructor; auto.
      eapply H; simpl; eauto.
    + inv H0; EqDep_subst.
      inv HESemAction; EqDep_subst.
      inv HESemAction0; EqDep_subst.
      inv HESemAction; EqDep_subst.
      econstructor 17; eauto.
      eapply H; simpl; eauto.
    + inv H0; EqDep_subst.
      econstructor; auto.
      eapply H; simpl; eauto.
    + inv H0; EqDep_subst.
      econstructor; auto.
      eapply H; simpl; eauto.
  - inv H0; EqDep_subst; econstructor; eapply H; simpl; eauto.
  - inv H0; EqDep_subst.
    econstructor; eauto.
    + eapply IHa; simpl; eauto.
    + eapply H; simpl; eauto.
  - inv H0; EqDep_subst; econstructor; eapply H; simpl; eauto.
  - inv H0; EqDep_subst; econstructor; eauto; eapply H; simpl; eauto.
  - inv H; EqDep_subst; econstructor; eauto; eapply IHa; simpl; eauto.
  - inv H0; EqDep_subst.
    + econstructor; eauto.
      * eapply IHa1; simpl; eauto.
      * eapply H; simpl; eauto.
    + econstructor 8; eauto.
      * eapply IHa2; simpl; eauto.
      * eapply H; simpl; eauto.
  - inv H; EqDep_subst; econstructor; eapply IHa; simpl; eauto.
Qed.

Lemma inline_SyncResInlines {k : Kind} (a : ActionT type k) rf :
  forall (read : SyncRead) (isAddr : bool) (reads : list SyncRead)
         (HIsSync : rfRead rf = Sync isAddr reads)
         (HIn : In read reads) o uml retv,
    ESemAction o (inlineSyncResFile read rf (Action_EAction a)) uml retv ->
    ESemAction o (Action_EAction (inlineSingle a (getSyncRes rf isAddr read))) uml retv.
Proof.
  intros read isAddr; induction a; intros; auto; simpl; destruct rf; subst;
    simpl in *; rewrite HIsSync in *; unfold getSyncReq in *; destruct read;
      remember (existsb _ _ ) as exb; symmetry in Heqexb; destruct exb;
        try rewrite existsb_nexists_sync in *; try congruence.
  - simpl in *; intros; remember (String.eqb _ _) as strb; symmetry in Heqstrb.
    destruct isAddr, strb; simpl in *; rewrite Heqstrb;
      [destruct Signature_dec | | destruct Signature_dec | ]; simpl in *.
    + inv H0; EqDep_subst; [ |discriminate].
      * econstructor; auto.
        -- instantiate (2 := nil).
           intro; auto.
        -- repeat econstructor; eauto.
        -- eapply H; eauto.
        -- reflexivity.
    + inv H0; EqDep_subst.
      econstructor; simpl; eauto.
    + inv H0; EqDep_subst.
      econstructor; simpl; eauto.
    + inv H0; EqDep_subst; [discriminate| ].
      * econstructor; auto.
        -- instantiate (2 := nil).
           intro; auto.
        -- repeat econstructor; eauto.
        -- eapply H; eauto.
        -- reflexivity.
    + inv H0; EqDep_subst.
      econstructor; simpl; eauto.
    + inv H0; EqDep_subst.
      econstructor; simpl; eauto.
  - inv H0; EqDep_subst.
    econstructor; eauto.
  - inv H0; EqDep_subst.
    econstructor; eauto.
  - inv H0; EqDep_subst.
    econstructor; eauto.
  - inv H0; EqDep_subst.
    econstructor; eauto.
  - inv H; EqDep_subst.
    econstructor; eauto.
  - inv H0; EqDep_subst.
    ++ econstructor; eauto.
    ++ econstructor 8; eauto.
  - inv H; EqDep_subst.
    econstructor; eauto.
Qed.

(* End SyncResInline. *)

Lemma inlineEach_inlineSingle_pos (lrf : list RegFileBase):
  forall k ty (a : ActionT ty k) n,
    inlineSingle_pos (listRfMethods lrf) a n = apply_nth (eachRfMethodInliners ty k lrf) a n.
Proof.
  induction lrf; simpl; intros.
  unfold listRfMethods, eachRfMethodInliners; simpl.
  unfold inlineSingle_pos, apply_nth.
  remember (nth_error _ _) as err0; remember (nth_error (nil : list (_ -> _)) _ ) as err1.
  symmetry in Heqerr0, Heqerr1.
  destruct err0; [apply nth_error_In in Heqerr0; inv Heqerr0|].
  destruct err1; [apply nth_error_In in Heqerr1; inv Heqerr1| reflexivity].
  unfold listRfMethods, eachRfMethodInliners, inlineSingle_pos, apply_nth in *; simpl.
  destruct (le_lt_dec (length (getRegFileMethods a)) n).
  - repeat rewrite nth_error_app2; try rewrite map_length; auto.
  - repeat rewrite nth_error_app1; try rewrite map_length; auto.
    remember (nth_error _ _) as err0; remember (nth_error (map _ _) _) as err1.
    symmetry in Heqerr0, Heqerr1.
    destruct err0.
    + eapply (map_nth_error (fun f a' => inlineSingle a' f (k:=k))) in Heqerr0.
      rewrite Heqerr1 in Heqerr0; rewrite Heqerr0; reflexivity.
    + rewrite (nth_error_map_None_iff (fun f a' => @inlineSingle ty k a' f)) in Heqerr0.
      setoid_rewrite Heqerr0 in Heqerr1; rewrite <- Heqerr1; reflexivity.
Qed.

Lemma inlineEach_inlineSome_pos xs :
  forall (lrf : list RegFileBase) k ty (a : ActionT ty k),
    fold_left (inlineSingle_pos (listRfMethods lrf)) xs a = fold_left (apply_nth (eachRfMethodInliners ty k lrf)) xs a.
Proof.
  induction xs; simpl; auto; intros.
  rewrite inlineEach_inlineSingle_pos, IHxs; reflexivity.
Qed.

Lemma EgetRegFileMapMethods_getRegFileMethods_len k ty (rf : RegFileBase) :
  length (EgetRegFileMapMethods ty k rf) = length (getRegFileMethods rf).
Proof.
  unfold EgetRegFileMapMethods, getRegFileMethods.
  destruct rf, rfRead; simpl.
  - induction reads; simpl; auto.
    rewrite <- IHreads.
    do 2 apply f_equal.
    do 2 rewrite map_length; reflexivity.
  - apply f_equal.
    destruct isAddr; simpl; repeat rewrite app_length; repeat rewrite map_length; reflexivity.
Qed.

Lemma inlineEach_SingleRf_inlineEeach (rf : RegFileBase) :
  forall n k (a : ActionT type k),
    (forall o uml retV,
        ESemAction o (Action_EAction (apply_nth (map (fun f a' => @inlineSingle type k a' f) (getRegFileMethods rf)) a n)) uml retV ->
        ESemAction o (apply_nth (EgetRegFileMapMethods type k rf) (Action_EAction a) n) uml retV).
Proof.
  unfold getRegFileMethods, EgetRegFileMapMethods; destruct rf, rfRead; simpl.
  - unfold apply_nth in *; destruct n; simpl in *; intros.
    + eapply WrInline_inlines; auto.
    + unfold readRegFile in H.
      remember (nth_error _ _) as err0.
      remember (nth_error (map (fun x => _) reads) n) as err1.
      symmetry in Heqerr0, Heqerr1.
      destruct err1.
      * rewrite nth_error_map_iff in Heqerr1; dest.
        rewrite <- H1.
        destruct err0.
        -- rewrite nth_error_map_iff in Heqerr0; dest.
           rewrite nth_error_map_iff in H2; dest.
           rewrite <- H4 in H3.
           eapply AsyncReadInline_inlines; simpl; eauto using nth_error_In.
           rewrite H0 in H2; inv H2; simpl; assumption.
        -- exfalso.
           repeat rewrite <- nth_error_map_None_iff in Heqerr0.
           rewrite H0 in Heqerr0; inv Heqerr0.
      * rewrite <- nth_error_map_None_iff in Heqerr1.
        destruct err0;[|assumption].
        exfalso.
        rewrite nth_error_map_iff in Heqerr0; dest.
        rewrite nth_error_map_iff in H0; dest.
        rewrite H0 in Heqerr1; discriminate.
  - unfold apply_nth in *; destruct n; simpl in *; intros.
    + eapply WrInline_inlines; auto.
    + unfold readSyncRegFile in H.
      remember (nth_error _ _) as err0.
      remember (nth_error ((map _ _ ) ++ (map _ _ )) _) as err1.
      symmetry in Heqerr0, Heqerr1.
      destruct (le_lt_dec (length reads) n), isAddr.
      * rewrite nth_error_app2 in Heqerr1; rewrite map_length in *;[| assumption].
        rewrite map_app in Heqerr0.
        rewrite nth_error_app2 in Heqerr0; repeat rewrite map_length in *; [| assumption].
        destruct err1.
        -- rewrite nth_error_map_iff in Heqerr1; dest.
           rewrite <- H1.
           destruct err0.
           ++ rewrite nth_error_map_iff in Heqerr0; dest.
              rewrite nth_error_map_iff in H2; dest.
              rewrite <- H4 in H3.
              eapply SyncResInline_inlines; simpl; eauto using nth_error_In.
              rewrite H0 in H2; inv H2; simpl; assumption.
           ++ exfalso.
              repeat rewrite <- nth_error_map_None_iff in Heqerr0.
              rewrite H0 in Heqerr0; inv Heqerr0.
        -- rewrite <- nth_error_map_None_iff in Heqerr1.
           destruct err0;[|assumption].
           exfalso.
           rewrite nth_error_map_iff in Heqerr0; dest.
           rewrite nth_error_map_iff in H0; dest.
           rewrite H0 in Heqerr1; discriminate.
      * rewrite nth_error_app2 in Heqerr1; rewrite map_length in *;[| assumption].
        rewrite map_app in Heqerr0.
        rewrite nth_error_app2 in Heqerr0; repeat rewrite map_length in *; [| assumption].
        destruct err1.
        -- rewrite nth_error_map_iff in Heqerr1; dest.
           rewrite <- H1.
           destruct err0.
           ++ rewrite nth_error_map_iff in Heqerr0; dest.
              rewrite nth_error_map_iff in H2; dest.
              rewrite <- H4 in H3.
              eapply SyncResInline_inlines; simpl; eauto using nth_error_In.
              rewrite H0 in H2; inv H2; simpl; assumption.
           ++ exfalso.
              repeat rewrite <- nth_error_map_None_iff in Heqerr0.
              rewrite H0 in Heqerr0; inv Heqerr0.
        -- rewrite <- nth_error_map_None_iff in Heqerr1.
           destruct err0;[|assumption].
           exfalso.
           rewrite nth_error_map_iff in Heqerr0; dest.
           rewrite nth_error_map_iff in H0; dest.
           rewrite H0 in Heqerr1; discriminate.
      * rewrite nth_error_app1 in Heqerr1;[| rewrite map_length in *; assumption].
        rewrite map_app in Heqerr0.
        rewrite nth_error_app1 in Heqerr0; repeat rewrite map_length in *; [| assumption].
        destruct err1.
        -- rewrite nth_error_map_iff in Heqerr1; dest.
           rewrite <- H1.
           destruct err0.
           ++ rewrite nth_error_map_iff in Heqerr0; dest.
              rewrite nth_error_map_iff in H2; dest.
              rewrite <- H4 in H3.
              eapply SyncReqInline_inlines; simpl; eauto using nth_error_In.
              rewrite H0 in H2; inv H2; simpl; assumption.
           ++ exfalso.
              repeat rewrite <- nth_error_map_None_iff in Heqerr0.
              rewrite H0 in Heqerr0; inv Heqerr0.
        -- rewrite <- nth_error_map_None_iff in Heqerr1.
           destruct err0;[|assumption].
           exfalso.
           rewrite nth_error_map_iff in Heqerr0; dest.
           rewrite nth_error_map_iff in H0; dest.
           rewrite H0 in Heqerr1; discriminate.
      * rewrite nth_error_app1 in Heqerr1;[| rewrite map_length in *; assumption].
        rewrite map_app in Heqerr0.
        rewrite nth_error_app1 in Heqerr0; repeat rewrite map_length in *; [| assumption].
        destruct err1.
        -- rewrite nth_error_map_iff in Heqerr1; dest.
           rewrite <- H1.
           destruct err0.
           ++ rewrite nth_error_map_iff in Heqerr0; dest.
              rewrite nth_error_map_iff in H2; dest.
              rewrite <- H4 in H3.
              eapply SyncReqInline_inlines; simpl; eauto using nth_error_In.
              rewrite H0 in H2; inv H2; simpl; assumption.
           ++ exfalso.
              repeat rewrite <- nth_error_map_None_iff in Heqerr0.
              rewrite H0 in Heqerr0; inv Heqerr0.
        -- rewrite <- nth_error_map_None_iff in Heqerr1.
           destruct err0;[|assumption].
           exfalso.
           rewrite nth_error_map_iff in Heqerr0; dest.
           rewrite nth_error_map_iff in H0; dest.
           rewrite H0 in Heqerr1; discriminate.
Qed.

Lemma inlineEeach_SingleRf_inlineEach (rf : RegFileBase) :
  forall n k (a : ActionT type k),
    (forall o uml retV,
        ESemAction o (apply_nth (EgetRegFileMapMethods type k rf) (Action_EAction a) n) uml retV
        -> ESemAction o (Action_EAction (apply_nth (map (fun f a' => @inlineSingle type k a' f) (getRegFileMethods rf)) a n)) uml retV).
Proof.
  unfold getRegFileMethods, EgetRegFileMapMethods; destruct rf, rfRead; simpl.
  - unfold apply_nth in *; destruct n; simpl in *; intros.
    + specialize (inline_WrInlines _ _ H); auto.
    + unfold readRegFile.
      remember (nth_error _ _) as err0.
      remember (nth_error (map _ (map _ reads)) n) as err1.
      symmetry in Heqerr0, Heqerr1.
      destruct err1.
      * rewrite nth_error_map_iff in Heqerr1; dest.
        rewrite <- H1.
        destruct err0.
        -- rewrite nth_error_map_iff in Heqerr0; dest.
           rewrite nth_error_map_iff in H0; dest.
           rewrite <- H4.
           rewrite <- H3 in H.
           assert (rfRead
                     {|
                       rfIsWrMask := rfIsWrMask;
                       rfNum := rfNum;
                       rfDataArray := rfDataArray;
                       rfRead := Async reads;
                       rfWrite := rfWrite;
                       rfIdxNum := rfIdxNum;
                       rfData := rfData;
                       rfInit := rfInit |} = Async reads) as P0.
           { auto. }
           specialize (inline_AsyncReadInlines _ _ P0 _  (nth_error_In _ _ H2) H) as P1.
           unfold getAsyncReads in P1; simpl in *.
           rewrite H0 in H2; inv H2; assumption.
        -- exfalso.
           repeat rewrite <- nth_error_map_None_iff in Heqerr0.
           rewrite nth_error_map_iff in H0; dest.
           rewrite H0 in Heqerr0; inv Heqerr0.
      * rewrite <- nth_error_map_None_iff in Heqerr1.
        destruct err0;[|assumption].
        exfalso.
        rewrite <- nth_error_map_None_iff in Heqerr1.
        rewrite nth_error_map_iff in Heqerr0; dest.
        rewrite H0 in Heqerr1; discriminate.
  - unfold apply_nth in *; destruct n; simpl in *; intros.
    + specialize (inline_WrInlines _ _ H); auto.
    + unfold readSyncRegFile.
      remember (nth_error _ _) as err0.
      remember (nth_error (map _ (if isAddr then _ else _ )) _) as err1.
      symmetry in Heqerr0, Heqerr1.
      destruct (le_lt_dec (length reads) n), isAddr; rewrite map_app in *.
      * rewrite nth_error_app2 in Heqerr1; repeat rewrite map_length in *;[| assumption].
        rewrite nth_error_app2 in Heqerr0; repeat rewrite map_length in *; [| assumption].
        destruct err1.
        -- rewrite nth_error_map_iff in Heqerr1; dest.
           rewrite <- H1.
           destruct err0.
           ++ rewrite nth_error_map_iff in Heqerr0; dest.
              rewrite nth_error_map_iff in H0; dest.
              rewrite <- H4.
              rewrite <- H3 in H.
              assert (rfRead
                        {|
                          rfIsWrMask := rfIsWrMask;
                          rfNum := rfNum;
                          rfDataArray := rfDataArray;
                          rfRead := Sync true reads;
                          rfWrite := rfWrite;
                          rfIdxNum := rfIdxNum;
                          rfData := rfData;
                          rfInit := rfInit |} = Sync true reads) as P0.
              { auto. }
              specialize (inline_SyncResInlines _ _ _ P0 (nth_error_In _ _ H2) H) as P1.
              simpl in *.
              rewrite H0 in H2; inv H2; simpl; assumption.
           ++ exfalso.
              rewrite <- nth_error_map_None_iff in Heqerr0.
              rewrite nth_error_map_iff in H0; dest.
              rewrite H0 in Heqerr0; inv Heqerr0.
        -- rewrite <- nth_error_map_None_iff in Heqerr1.
           destruct err0;[|assumption].
           exfalso.
           rewrite nth_error_map_iff in Heqerr0; dest.
           rewrite <- nth_error_map_None_iff in Heqerr1.
           rewrite H0 in Heqerr1; discriminate.
      * rewrite nth_error_app2 in Heqerr1; repeat rewrite map_length in *;[| assumption].
        rewrite nth_error_app2 in Heqerr0; rewrite map_length in *; [| assumption].
        destruct err1.
        -- rewrite nth_error_map_iff in Heqerr1; dest.
           rewrite <- H1.
           destruct err0.
           ++ rewrite nth_error_map_iff in Heqerr0; dest.
              rewrite nth_error_map_iff in H0; dest.
              rewrite <- H4.
              rewrite <- H3 in H. 
              assert (rfRead
                        {|
                          rfIsWrMask := rfIsWrMask;
                          rfNum := rfNum;
                          rfDataArray := rfDataArray;
                          rfRead := Sync false reads;
                          rfWrite := rfWrite;
                          rfIdxNum := rfIdxNum;
                          rfData := rfData;
                          rfInit := rfInit |} = Sync false reads) as P0.
              { auto. }
              specialize (inline_SyncResInlines _ _ _ P0 (nth_error_In _ _ H2) H) as P1.
              rewrite H0 in H2; inv H2; simpl; assumption.
           ++ exfalso.
              repeat rewrite <- nth_error_map_None_iff in Heqerr0.
              rewrite nth_error_map_iff in H0; dest.
              rewrite H0 in Heqerr0; inv Heqerr0.
        -- rewrite <- nth_error_map_None_iff in Heqerr1.
           destruct err0;[|assumption].
           exfalso.
           rewrite nth_error_map_iff in Heqerr0; dest.
           rewrite <- nth_error_map_None_iff in Heqerr1; dest.
           rewrite H0 in Heqerr1; discriminate.
      * rewrite nth_error_app1 in Heqerr1;[| repeat rewrite map_length in *; assumption].
        rewrite nth_error_app1 in Heqerr0; repeat rewrite map_length in *; [| assumption].
        destruct err1.
        -- rewrite nth_error_map_iff in Heqerr1; dest.
           rewrite <- H1.
           destruct err0.
           ++ rewrite nth_error_map_iff in Heqerr0; dest.
              rewrite nth_error_map_iff in H0; dest.
              rewrite <- H4.
              rewrite <- H3 in H. 
              assert (rfRead
                        {|
                          rfIsWrMask := rfIsWrMask;
                          rfNum := rfNum;
                          rfDataArray := rfDataArray;
                          rfRead := Sync true reads;
                          rfWrite := rfWrite;
                          rfIdxNum := rfIdxNum;
                          rfData := rfData;
                          rfInit := rfInit |} = Sync true reads) as P0.
              { auto. }
              specialize (inline_SyncReqInlines _ _ _ P0 (nth_error_In _ _ H2) H) as P1.
              rewrite H0 in H2; inv H2; simpl; assumption.
           ++ exfalso.
              rewrite <- nth_error_map_None_iff in Heqerr0.
              rewrite nth_error_map_iff in H0; dest.
              rewrite H0 in Heqerr0; inv Heqerr0.
        -- rewrite <- nth_error_map_None_iff in Heqerr1.
           destruct err0;[|assumption].
           exfalso.
           rewrite nth_error_map_iff in Heqerr0; dest.
           rewrite <- nth_error_map_None_iff in Heqerr1.
           rewrite H0 in Heqerr1; discriminate.
      * rewrite nth_error_app1 in Heqerr1;[| repeat rewrite map_length in *; assumption].
        rewrite nth_error_app1 in Heqerr0; repeat rewrite map_length in *; [| assumption].
        destruct err1.
        -- rewrite nth_error_map_iff in Heqerr1; dest.
           rewrite <- H1.
           destruct err0.
           ++ rewrite nth_error_map_iff in Heqerr0; dest.
              rewrite nth_error_map_iff in H0; dest.
              rewrite <- H4.
              rewrite <- H3 in H. 
              assert (rfRead
                        {|
                          rfIsWrMask := rfIsWrMask;
                          rfNum := rfNum;
                          rfDataArray := rfDataArray;
                          rfRead := Sync false reads;
                          rfWrite := rfWrite;
                          rfIdxNum := rfIdxNum;
                          rfData := rfData;
                          rfInit := rfInit |} = Sync false reads) as P0.
              { auto. }
              specialize (inline_SyncReqInlines _ _ _ P0 (nth_error_In _ _ H2) H) as P1.
              rewrite H0 in H2; inv H2; simpl; assumption.
           ++ exfalso.
              rewrite <- nth_error_map_None_iff in Heqerr0.
              rewrite nth_error_map_iff in H0; dest.
              rewrite H0 in Heqerr0; inv Heqerr0.
        -- rewrite <- nth_error_map_None_iff in Heqerr1.
           destruct err0;[|assumption].
           exfalso.
           rewrite nth_error_map_iff in Heqerr0; dest.
           rewrite <- nth_error_map_None_iff in Heqerr1; dest.
           rewrite H0 in Heqerr1; discriminate.
Qed.

Lemma inlineEach_Singlelist_inlineEeach (lrf : list RegFileBase):
  forall n k (a : ActionT type k),
    (forall o uml retV, ESemAction o (Action_EAction (apply_nth (eachRfMethodInliners _ k lrf) a n)) uml retV
                        -> ESemAction o (apply_nth (EeachRfMethodInliners _ k lrf) (Action_EAction a) n) uml retV).
Proof.
  induction lrf; intros.
  - unfold eachRfMethodInliners, EeachRfMethodInliners in *; simpl in *.
    unfold apply_nth in *.
    rewrite nth_error_nil_None; rewrite nth_error_nil_None in H.
    assumption.
  - unfold eachRfMethodInliners, EeachRfMethodInliners in *.
    destruct (le_lt_dec (length (getRegFileMethods a)) n).
    + unfold apply_nth in *; simpl in *.
      rewrite nth_error_app2 in H; try rewrite map_length in *; auto.
      rewrite app_comm_cons; rewrite nth_error_app2.
      * fold (EgetRegFileMapMethods type k a).
        rewrite EgetRegFileMapMethods_getRegFileMethods_len.
        apply IHlrf; auto.
      * erewrite <-EgetRegFileMapMethods_getRegFileMethods_len in l; eauto.
    + unfold apply_nth in *; simpl in *.
      rewrite nth_error_app1 in H; try rewrite map_length in *; auto.
      rewrite app_comm_cons; rewrite nth_error_app1.
      * eapply inlineEach_SingleRf_inlineEeach.
        assumption.
      * erewrite <-EgetRegFileMapMethods_getRegFileMethods_len in l; eauto.
Qed.

Lemma inlineEeach_Singlelist_inlineEach (lrf : list RegFileBase):
  forall n k (a : ActionT type k),
    (forall o uml retV,  ESemAction o (apply_nth (EeachRfMethodInliners _ k lrf) (Action_EAction a) n) uml retV
                         ->ESemAction o (Action_EAction (apply_nth (eachRfMethodInliners _ k lrf) a n)) uml retV).
Proof.
  induction lrf; intros.
  - unfold eachRfMethodInliners, EeachRfMethodInliners in *; simpl in *.
    unfold apply_nth in *.
    rewrite nth_error_nil_None; rewrite nth_error_nil_None in H.
    assumption.
  - unfold eachRfMethodInliners, EeachRfMethodInliners in *.
    destruct (le_lt_dec (length (getRegFileMethods a)) n).
    + unfold apply_nth in *; simpl in *.
      rewrite nth_error_app2; try rewrite map_length in *; auto.
      rewrite app_comm_cons, nth_error_app2 in H.
      * fold (EgetRegFileMapMethods type k a) in H.
        rewrite EgetRegFileMapMethods_getRegFileMethods_len in H.
        apply IHlrf; auto.
      * erewrite <- EgetRegFileMapMethods_getRegFileMethods_len in l; eauto.
    + unfold apply_nth in *; simpl in *.
      rewrite nth_error_app1; try rewrite map_length in *; auto.
      rewrite app_comm_cons, nth_error_app1 in H.
      * eapply inlineEeach_SingleRf_inlineEach.
        assumption.
      * erewrite <-EgetRegFileMapMethods_getRegFileMethods_len in l; eauto.
Qed.

Lemma inlineEeach_Single_Congruence (rf : RegFileBase) :
  forall n k (ea1 ea2 : EActionT type k),
    (forall o uml retV, ESemAction o ea1 uml retV -> ESemAction o ea2 uml retV) ->
    (forall o uml retV,
        ESemAction o (apply_nth (EgetRegFileMapMethods type k rf) ea1 n) uml retV ->
        ESemAction o (apply_nth (EgetRegFileMapMethods type k rf) ea2 n) uml retV).
Proof.
  unfold EgetRegFileMapMethods; destruct rf, rfRead; simpl.
  - unfold apply_nth in *; destruct n; simpl in *; intros.
    + eapply inlineWrites_congruence; eauto.
    + remember (nth_error _ _) as err0.
      symmetry in Heqerr0; destruct err0; eauto.
      rewrite nth_error_map_iff in Heqerr0; dest.
      rewrite <- H2 in *.
      eapply inlineAsyncRead_congruence; simpl; eauto using nth_error_In.
  - unfold apply_nth in *; destruct n; simpl in *; intros.
    + eapply inlineWrites_congruence; eauto.
    + remember (nth_error _ _) as err0.
      symmetry in Heqerr0.
      destruct (le_lt_dec (length reads) n).
      * rewrite nth_error_app2 in Heqerr0; rewrite map_length in *; [| assumption].
        destruct err0; eauto.
        rewrite nth_error_map_iff in Heqerr0; dest.
        rewrite <- H2 in *.
        eapply inlineSyncRes_congruence; simpl in *; eauto using nth_error_In.
      * rewrite nth_error_app1 in Heqerr0;[| rewrite map_length; assumption].
        destruct err0; eauto.
        rewrite nth_error_map_iff in Heqerr0; dest.
        rewrite <- H2 in *.
        eapply inlineSyncReq_congruence; simpl in *; eauto using nth_error_In.
Qed.

Lemma inlineEeach_SingleList_Congruence (lrf : list RegFileBase) :
  forall n k (ea1 ea2 : EActionT type k),
    (forall o uml retV, ESemAction o ea1 uml retV -> ESemAction o ea2 uml retV) ->
    (forall o uml retV,
        ESemAction o (apply_nth (EeachRfMethodInliners type k lrf) ea1 n) uml retV
        -> ESemAction o (apply_nth (EeachRfMethodInliners type k lrf) ea2 n) uml retV).
Proof.
  induction lrf; unfold EeachRfMethodInliners; simpl; intros.
  - unfold apply_nth in *.
    rewrite nth_error_nil_None in *; auto.
  - unfold apply_nth in *; rewrite app_comm_cons in *.
    destruct (le_lt_dec (length (EgetRegFileMapMethods type k a)) n).
    + rewrite nth_error_app2 in *; eauto.
    + rewrite nth_error_app1 in *; eauto.
      eapply inlineEeach_Single_Congruence; eauto.
Qed.

Lemma inlineEeach_Some_Congruence xs :
  forall (lrf : list RegFileBase) k (ea1 ea2 : EActionT type k),
    (forall o uml retV, ESemAction o ea1 uml retV -> ESemAction o ea2 uml retV) ->
    (forall o uml retV,
        ESemAction o (fold_left (apply_nth (EeachRfMethodInliners type k lrf)) xs ea1) uml retV ->
        ESemAction o (fold_left (apply_nth (EeachRfMethodInliners type k lrf)) xs ea2) uml retV).
Proof.
  induction xs; simpl; eauto; intros.
  eapply IHxs.
  - eapply inlineEeach_SingleList_Congruence; eauto.
  - assumption.
Qed.

Lemma inlineEach_Somelist_inlineEeach (lrf : list RegFileBase) xs :
  forall  k (a : ActionT type k),
    (forall o uml retV, ESemAction o (Action_EAction (fold_left (apply_nth (eachRfMethodInliners _ k lrf)) xs a)) uml retV
                        -> ESemAction o (fold_left (apply_nth (EeachRfMethodInliners _ k lrf)) xs (Action_EAction a)) uml retV).
Proof.
  induction xs; simpl in *; auto; intros.
  eapply inlineEeach_Some_Congruence.
  - eapply inlineEach_Singlelist_inlineEeach.
  - eapply IHxs; assumption.
Qed.

Lemma inlineEeach_Somelist_inlineEach (lrf : list RegFileBase) xs :
  forall  k (a : ActionT type k),
    (forall o uml retV, ESemAction o (fold_left (apply_nth (EeachRfMethodInliners _ k lrf)) xs (Action_EAction a)) uml retV
                        -> ESemAction o (Action_EAction (fold_left (apply_nth (eachRfMethodInliners _ k lrf)) xs a)) uml retV).
Proof.
  induction xs; simpl in *; auto; intros.
  eapply inlineEeach_Some_Congruence in H.
  - eapply IHxs; apply H.
  - eapply inlineEeach_Singlelist_inlineEach.
Qed.

Lemma ESameOldLoop o:
  forall rules old upds calls retl lrf,
    @SemCompActionT Void (compileRulesRf type (o, nil) (rev rules) lrf) (old, upds) calls retl ->
    o = old.
Proof.
  induction rules; simpl in *; intros.
  - rewrite (unifyWO retl) in H.
    inv H; EqDep_subst.
    inv HRegMapWf.
    inv H.
    reflexivity.
  - unfold compileRulesRf, compileActionsRf in *; simpl in *.
    setoid_rewrite <- fold_left_rev_right in IHrules.
    rewrite map_app, <- fold_left_rev_right, map_rev in *.
    simpl in *.
    rewrite rev_app_distr, rev_involutive in *; simpl in *.
    rewrite (unifyWO retl) in H.
    inv H; EqDep_subst.
    apply Eqdep.EqdepTheory.inj_pair2 in H4; subst; simpl in *.
    destruct regMap_a.
    specialize (IHrules _ _ _ _ _ HSemCompActionT_a); subst.
    rewrite (unifyWO WO) in HSemCompActionT_cont.
    inv HSemCompActionT_cont; simpl in *; EqDep_subst.
    rewrite (unifyWO val_a0) in HSemCompActionT_a0.
    inv HSemCompActionT_a0; simpl in *; EqDep_subst.
    destruct regMap_a; inv HRegMapWf; inv H; inv HSemRegMap.
    apply (ESameOldAction _ _ _ _ (SemVarRegMap _) HSemCompActionT_cont0).
Qed.

Lemma CompileRules_Congruence rules  (b : BaseModule) (lrf : list RegFileBase) : 
  let m := inlineAll_All_mod (mergeSeparatedSingle b lrf) in
  forall  o upds calls retl
          (HConsist : getKindAttr o = getKindAttr (getRegisters m))
          (HSubList1 : SubList (listRfMethods lrf) (getMethods m))
          (HSubList2 : SubList rules (getRules b))
          (HWfMod : WfMod (mergeSeparatedSingle b lrf)),
    SemCompActionT (compileRulesRf type (o, []) (rev rules) lrf) (o, upds) calls retl ->
    SemCompActionT
      (compileRules type (o, []) (map (inline_Rules (getAllMethods (mergeSeparatedBaseFile lrf))
                                                    (seq 0 (Datatypes.length (getAllMethods (mergeSeparatedBaseFile lrf))))) (rev rules))) (o, upds) calls retl.
Proof.
  unfold compileRulesRf, compileRules, compileActionsRf, compileActions.
  setoid_rewrite <-fold_left_rev_right at 2 3; repeat setoid_rewrite <-map_rev; repeat rewrite rev_involutive.
  induction rules; simpl; intros; auto.
  rewrite (unifyWO retl) in H3; inv H3; simpl in *; EqDep_subst.
  rewrite (unifyWO WO) in HSemCompActionT_cont;
    inv HSemCompActionT_cont; simpl in *; EqDep_subst.
  destruct regMap_a, regMap_a0.
  rewrite (unifyWO val_a0) in HSemCompActionT_a0;
    inv HSemCompActionT_a0; simpl in *; EqDep_subst.
  specialize (ESameOldAction _ _ _ _ (SemVarRegMap _) HSemCompActionT_cont0) as TMP; subst.
  unfold WfRegMapExpr in *; dest.
  inv H3; inv HSemRegMap.
  rewrite <- (app_nil_l calls_cont0).
  assert (SubList rules (getRules b)) as P0.
  { repeat intro; apply H1; right; assumption. }
  repeat (econstructor; eauto); try (apply H4; auto); destruct a; simpl.
  unfold preCompileRegFiles in *; simpl in *.
  assert (allMeths_merge_listRf : forall lrf', getAllMethods (mergeSeparatedBaseFile lrf') = listRfMethods lrf').
  { clear.
    induction lrf'; simpl; unfold listRfMethods; simpl; eauto.
    rewrite IHlrf'; reflexivity. }
  rewrite allMeths_merge_listRf, inlineEach_inlineSome_pos, <- Extension_Compiles_iff.
  assert (NoDup (map fst o)) as P1.
  { unfold mergeSeparatedSingle in H2; inv H2.
    rewrite (getKindAttr_map_fst _ _ H), map_app, NoDup_app_iff; repeat split.
    - inv HWf1; unfold WfBaseModule in HWfBaseModule; dest; assumption.
    - clear - HWf2.
      induction lrf; simpl in *; [constructor|].
      inv HWf2; inv HWf1; unfold WfBaseModule in *; dest.
      rewrite map_app, NoDup_app_iff; repeat split; auto.
      + repeat intro.
        specialize (HDisjRegs a0); clear - HDisjRegs H4 H5; inv HDisjRegs; contradiction.
      + repeat intro.
        specialize (HDisjRegs a0); clear - HDisjRegs H4 H5; inv HDisjRegs; contradiction.
    - repeat intro.
      specialize (HDisjRegs a0); clear - HDisjRegs H2 H3; inv HDisjRegs; contradiction.
    - repeat intro.
      specialize (HDisjRegs a0); clear - HDisjRegs H2 H3; inv HDisjRegs; contradiction.
  }
  specialize (PriorityUpds_exist _ P1 ([]::upds0) (ltac:(eapply H4; eauto))
                                 (ltac:(eapply H4; eauto))) as TMP; dest.
  eapply ECompCongruence with (old := o) (o := x); auto.
  - intros; eapply H4; eauto.
  - symmetry; eapply prevPrevRegsTrue; eauto.
  - unfold WfRegMapExpr; split.
    + econstructor.
    + assumption.
  - instantiate (1 := inlineAll_All_mod (mergeSeparatedSingle b lrf)); simpl.
    rewrite <- (prevPrevRegsTrue H3); assumption.
  - unfold WfBaseModule in H2; dest.
    unfold eachRfMethodInliners.
    rewrite <- map_map, <- concat_map.
    apply WfBaseMod_inlineSome_map; auto.
    + specialize (flatten_inline_everything_Wf (Build_ModWf H2)) as P2.
      unfold flatten_inline_everything in P2; rewrite WfMod_createHide in P2; dest; simpl in *; inv H6; assumption.
    +unfold mergeSeparatedSingle in H2; inv H2; inv HWf1.
     unfold WfBaseModule in *; dest.
     specialize (H2 type _ (H1 _ (or_introl eq_refl))); simpl in H2.
     eapply WfExpand; eauto.
     unfold inlineAll_All_mod; simpl; apply SubList_app_r, SubList_refl.
  - apply inlineEeach_Somelist_inlineEach.
  - rewrite (unifyWO retl); simpl.
    assert (forall lrf, length (listRfMethods lrf) = length (EeachRfMethodInliners type Void lrf)).
    { clear.
      unfold listRfMethods, EeachRfMethodInliners.
      repeat rewrite <- flat_map_concat_map.
      induction lrf; auto.
      unfold getRegFileMethods; destruct a; simpl.
      repeat rewrite app_length; rewrite <- IHlrf; clear.
      apply f_equal; apply f_equal2; auto.
      destruct rfRead.
      - unfold readRegFile.
        repeat rewrite map_length; reflexivity.
      - unfold readSyncRegFile; destruct isAddr; repeat rewrite app_length;
          repeat rewrite map_length; reflexivity. }
    setoid_rewrite H5.
    assumption.
Qed.

Lemma EEquivLoop (b : BaseModule) (lrf : list RegFileBase) o :
  let m := inlineAll_All_mod (mergeSeparatedSingle b lrf) in
  forall rules upds calls retl ls
         (HWfMod : WfMod (mergeSeparatedSingle b lrf))
         (HTrace : Trace m o ls)
         (HNoSelfCalls : NoSelfCallBaseModule m)
         (HNoSelfCallsBase : NoSelfCallBaseModule b),
    SubList rules (getRules b) ->
    @SemCompActionT Void (compileRulesRf type (o, nil) rules lrf) (o, upds) calls retl ->
    (forall u, In u upds -> (NoDup (map fst u)) /\ SubList (getKindAttr u) (getKindAttr o)) /\
    exists o' (ls' : list (list FullLabel)),
      PriorityUpds o upds o' /\
      upds = (map getLabelUpds ls') /\
      (map Rle (map fst (rev rules))) = getLabelExecs (concat ls') /\
      calls = concat (map getLabelCalls (rev ls')) /\
      Trace m o' (ls' ++ ls).
Proof.
  intros.
  specialize (mergeFile_noCalls lrf) as P0.
  assert (
      forall (meth : DefMethT) (ty : Kind -> Type),
        In meth (getAllMethods (mergeSeparatedBaseFile lrf)) -> forall arg : ty (fst (projT1 (snd meth))), NeverCallActionT (projT2 (snd meth) ty arg)).
  { revert P0; clear.
    induction lrf; simpl; intros; [contradiction|].
    rewrite in_app_iff in H; inv H.
    - specialize (RegFileBase_noCalls a) as P1.
      inv P1; inv HNCBaseModule; eauto.
    - inv P0.
      eapply IHlrf; eauto. }
  assert ( map fst (rev rules) =
           map fst (rev (map (inline_Rules (getAllMethods (mergeSeparatedBaseFile lrf))
                                           (seq 0 (Datatypes.length (getAllMethods (mergeSeparatedBaseFile lrf))))) rules))) as P2.
  { rewrite <- map_rev.
    rewrite SameKeys_inlineSome_Rules_map; reflexivity. }
  rewrite P2.
  eapply EquivLoop'; eauto; simpl.
  - rewrite map_app, NoDup_app_iff; repeat split; auto; inv HWfMod.
    + inv HWf1; inv HWfBaseModule; dest; assumption.
    + clear - HWf2; induction lrf; simpl; [constructor| inv HWf2].
      rewrite map_app, NoDup_app_iff; repeat split; eauto.
      * inv HWf1; inv HWfBaseModule; dest; assumption.
      * repeat intro; specialize (HDisjRegs a0); clear - HDisjRegs H H0; inv HDisjRegs; contradiction.
      * repeat intro; specialize (HDisjRegs a0); clear - HDisjRegs H H0; inv HDisjRegs; contradiction.
    + repeat intro; specialize (HDisjRegs a); clear - HDisjRegs H2 H3; inv HDisjRegs; contradiction.
    + repeat intro; specialize (HDisjRegs a); clear - HDisjRegs H2 H3; inv HDisjRegs; contradiction.
  - unfold inlineAll_All_mod, inlineAll_All, inlineAll_Meths; simpl.
    rewrite inlineAll_Meths_RegFile_fold_flat, inlineAll_Rules_NoCalls, inlineAll_Rules_in;
      eauto; simpl in *.
    rewrite getAllRules_mergeBaseFile, app_nil_r.
    inv HNoSelfCallsBase; unfold NoSelfCallMethsBaseModule, NoSelfCallRulesBaseModule in *.
    apply SubList_map.
    erewrite inlineSome_Meths_pos_NoCalls_ident'; eauto using SubList_refl.
    unfold inlineAll_Rules.
    erewrite inlineSome_Rules_pos_NoCalls_ident'; eauto.
    rewrite SameKindAttrs_inlineSome_Flat; apply SubList_refl.
  - setoid_rewrite <- (rev_involutive rules).
    eapply CompileRules_Congruence.
    + apply (Trace_sameRegs HTrace).
    + simpl; unfold inlineAll_Meths.
      rewrite inlineAll_Meths_RegFile_fold_flat; simpl.
      * repeat intro; rewrite in_app_iff; right.
        clear - H2.
        unfold listRfMethods in *; simpl in *.
        induction lrf; simpl in *; auto.
        rewrite in_app_iff in *; inv H2; auto.
      * assumption.
    + repeat intro.
      rewrite <-in_rev in H2; apply H; assumption.
    + assumption.
    + rewrite rev_involutive.
      apply H0.
Qed.

Lemma inlineSingle_pos_NoCall_persistent xs:
  forall ty k (a : ActionT ty k) (l l' : list DefMethT),
    (forall f, In f l' -> (forall v, NeverCallActionT (projT2 (snd f) ty v))) ->
    NoCallActionT l a ->
    NoCallActionT l (fold_left (inlineSingle_pos l') xs a).
Proof.
  induction xs; simpl; auto; intros.
  eapply IHxs; eauto; unfold inlineSingle_pos; destruct (nth_error _ _) eqn:G; auto.
  apply NeverCall_inline_persistent; eauto using nth_error_In.
Qed.

Lemma inlineFlat_persistent xs :
  forall (l l' l'': list DefMethT),
    (forall meth ty, In meth l -> (forall v, NeverCallActionT (projT2 (snd meth) ty v))) ->
    (forall meth ty, In meth l' -> (forall v, NoCallActionT l'' (projT2 (snd meth) ty v))) ->
    (forall meth ty, In meth (fold_left (inlineSingle_Flat_pos l) xs l') ->
                     (forall v, NoCallActionT l'' (projT2 (snd meth) ty v))).
Proof.
  induction xs; simpl; auto; intros.
  eapply IHxs with (l := l) (l' := (inlineSingle_Flat_pos l l' a)); auto; intros.
  unfold inlineSingle_Flat_pos in H2; destruct (nth_error _ _) eqn:G; auto.
  rewrite in_map_iff in H2; dest; destruct x, s0, d; subst; simpl in *.
  destruct (String.eqb s0 s); simpl in *.
  - specialize (H0 _ ty0 H3 v0); assumption.
  - apply NeverCall_inline_persistent; eauto using nth_error_In.
    specialize (H0 _ ty0 H3 v0); assumption.
Qed.

Lemma inlineFlat_ident' xs :
  forall (l l' : list DefMethT),
    (forall meth ty, In meth l' -> (forall v, NeverCallActionT (projT2 (snd meth) ty v))) ->
    (forall meth ty,
        In meth (map (inline_Meths l' xs) l) ->
        (forall v, NoCallActionT (subseq_list l' xs) (projT2 (snd meth) ty v))).
Proof.
  intros; rewrite in_map_iff in H0; dest; subst.
  unfold inline_Meths in *; destruct x, s0; simpl in *.
  apply NeverCall_inlineSome_pos_full; eauto.
Qed.

Lemma NoSelfCall_BaseModule_extension (b : BaseModule) (lrf : list RegFileBase) :
  forall (HDisjKeys : DisjKey (getMethods b) (getAllMethods (mergeSeparatedBaseFile lrf))),
    NoSelfCallBaseModule b ->
    (NoSelfCallBaseModule (inlineAll_All_mod (mergeSeparatedSingle b lrf))).
Proof.
  specialize (NeverCallMod_NeverCalls (mergeFile_noCalls lrf)) as TMP; dest.
  unfold inlineAll_All_mod, inlineAll_All, inlineAll_Meths, NoSelfCallBaseModule, NoSelfCallRulesBaseModule, NoSelfCallMethsBaseModule;
    simpl; repeat intro; dest; split; intros; rewrite getAllRules_mergeBaseFile in *.
  - rewrite inlineAll_Meths_RegFile_fold_flat, app_nil_r in *; eauto.
    erewrite inlineSome_Meths_pos_NoCalls_ident' in *; eauto using SubList_refl.
    rewrite inlineAll_Rules_NoCalls in H3.
    unfold inlineAll_Rules at 2 in H3; erewrite inlineSome_Rules_pos_NoCalls_ident' in H3; eauto.
    + unfold inlineAll_Rules in H3; rewrite inline_Rules_eq_inlineSome, in_map_iff in H3; dest; subst; destruct x; simpl.
      apply NoCallActionT_Stitch.
      * eapply SignatureReplace_NoCall with (ls := (getMethods b)); eauto using SameKindAttrs_inlineSome_Flat.
        apply inlineSingle_pos_NoCall_persistent; eauto.
        apply (H1 _ ty H4).
      * eapply SignatureReplace_NoCall;[apply f_equal, (subseq_list_all (getAllMethods (mergeSeparatedBaseFile lrf)))|].
        apply NeverCall_inlineSome_pos_full; auto.
    + rewrite SameKindAttrs_inlineSome_Flat; apply SubList_refl.
  - rewrite inlineAll_Meths_RegFile_fold_flat in *; auto.
    erewrite inlineSome_Meths_pos_NoCalls_ident' in *; eauto using SubList_refl.
    rewrite in_app_iff in H3; inv H3.
    + apply NoCallActionT_Stitch.
      * eapply SignatureReplace_NoCall with (ls := (getMethods b));
          eauto using SameKindAttrs_inlineSome_Flat.
        eapply inlineFlat_persistent; intros; eauto.
      * rewrite inline_Meths_eq_inlineSome in H4; auto.
        rewrite <- (subseq_list_all (getAllMethods (_ _))).
        eapply inlineFlat_ident'; eauto.
    + apply NeverCall_NoCalls; eauto.
Qed.

Lemma EEquivLoop' (b : BaseModule) (lrf : list RegFileBase) o :
  let m := inlineAll_All_mod (mergeSeparatedSingle b lrf) in
  forall rules upds calls retl ls
         (HWfMod : WfMod (mergeSeparatedSingle b lrf))
         (HTrace : Trace m o ls)
         (HNoSelfCallsBase : NoSelfCallBaseModule b),
    SubList rules (getRules b) ->
    @SemCompActionT Void (compileRulesRf type (o, nil) rules lrf) (o, upds) calls retl ->
    (forall u, In u upds -> (NoDup (map fst u)) /\ SubList (getKindAttr u) (getKindAttr o)) /\
    exists o' (ls' : list (list FullLabel)),
      PriorityUpds o upds o' /\
      upds = (map getLabelUpds ls') /\
      (map Rle (map fst (rev rules))) = getLabelExecs (concat ls') /\
      calls = concat (map getLabelCalls (rev ls')) /\
      Trace m o' (ls' ++ ls).
Proof.
  intros; eapply EEquivLoop; eauto.
  inv HWfMod; apply NoSelfCall_BaseModule_extension; auto.
Qed.

Lemma PriorityUpds_Equiv' :
  forall old upds new,
    NoDup (map fst old) ->
    (forall u, In u upds -> NoDup (map fst u)) ->
    PriorityUpds old upds new ->
    (forall new',
        PriorityUpds old upds new' ->
        new = new').
Proof.
  intros.
  specialize (PriorityUpds_Equiv H H0 H1 H2) as P0.
  assert (map fst old = map fst new) as P1.
  { do 2 rewrite <- fst_getKindAttr.
    setoid_rewrite <- (prevPrevRegsTrue H1); reflexivity. }
  assert (map fst old = map fst new') as P2.
  { do 2 rewrite <- fst_getKindAttr.
    setoid_rewrite <- (prevPrevRegsTrue H2); reflexivity. }
  rewrite P1 in H, P2.
  apply KeyPair_Equiv; assumption.
Qed.

Lemma CompTraceEquiv (b : BaseModule) (lrf : list RegFileBase) o :
  let m := inlineAll_All_mod (mergeSeparatedSingle b lrf) in
  let regInits := (getRegisters b) ++ (concat (map getRegFileRegisters lrf)) in
  forall rules lupds lcalls
         (HWfMod : WfMod (mergeSeparatedSingle b lrf))
         (HNoSelfCallsBase : NoSelfCallBaseModule b),
    SubList rules (getRules b) ->
    SemCompTrace regInits (fun s => compileRulesRf type (s, nil) rules lrf) o lupds lcalls ->
    (forall upds u, In upds lupds -> In u upds -> (NoDup (map fst u)) /\ SubList (getKindAttr u) (getKindAttr o)) /\
    exists (lss : list (list (list FullLabel))),
      Forall2 (fun x y => x = (map getLabelUpds y)) lupds lss /\
      (forall x, In x lss -> (map Rle (map fst (rev rules))) = getLabelExecs (concat x)) /\ 
      Forall2 (fun x y => x = concat (map getLabelCalls (rev y))) lcalls lss /\
      Trace m o (concat lss).
Proof.
  induction 4; split; subst; intros; dest; auto.
  - inv H0.
  - exists nil; repeat split; auto.
    + intros; exfalso.
      inv H0.
    + econstructor; eauto.
      unfold regInits in *; simpl in *.
      enough (getAllRegisters (mergeSeparatedBaseFile lrf) = concat (map getRegFileRegisters lrf)).
      { rewrite H0; assumption. }
      clear; induction lrf; simpl; auto.
      rewrite IHlrf; reflexivity.
  - rewrite <-(rev_involutive rules) in HSemAction.
    specialize (ESameOldLoop _ _ _ HSemAction) as TMP; subst.
    rewrite rev_involutive in HSemAction.
    inv H1; rewrite <- (prevPrevRegsTrue HPriorityUpds); eauto.
    eapply EEquivLoop' with (calls := calls) (retl := val); eauto.
  - rewrite <-(rev_involutive rules) in HSemAction.
    specialize (ESameOldLoop _ _ _ HSemAction) as TMP; subst.
    rewrite rev_involutive in HSemAction.
    specialize (EEquivLoop' HWfMod H5 HNoSelfCallsBase H HSemAction) as TMP2; dest.
    unfold m; exists (x1 :: x); repeat split; auto.
    + intros; inv H12; eauto.
    + simpl; enough (o' = x0).
    { subst; assumption. }
    eapply PriorityUpds_Equiv'; eauto.
    * apply Trace_sameRegs in H5.
      apply WfNoDups in HWfMod; dest.
      unfold m in H4; simpl in *.
      rewrite <- fst_getKindAttr; setoid_rewrite H5.
      rewrite <- fst_getKindAttr in H12; assumption.
    * intros; eapply H6; assumption.
Qed.
