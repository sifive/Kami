Require Import Kami.Syntax Lib.Fold.

Import ListNotations.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.PermutEq.
Require Import RelationClasses Setoid Morphisms.
Require Import ZArith.

Definition filterRegs f m (o: RegsT) :=
  filter (fun x => f (getBool (in_dec string_dec (fst x) (map fst (getAllRegisters m))))) o.

Definition filterExecs f m (l: list FullLabel) :=
  filter (fun x => f match fst (snd x) with
                     | Rle y =>
                       getBool (in_dec string_dec y (map fst (getAllRules m)))
                     | Meth (y, _) =>
                       getBool (in_dec string_dec y (map fst (getAllMethods m)))
                     end) l.

Inductive WeakInclusions : list (list FullLabel) -> list (list (FullLabel)) -> Prop :=
| WI_Nil : WeakInclusions nil nil
| WI_Cons : forall (ls ls' : list (list FullLabel)) (l l' : list FullLabel), WeakInclusions ls ls' -> WeakInclusion l l' -> WeakInclusions (l::ls)(l'::ls').


Definition WeakEqualities ls ls' := WeakInclusions ls ls' /\ WeakInclusions ls' ls.

Notation "l '[=]' r" :=
  ((@Permutation _ (l) (r)))
    (at level 70, no associativity).

Section Semantics.
  Variable o: RegsT.

  Inductive PSemAction:
    forall k, ActionT type k -> RegsT -> RegsT -> MethsT -> type k -> Prop :=
  | PSemMCall
      meth s (marg: Expr type (SyntaxKind (fst s)))
      (mret: type (snd s))
      retK (fret: type retK)
      (cont: type (snd s) -> ActionT type retK)
      readRegs newRegs (calls: MethsT) acalls
      (HAcalls: acalls [=] (meth, (existT _ _ (evalExpr marg, mret))) :: calls)
      (HPSemAction: PSemAction (cont mret) readRegs newRegs calls fret):
      PSemAction (MCall meth s marg cont) readRegs newRegs acalls fret
  | PSemLetExpr
      k (e: Expr type k) retK (fret: type retK)
      (cont: fullType type k -> ActionT type retK) readRegs newRegs calls
      (HPSemAction: PSemAction (cont (evalExpr e)) readRegs newRegs calls fret):
      PSemAction (LetExpr e cont) readRegs newRegs calls fret
  | PSemLetAction
      k (a: ActionT type k) (v: type k) retK (fret: type retK)
      (cont: type k -> ActionT type retK)
      readRegs newRegs readRegsCont newRegsCont calls callsCont
      (HDisjRegs: DisjKey newRegs newRegsCont)
      (HPSemAction: PSemAction a readRegs newRegs calls v)
      ureadRegs unewRegs ucalls
      (HUReadRegs: ureadRegs [=] readRegs ++ readRegsCont)
      (HUNewRegs: unewRegs [=] newRegs ++ newRegsCont)
      (HUCalls: ucalls [=] calls ++ callsCont)
      (HPSemActionCont: PSemAction (cont v) readRegsCont newRegsCont callsCont fret):
      PSemAction (LetAction a cont) (ureadRegs) (unewRegs)
                (ucalls) fret
  | PSemReadNondet
      valueT (valueV: fullType type valueT)
      retK (fret: type retK) (cont: fullType type valueT -> ActionT type retK)
      readRegs newRegs calls
      (HPSemAction: PSemAction (cont valueV) readRegs newRegs calls fret):
      PSemAction (ReadNondet _ cont) readRegs newRegs calls fret
  | PSemReadReg
      (r: string) regT (regV: fullType type regT)
      retK (fret: type retK) (cont: fullType type regT -> ActionT type retK)
      readRegs newRegs calls areadRegs
      (HRegVal: In (r, existT _ regT regV) o)
      (HPSemAction: PSemAction (cont regV) readRegs newRegs calls fret)
      (HNewReads: areadRegs [=] (r, existT _ regT regV) :: readRegs):
      PSemAction (ReadReg r _ cont) areadRegs newRegs calls fret
  | PSemWriteReg
      (r: string) k
      (e: Expr type k)
      retK (fret: type retK)
      (cont: ActionT type retK) readRegs newRegs calls anewRegs
      (HRegVal: In (r, k) (getKindAttr o))
      (HDisjRegs: key_not_In r newRegs)
      (HANewRegs: anewRegs [=] (r, (existT _ _ (evalExpr e))) :: newRegs)
      (HPSemAction: PSemAction cont readRegs newRegs calls fret):
      PSemAction (WriteReg r e cont) readRegs anewRegs calls fret
  | PSemIfElseTrue
      (p: Expr type (SyntaxKind Bool)) k1
      (a: ActionT type k1)
      (a': ActionT type k1)
      (r1: type k1)
      k2 (cont: type k1 -> ActionT type k2)
      readRegs1 readRegs2  newRegs1 newRegs2 calls1 calls2 (r2: type k2)
      (HDisjRegs: DisjKey newRegs1 newRegs2)
      (HTrue: evalExpr p = true)
      (HAction: PSemAction a readRegs1 newRegs1 calls1 r1)
      (HPSemAction: PSemAction (cont r1) readRegs2 newRegs2 calls2 r2)
      ureadRegs unewRegs ucalls
      (HUReadRegs: ureadRegs [=] readRegs1 ++ readRegs2)
      (HUNewRegs: unewRegs [=] newRegs1 ++ newRegs2)
      (HUCalls: ucalls [=] calls1 ++ calls2) :
      PSemAction (IfElse p a a' cont) ureadRegs unewRegs ucalls r2
  | PSemIfElseFalse
      (p: Expr type (SyntaxKind Bool)) k1
      (a: ActionT type k1)
      (a': ActionT type k1)
      (r1: type k1)
      k2 (cont: type k1 -> ActionT type k2)
      readRegs1 readRegs2 newRegs1 newRegs2 calls1 calls2 (r2: type k2)
      (HDisjRegs: DisjKey newRegs1 newRegs2)
      (HFalse: evalExpr p = false)
      (HAction: PSemAction a' readRegs1 newRegs1 calls1 r1)
      (HPSemAction: PSemAction (cont r1) readRegs2 newRegs2 calls2 r2)
      ureadRegs unewRegs ucalls
      (HUReadRegs: ureadRegs [=] readRegs1 ++ readRegs2)
      (HUNewRegs: unewRegs [=] newRegs1 ++ newRegs2)
      (HUCalls: ucalls [=] calls1 ++ calls2):
      PSemAction (IfElse p a a' cont) ureadRegs unewRegs ucalls r2
  | PSemDisplay
      (ls: list (SysT type)) k (cont: ActionT type k)
      r readRegs newRegs calls
      (HPSemAction: PSemAction cont readRegs newRegs calls r):
      PSemAction (Sys ls cont) readRegs newRegs calls r
  | PSemReturn
      k (e: Expr type (SyntaxKind k)) evale
      (HEvalE: evale = evalExpr e)
      readRegs newRegs calls
      (HReadRegs: readRegs = nil)
      (HNewRegs: newRegs = nil)
      (HCalls: calls = nil) :
      PSemAction (Return e) readRegs newRegs calls evale.  
End Semantics.


Section BaseModule.
  Variable m: BaseModule.
  Variable o: RegsT.
  Inductive PSubsteps: list FullLabel -> Prop :=
  | NilPSubstep (HRegs: getKindAttr o [=] getKindAttr (getRegisters m)) : PSubsteps nil
  | PAddRule (HRegs: getKindAttr o [=] getKindAttr (getRegisters m))
             rn rb
             (HInRules: In (rn, rb) (getRules m))
             reads u cs
             (HPAction: PSemAction o (rb type) reads u cs WO)
             (HReadsGood: SubList (getKindAttr reads)
                                  (getKindAttr (getRegisters m)))
             (HUpdGood: SubList (getKindAttr u)
                                (getKindAttr (getRegisters m)))
             l ls (HLabel: l [=] (u, (Rle rn, cs)) :: ls)
             (HDisjRegs: forall x, In x ls -> DisjKey (fst x) u)
             (HNoRle: forall x, In x ls -> match fst (snd x) with
                                           | Rle _ => False
                                           | _ => True
                                           end)
             (HPSubstep: PSubsteps ls):
      PSubsteps l
  | PAddMeth (HRegs: getKindAttr o [=] getKindAttr (getRegisters m))
             fn fb
             (HInMeths: In (fn, fb) (getMethods m))
             reads u cs argV retV
             (HPAction: PSemAction o ((projT2 fb) type argV) reads u cs retV)
             (HReadsGood: SubList (getKindAttr reads)
                                  (getKindAttr (getRegisters m)))
             (HUpdGood: SubList (getKindAttr u)
                                (getKindAttr (getRegisters m)))
             l ls (HLabel: l [=] (u, (Meth (fn, existT _ _ (argV, retV)), cs)) :: ls )
             (HDisjRegs: forall x, In x ls -> DisjKey (fst x) u)
             (HPSubsteps: PSubsteps ls):
      PSubsteps l.

  Inductive PPlusSubsteps: RegsT -> list RuleOrMeth -> MethsT -> Prop :=
  | NilPPlusSubstep (HRegs: getKindAttr o [=] getKindAttr (getRegisters m)) : PPlusSubsteps nil nil nil
  | PPlusAddRule (HRegs: getKindAttr o [=] getKindAttr (getRegisters m))
            rn rb
            (HInRules: In (rn, rb) (getRules m))
            reads u cs
            (HPAction: PSemAction o (rb type) reads u cs WO)
            (HReadsGood: SubList (getKindAttr reads)
                                 (getKindAttr (getRegisters m)))
            (HUpdGood: SubList (getKindAttr u)
                               (getKindAttr (getRegisters m)))
            upds execs calls oldUpds oldExecs oldCalls
            (HUpds: upds [=] u ++ oldUpds)
            (HExecs: execs [=] Rle rn :: oldExecs)
            (HCalls: calls [=] cs ++ oldCalls)
            (HDisjRegs: DisjKey oldUpds u)
            (HNoRle: forall x, In x oldExecs -> match x with
                                                | Rle _ => False
                                                | _ => True
                                                end)
            (HPSubstep: PPlusSubsteps oldUpds oldExecs oldCalls):
      PPlusSubsteps upds execs calls
  | PPlusAddMeth (HRegs: getKindAttr o [=] getKindAttr (getRegisters m))
            fn fb
            (HInMeths: In (fn, fb) (getMethods m))
            reads u cs argV retV
            (HPAction: PSemAction o ((projT2 fb) type argV) reads u cs retV)
            (HReadsGood: SubList (getKindAttr reads)
                                 (getKindAttr (getRegisters m)))
            (HUpdGood: SubList (getKindAttr u)
                               (getKindAttr (getRegisters m)))
            upds execs calls oldUpds oldExecs oldCalls
            (HUpds: upds [=] u ++ oldUpds)
            (HExecs: execs [=] Meth (fn, existT _ _ (argV, retV)) :: oldExecs)
            (HCalls: calls [=] cs ++ oldCalls)
            (HDisjRegs: DisjKey oldUpds u)
            (HPSubstep: PPlusSubsteps oldUpds oldExecs oldCalls):
      PPlusSubsteps upds execs calls.
End BaseModule.

Inductive PStep: Mod -> RegsT -> list FullLabel -> Prop :=
| PBaseStep m o l (HPSubsteps: PSubsteps m o l) (HMatching: MatchingExecCalls_Base l m):
    PStep (Base m) o l
| PHideMethStep m s o l (HPStep: PStep m o l)
               (HHidden : In s (map fst (getAllMethods m)) -> (forall v, (getListFullLabel_diff (s, v) l = 0%Z))):
    PStep (HideMeth m s) o l
| PConcatModStep m1 m2 o1 o2 l1 l2
                 (HPStep1: PStep m1 o1 l1)
                 (HPStep2: PStep m2 o2 l2)
                 (HMatching1: MatchingExecCalls_Concat l1 l2 m2)
                 (HMatching2: MatchingExecCalls_Concat l2 l1 m1)
                 (HNoRle: forall x y, In x l1 -> In y l2 -> match fst (snd x), fst (snd y) with
                                                            | Rle _, Rle _ => False
                                                            | _, _ => True
                                                            end)
                 o l
                 (HRegs: o [=] o1 ++ o2)
                 (HLabels: l [=] l1 ++ l2):
    PStep (ConcatMod m1 m2) o l.

Section PPlusStep.
  Variable m: BaseModule.
  Variable o: RegsT.
  
  Definition MatchingExecCalls_flat (calls : MethsT) (execs : list RuleOrMeth) (m : BaseModule) :=
    forall (f : MethT),
      In (fst f) (map fst (getMethods m)) ->
      (getNumFromCalls f calls <= getNumFromExecs f execs)%Z.
  
  Inductive PPlusStep :  RegsT -> list RuleOrMeth -> MethsT -> Prop :=
  | BasePPlusStep upds execs calls:
      PPlusSubsteps m o upds execs calls ->
      MatchingExecCalls_flat calls execs m -> PPlusStep upds execs calls.
End PPlusStep.


Section Trace.
  Variable m: Mod.
  Definition PUpdRegs (u: list RegsT) (o o': RegsT)
    := getKindAttr o [=] getKindAttr o' /\
       (forall s v, In (s, v) o' -> ((exists x, In x u /\ In (s, v) x) \/
                                     ((~ exists x, In x u /\ In s (map fst x)) /\ In (s, v) o))).

  Inductive PTrace: RegsT -> list (list FullLabel) -> Prop :=
  | PInitTrace (o' o'' : RegsT) ls'
               (HPerm : o' [=] o'')
               (HUpdRegs : Forall2 regInit o'' (getAllRegisters m))
               (HTrace: ls' = nil):
      PTrace o' ls'
  | PContinueTrace o ls l o' ls'
                   (PHOldTrace: PTrace o ls)
                   (HPStep: PStep m o l)
                   (HPUpdRegs: PUpdRegs (map fst l) o o')
                   (HTrace: ls' = l :: ls):
      PTrace o' ls'.
End Trace.



Definition PPlusUpdRegs (u o o' : RegsT) :=
  getKindAttr o [=] getKindAttr o' /\
  (forall s v, In (s, v) o' -> In (s, v) u \/ (~ In s (map fst u) /\ In (s, v) o)).
  
Section PPlusTrace.
  Variable m: BaseModule.
  Inductive PPlusTrace : RegsT -> list (RegsT * ((list RuleOrMeth) * MethsT)) -> Prop :=
  | PPlusInitTrace (o' o'' : RegsT) ls'
                   (HPerm : o' [=] o'')
                   (HUpdRegs : Forall2 regInit o'' (getRegisters m))
                   (HTrace : ls' = nil):
      PPlusTrace o' ls'
  | PPlusContinueTrace (o o' : RegsT)
                       (upds : RegsT)
                       (execs : list RuleOrMeth)
                       (calls : MethsT)
                       (ls ls' : list (RegsT * ((list RuleOrMeth) * MethsT)))
                       (PPlusOldTrace : PPlusTrace o ls)
                       (HPPlusStep : PPlusStep m o upds execs calls)
                       (HUpdRegs : PPlusUpdRegs upds o o')
                       (HPPlusTrace : ls' = ((upds, (execs, calls))::ls)):
      PPlusTrace o' ls'.
End PPlusTrace.

Definition PTraceList (m : Mod) (ls : list (list FullLabel)) :=
  (exists (o : RegsT), PTrace m o ls).

Definition PTraceInclusion (m m' : Mod) :=
  forall (o : RegsT) (ls : list (list FullLabel)),
    PTrace m o ls -> exists (ls' : list (list FullLabel)), PTraceList m' ls' /\ WeakInclusions ls ls'.

Definition PStepSubstitute m o l :=
  PSubsteps (BaseMod (getAllRegisters m) (getAllRules m) (getAllMethods m)) o l /\
  MatchingExecCalls_Base l (getFlat m) /\
  (forall s v, In s (map fst (getAllMethods m)) ->
               In s (getHidden m) ->
               (getListFullLabel_diff (s, v) l = 0%Z)).

Definition StepSubstitute m o l :=
  Substeps (BaseMod (getAllRegisters m) (getAllRules m) (getAllMethods m)) o l /\
  MatchingExecCalls_Base l (getFlat m) /\
  (forall s v, In s (map fst (getAllMethods m)) ->
               In s (getHidden m) ->
               (getListFullLabel_diff (s, v) l = 0%Z)).

Definition InExec f (l: list (RegsT * (RuleOrMeth * MethsT))) :=
  In (Meth f) (map getRleOrMeth l).

Definition InCall f (l: list (RegsT * (RuleOrMeth * MethsT))) :=
  exists x, In x l /\ In f (snd (snd x)).

Lemma Kind_eq: forall k, Kind_dec k k = left eq_refl.
Proof.
  intros; destruct (Kind_dec k k).
  - f_equal.
    apply Eqdep_dec.UIP_dec.
    apply Kind_dec.
  - apply (match n eq_refl with end).
Qed.

Lemma Signature_eq: forall sig, Signature_dec sig sig = left eq_refl.
Proof.
  intros; destruct (Signature_dec sig sig).
  - f_equal.
    apply Eqdep_dec.UIP_dec.
    apply Signature_dec.
  - apply (match n eq_refl with end).
Qed.

Section InverseSemAction.
  Variable o: RegsT.

  Lemma inversionSemAction
          k a reads news calls retC
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
      exists reads1 news1 calls1 reads2 news2 calls2 r1,
      DisjKey news1 news2 /\
      match evalExpr p with
      | true =>
        SemAction o aT reads1  news1 calls1 r1 /\
        SemAction o (c r1) reads2 news2 calls2 retC /\
        reads = reads1 ++ reads2 /\
        news = news1 ++ news2 /\
        calls = calls1 ++ calls2
      | false =>
        SemAction o aF reads1 news1 calls1 r1 /\
        SemAction o (c r1) reads2 news2 calls2 retC /\
        reads = reads1 ++ reads2 /\
        news = news1 ++ news2 /\
        calls = calls1 ++ calls2
      end
    | Sys _ c =>
      SemAction o c reads news calls retC
    | Return e =>
      retC = evalExpr e /\
      news = nil /\
      calls = nil
    end.
  Proof.
    destruct evalA; eauto; repeat eexists; try destruct (evalExpr p); eauto; try discriminate.
  Qed.

  Lemma SemActionReadsSub k a reads upds calls ret:
    @SemAction o k a reads upds calls ret ->
    SubList reads o.
  Proof.
    induction 1; auto; subst;
      unfold SubList in *; intros;
        rewrite ?in_app_iff in *.
    - subst; firstorder.
    - repeat (subst; firstorder).
    - subst.
      rewrite ?in_app_iff in H1.
      destruct H1; intuition.
    - subst.
      rewrite ?in_app_iff in H1.
      destruct H1; intuition.
    - subst; simpl in *; intuition.
  Qed.
End InverseSemAction.

Section evalExpr.

  Lemma castBits_same ty ni no (pf: ni = no) (e: Expr ty (SyntaxKind (Bit ni))): castBits pf e = match pf in _ = Y return Expr ty (SyntaxKind (Bit Y)) with
                                                                                                 | eq_refl => e
                                                                                                 end.
  Proof.
    unfold castBits.
    destruct pf.
    rewrite nat_cast_same.
    auto.
  Qed.

  Lemma evalExpr_castBits: forall ni no (pf: ni = no) (e: Bit ni @# type), evalExpr (castBits pf e) =
                                                                           nat_cast (fun n => word n) pf (evalExpr e).
  Proof.
    intros.
    unfold castBits.
    destruct pf.
    rewrite ?nat_cast_same.
    auto.
  Qed.

  Lemma evalExpr_BinBit: forall kl kr k (op: BinBitOp kl kr k)
                                (l1 l2: Bit kl @# type)
                                (r1 r2: Bit kr @# type),
    evalExpr l1 = evalExpr l2 ->
    evalExpr r1 = evalExpr r2 ->
    evalExpr (BinBit op l1 r1) = evalExpr (BinBit op l2 r2).
  Proof.
    intros.
    induction op; simpl; try congruence.
  Qed.

  Lemma evalExpr_ZeroExtend: forall lsb msb (e1 e2: Bit lsb @# type), evalExpr e1 = evalExpr e2 ->
                                                                      evalExpr (ZeroExtend msb e1) = evalExpr (ZeroExtend msb e2).
  Proof.
    intros.
    unfold ZeroExtend.
    erewrite evalExpr_BinBit; eauto.
  Qed.

  Lemma evalExpr_pack_Bool: forall (e1 e2: Bool @# type),
      evalExpr e1 = evalExpr e2 ->
      evalExpr (pack e1) = evalExpr (pack e2).
  Proof.
    intros.
    simpl.
    rewrite H.
    reflexivity.
  Qed.

  Lemma evalExpr_Void (e: Expr type (SyntaxKind (Bit 0))):
    evalExpr e = WO.
  Proof.
    inversion e; auto.
  Qed.

  Lemma evalExpr_countLeadingZeros ni: forall no (e: Expr type (SyntaxKind (Bit ni))),
      evalExpr (countLeadingZeros no e) = countLeadingZerosWord no (evalExpr e).
  Proof.
    induction ni; simpl; intros; auto.
    rewrite evalExpr_castBits.
    simpl.
    unfold wzero at 2.
    rewrite wzero_wplus.
    match goal with
    | |- (if getBool ?P then _ else _) = (if ?P then _ else _) => destruct P; auto
    end.
    repeat f_equal.
    rewrite IHni.
    simpl.
    rewrite evalExpr_castBits.
    repeat f_equal.
  Qed.
End evalExpr.


Lemma getNumCalls_nil f :
  getNumCalls f nil = 0%Z.
Proof.
  reflexivity.
Qed.

Lemma getNumExecs_nil f :
  getNumExecs f nil = 0%Z.
Proof.
  reflexivity.
Qed.

Lemma getNumFromCalls_eq_cons f g l :
  f = g ->
  getNumFromCalls f (g::l) = (1 + (getNumFromCalls f l))%Z.
Proof.
  intro;unfold getNumFromCalls; destruct MethT_dec; auto; contradiction.
Qed.

Lemma getNumFromCalls_neq_cons f g l :
  f <> g ->
  getNumFromCalls f (g::l) = getNumFromCalls f l.
Proof.
  intro; unfold getNumFromCalls; destruct MethT_dec; auto; contradiction.
Qed.

Opaque getNumFromCalls.
Lemma getNumFromCalls_app f l1:
  forall l2,
  getNumFromCalls f (l1++l2) = (getNumFromCalls f l1 + getNumFromCalls f l2)%Z.
Proof.
  induction l1.
  - simpl; reflexivity.
  - intros.
    destruct (MethT_dec f a).
    + simpl; repeat rewrite getNumFromCalls_eq_cons; auto.
      rewrite IHl1; ring.
    + simpl; repeat rewrite getNumFromCalls_neq_cons; auto.
Qed.
Transparent getNumFromCalls.

Corollary getNumCalls_app f l1 :
  forall l2,
    getNumCalls f (l1 ++ l2) = (getNumCalls f l1 + getNumCalls f l2)%Z.
Proof.
  unfold getNumCalls.
  intro.
  rewrite map_app, concat_app, getNumFromCalls_app.
  reflexivity.
Qed.

Lemma getNumCalls_cons f a l :
  getNumCalls f (a::l) = ((getNumFromCalls f (snd (snd a))) + getNumCalls f l)%Z.
Proof.
  unfold getNumCalls.
  simpl; rewrite getNumFromCalls_app; reflexivity.
Qed.
Transparent getNumFromCalls.

Lemma getNumFromCalls_nonneg f l :
  (0 <= getNumFromCalls f l)%Z.
Proof.
  induction l.
  - unfold getNumFromCalls; reflexivity.
  - destruct (MethT_dec f a);[rewrite getNumFromCalls_eq_cons; auto| rewrite getNumFromCalls_neq_cons; auto].
    Omega.omega.
Qed.

Lemma getNumCalls_nonneg f l:
  (0 <= (getNumCalls f l))%Z.
Proof.
  induction l.
  - rewrite getNumCalls_nil;reflexivity.
  - rewrite getNumCalls_cons.
    specialize (getNumFromCalls_nonneg f (snd (snd a))) as B1.
    Omega.omega.
Qed.
    
Lemma getNumFromExecs_eq_cons f g l :
  f = g ->
  getNumFromExecs f ((Meth g)::l) = (1 + (getNumFromExecs f l))%Z.
Proof.
  intros; simpl; destruct (MethT_dec f g); auto; contradiction.
Qed.

Lemma getNumFromExecs_neq_cons f g l :
  f <> g ->
  getNumFromExecs f ((Meth g)::l) = (getNumFromExecs f l).
Proof.
  intros; simpl; destruct (MethT_dec f g); auto; contradiction.
Qed.

Lemma getNumFromExecs_Rle_cons f rn l:
  getNumFromExecs f ((Rle rn)::l) = (getNumFromExecs f l).
Proof.
  intros; simpl; reflexivity.
Qed.

Opaque getNumFromExecs.
Lemma getNumFromExecs_app f l1:
  forall l2,
    getNumFromExecs f (l1++l2) = (getNumFromExecs f l1 + getNumFromExecs f l2)%Z.
Proof.
  induction l1.
  - simpl; reflexivity.
  - intros; destruct a;[|destruct (MethT_dec f f0)];simpl.
    + repeat rewrite getNumFromExecs_Rle_cons; apply IHl1.
    + repeat rewrite getNumFromExecs_eq_cons; auto.
      rewrite IHl1; ring.
    + repeat rewrite getNumFromExecs_neq_cons; auto.
Qed.
Transparent getNumFromExecs.

Corollary getNumExecs_app f l1 :
  forall l2,
    getNumExecs f (l1++l2) = (getNumExecs f l1 + getNumExecs f l2)%Z.
Proof.
  unfold getNumExecs.
  intros;rewrite map_app, getNumFromExecs_app; reflexivity.
Qed.

Lemma getNumFromExecs_nonneg f l:
  (0 <= (getNumFromExecs f l))%Z.
Proof.
  induction l.
  - simpl; reflexivity.
  - destruct a;[rewrite getNumFromExecs_Rle_cons
               |destruct (MethT_dec f f0);[rewrite getNumFromExecs_eq_cons
                                          |rewrite getNumFromExecs_neq_cons]]; auto; Omega.omega.
Qed.

Corollary getNumExecs_nonneg f l :
  (0 <= (getNumExecs f l))%Z.
Proof.
  unfold getNumExecs;apply getNumFromExecs_nonneg.
Qed.

Lemma getNumFromCalls_perm f l l':
  l [=] l' ->
  getNumFromCalls f l = getNumFromCalls f l'.
Proof.
  induction 1; auto.
  - destruct (MethT_dec f x);[repeat rewrite getNumFromCalls_eq_cons| repeat rewrite getNumFromCalls_neq_cons];auto.
    rewrite IHPermutation; reflexivity.
  - destruct (MethT_dec f x), (MethT_dec f y).
    + repeat rewrite getNumFromCalls_eq_cons; auto.
    + rewrite getNumFromCalls_neq_cons, getNumFromCalls_eq_cons, getNumFromCalls_eq_cons, getNumFromCalls_neq_cons ; auto.
    + rewrite getNumFromCalls_eq_cons, getNumFromCalls_neq_cons, getNumFromCalls_neq_cons, getNumFromCalls_eq_cons ; auto.
    + repeat rewrite getNumFromCalls_neq_cons; auto.
  - rewrite IHPermutation1, IHPermutation2; reflexivity.
Qed.

Global Instance getNumFromCalls_perm_rewrite' :
  Proper (eq ==> @Permutation (MethT) ==> eq) (@getNumFromCalls) | 10.
Proof.
  repeat red; intros; subst; eauto using getNumFromCalls_perm.
Qed.

Lemma concat_perm_rewrite (A : Type) (l l' : list (list A)):
  l [=] l' ->
  concat l [=] concat l'.
Proof.
  induction 1.
  - reflexivity.
  - simpl; rewrite IHPermutation; reflexivity.
  - simpl; repeat rewrite app_assoc.
    apply Permutation_app_tail, Permutation_app_comm.
  - eauto using Permutation_trans.
Qed.

Global Instance concat_perm_rewrite' {A : Type}:
  Proper (@Permutation (list A) ==> @Permutation A) (@concat A) | 10.
Proof.
  repeat red; eauto using concat_perm_rewrite.
Qed.

Corollary getNumCalls_perm_rewrite f l l':
  l [=] l' ->
  getNumCalls f l = getNumCalls f l'.
Proof.
  unfold getNumCalls.
  intros; rewrite H; reflexivity.
Qed.

Global Instance getNumCalls_perm_rewrite' :
  Proper (eq ==> @Permutation FullLabel ==> eq) (@getNumCalls) | 10.
Proof.
  repeat red; intros; subst; eauto using getNumCalls_perm_rewrite.
Qed.

Lemma getNumFromExecs_perm f l l':
  l [=] l' ->
  getNumFromExecs f l = getNumFromExecs f l'.
Proof.
  induction 1; auto.
  - destruct x;[repeat rewrite getNumFromExecs_Rle_cons;rewrite IHPermutation; reflexivity|].
    destruct (MethT_dec f f0);[repeat rewrite getNumFromExecs_eq_cons| repeat rewrite getNumFromExecs_neq_cons];auto.
    rewrite IHPermutation; reflexivity.
  - destruct x, y.
    + repeat rewrite getNumFromExecs_Rle_cons; reflexivity.
    + destruct (MethT_dec f f0).
      * rewrite getNumFromExecs_eq_cons, getNumFromExecs_Rle_cons, getNumFromExecs_Rle_cons, getNumFromExecs_eq_cons; auto.
      * rewrite getNumFromExecs_neq_cons, getNumFromExecs_Rle_cons, getNumFromExecs_Rle_cons, getNumFromExecs_neq_cons; auto.
    + destruct (MethT_dec f f0).
      * rewrite getNumFromExecs_eq_cons, getNumFromExecs_Rle_cons, getNumFromExecs_Rle_cons, getNumFromExecs_eq_cons; auto.
      * rewrite getNumFromExecs_neq_cons, getNumFromExecs_Rle_cons, getNumFromExecs_Rle_cons, getNumFromExecs_neq_cons; auto.
    + destruct (MethT_dec f f0), (MethT_dec f f1).
      * repeat rewrite getNumFromExecs_eq_cons; auto.
      * rewrite getNumFromExecs_neq_cons, getNumFromExecs_eq_cons, getNumFromExecs_eq_cons, getNumFromExecs_neq_cons; auto.
      * rewrite getNumFromExecs_eq_cons, getNumFromExecs_neq_cons, getNumFromExecs_neq_cons, getNumFromExecs_eq_cons; auto.
      * repeat rewrite getNumFromExecs_neq_cons; auto.
  - eauto using eq_trans.
Qed.

Global Instance getNumFromExecs_perm_rewrite' :
  Proper (eq ==> @Permutation RuleOrMeth ==> eq) (@getNumFromExecs) | 10.
Proof.
  repeat red; intros; subst; eauto using getNumFromExecs_perm.
Qed.

Corollary getNumExecs_perm_rewrite f l l':
  l [=] l' ->
  getNumExecs f l = getNumExecs f l'.
Proof.
  intros; unfold getNumExecs; rewrite H; reflexivity.
Qed.

Global Instance getNumExecs_perm_rewrite' :
  Proper (eq ==> @Permutation FullLabel ==> eq) (@getNumExecs) | 10.
Proof.
  repeat red; intros; subst; eauto using getNumExecs_perm_rewrite.
Qed.

Definition UpdRegs' (u: list RegsT) (o o': RegsT)
  := map fst o = map fst o' /\
     (forall s v, In (s, v) o' -> ((exists x, In x u /\ In (s, v) x) \/
                                   ((~ exists x, In x u /\ In s (map fst x)) /\ In (s, v) o))).


Lemma UpdRegs_same: forall u o o', UpdRegs u o o' -> UpdRegs' u o o'.
Proof.
  unfold UpdRegs, UpdRegs'.
  intros; dest.
  apply (f_equal (map fst)) in H.
  rewrite ?map_map in H; simpl in *.
  setoid_rewrite (functional_extensionality (fun x => fst x) fst) in H; tauto.
Qed.


Lemma getKindAttr_map_fst A (P Q: A -> Type)
  : forall (l2: list (Attribute (sigT P))) (l1: list (Attribute (sigT Q))),
    getKindAttr l1 = getKindAttr l2 ->
    map fst l1 = map fst l2.
Proof.
  induction l2; simpl; auto; intros.
  - apply map_eq_nil in H; subst; auto.
  - destruct l1; simpl in *.
    + discriminate.
    + inv H; f_equal.
      apply IHl2; auto.
Qed.

Lemma Step_getAllRegisters m o l:
  Step m o l ->
  getKindAttr o = getKindAttr (getAllRegisters m).
Proof.
  induction 1; auto; simpl.
  - inv HSubsteps; auto.
  - rewrite map_app.
    rewrite <- IHStep1, <- IHStep2, HRegs.
    rewrite map_app.
    auto.
Qed.

Lemma Step_getAllRegisters_fst m o l:
  Step m o l ->
  map fst o = map fst (getAllRegisters m).
Proof.
  intros.
  apply Step_getAllRegisters in H.
  eapply getKindAttr_map_fst; eauto.
Qed.

Lemma DisjRegs_1_id (l1: list RegInitT):
  forall l2 (o1 o2: RegsT),
    DisjKey l1 l2 ->
    map fst o1 = map fst l1 ->
    map fst o2 = map fst l2 ->
    filter (fun x => id (getBool (in_dec string_dec (fst x) (map fst l1)))) (o1 ++ o2) = o1.
Proof.
  intros.
  rewrite filter_app.
  rewrite <- H0.
  erewrite filter_in_dec_map.
  erewrite filter_not_in_dec_map.
  - rewrite app_nil_r; auto.
  - unfold DisjKey in *; intros.
    specialize (H k).
    firstorder congruence.
Qed.
  
Lemma DisjRegs_1_negb (l1: list RegInitT):
  forall l2 (o1 o2: RegsT),
    DisjKey l1 l2 ->
    map fst o1 = map fst l1 ->
    map fst o2 = map fst l2 ->
    filter (fun x => negb (getBool (in_dec string_dec (fst x) (map fst l1)))) (o1 ++ o2) = o2.
Proof.
  intros.
  rewrite filter_app.
  rewrite <- H0.
  erewrite filter_negb_in_dec_map.
  erewrite filter_negb_not_in_dec_map.
  - auto.
  - unfold DisjKey in *; intros.
    specialize (H k).
    firstorder congruence.
Qed.
  
Lemma DisjRegs_2_id (l1: list RegInitT):
  forall l2 (o1 o2: RegsT),
    DisjKey l1 l2 ->
    map fst o1 = map fst l1 ->
    map fst o2 = map fst l2 ->
    filter (fun x => id (getBool (in_dec string_dec (fst x) (map fst l2)))) (o1 ++ o2) = o2.
Proof.
  intros.
  rewrite filter_app.
  rewrite <- H1.
  erewrite filter_in_dec_map.
  erewrite filter_not_in_dec_map.
  - rewrite ?app_nil_r; auto.
  - unfold DisjKey in *; intros.
    specialize (H k).
    firstorder congruence.
Qed.
  
Lemma DisjRegs_2_negb (l1: list RegInitT):
  forall l2 (o1 o2: RegsT),
    DisjKey l1 l2 ->
    map fst o1 = map fst l1 ->
    map fst o2 = map fst l2 ->
    filter (fun x => negb (getBool (in_dec string_dec (fst x) (map fst l2)))) (o1 ++ o2) = o1.
Proof.
  intros.
  rewrite filter_app.
  rewrite <- H1.
  erewrite filter_negb_in_dec_map.
  erewrite filter_negb_not_in_dec_map.
  - rewrite ?app_nil_r; auto.
  - unfold DisjKey in *; intros.
    specialize (H k).
    firstorder congruence.
Qed.

Lemma Substeps_rm_In m o l:
  Substeps m o l ->
  forall fv, In fv l ->
             match fst (snd fv) with
             | Rle r => getBool (in_dec string_dec r (map fst (getRules m)))
             | Meth (f, v) => getBool (in_dec string_dec f (map fst (getMethods m)))
             end = true.
Proof.
  induction 1; simpl; intros; subst; try tauto.
  - simpl in *.
    destruct H0.
    + inv H0.
      simpl.
      destruct (in_dec string_dec rn (map fst (getRules m))); simpl; auto.
      exfalso; apply (n (in_map fst _ _ HInRules)).
    + eapply IHSubsteps; eauto.
  - simpl in *.
    destruct H0.
    + inv H0.
      simpl.
      destruct (in_dec string_dec fn (map fst (getMethods m))); simpl; auto.
      exfalso; apply (n (in_map fst _ _ HInMeths)).
    + eapply IHSubsteps; eauto.
Qed.

Lemma Step_rm_In m o l:
  Step m o l ->
  forall fv, In fv l ->
             match fst (snd fv) with
             | Rle r => getBool (in_dec string_dec r (map fst (getAllRules m)))
             | Meth (f, v) => getBool (in_dec string_dec f (map fst (getAllMethods m)))
             end = true.
Proof.
  induction 1; simpl; auto; intros.
  - eapply Substeps_rm_In; eauto.
  - subst.
    specialize (IHStep1 fv).
    specialize (IHStep2 fv).
    rewrite ?map_app, in_app_iff in *.
    destruct fv as [? [b ?]]; simpl; auto.
    destruct b as [b | b]; auto; simpl in *; [| destruct b];
      match goal with
      | |- getBool ?P = _ => destruct P
      end; simpl; auto;
        rewrite in_app_iff in *.
    + destruct (in_dec string_dec b (map fst (getAllRules m1))),
      (in_dec string_dec b (map fst (getAllRules m2))); simpl in *; tauto.
    + destruct (in_dec string_dec s (map fst (getAllMethods m1))),
      (in_dec string_dec s (map fst (getAllMethods m2))); simpl in *; tauto.
Qed.

Lemma Substeps_rm_not_In m1 m2 o l:
  DisjKey (getAllRules m1) (getRules m2) ->
  DisjKey (getAllMethods m1) (getMethods m2) ->
  Substeps m2 o l ->
  forall fv, In fv l ->
             match fst (snd fv) with
             | Rle r => getBool (in_dec string_dec r (map fst (getAllRules m1)))
             | Meth (f, v) => getBool (in_dec string_dec f (map fst (getAllMethods m1)))
             end = false.
Proof.
  intros DisjRules DisjMeths.
  induction 1; simpl; auto; intros; subst; try tauto.
  - destruct H0.
    + inv H0.
      simpl.
      destruct (in_dec string_dec rn (map fst (getAllRules m1))); simpl; auto.
      apply (in_map fst) in HInRules.
      clear - DisjRules DisjMeths HInRules i; firstorder.
    + eapply IHSubsteps; eauto.
  - simpl in *.
    destruct H0.
    + inv H0.
      simpl.
      destruct (in_dec string_dec fn (map fst (getAllMethods m1))); simpl; auto.
      apply (in_map fst) in HInMeths.
      clear - DisjRules DisjMeths HInMeths i; firstorder.
    + eapply IHSubsteps; eauto.
Qed.

Lemma Step_rm_not_In m1 m2 o l:
  DisjKey (getAllRules m1) (getAllRules m2) ->
  DisjKey (getAllMethods m1) (getAllMethods m2) ->
  Step m2 o l ->
  forall fv, In fv l ->
             match fst (snd fv) with
             | Rle r => getBool (in_dec string_dec r (map fst (getAllRules m1)))
             | Meth (f, v) => getBool (in_dec string_dec f (map fst (getAllMethods m1)))
             end = false.
Proof.
  intros DisjRules DisjMeths.
  induction 1; simpl; auto; intros.
  - eapply Substeps_rm_not_In; eauto.
  - subst.
    assert (sth1: DisjKey (getAllRules m1) (getAllRules m0)) by
        (clear - DisjRules; unfold DisjKey in *; simpl in *;
         rewrite ?map_app in *; setoid_rewrite in_app_iff in DisjRules; firstorder fail).
    assert (sth2: DisjKey (getAllMethods m1) (getAllMethods m0)) by
        (clear - DisjMeths; unfold DisjKey in *; simpl in *;
         rewrite ?map_app in *; setoid_rewrite in_app_iff in DisjMeths; firstorder fail).
    assert (sth3: DisjKey (getAllRules m1) (getAllRules m2)) by
        (clear - DisjRules; unfold DisjKey in *; simpl in *;
         rewrite ?map_app in *; setoid_rewrite in_app_iff in DisjRules; firstorder fail).
    assert (sth4: DisjKey (getAllMethods m1) (getAllMethods m2)) by
        (clear - DisjMeths; unfold DisjKey in *; simpl in *;
         rewrite ?map_app in *; setoid_rewrite in_app_iff in DisjMeths; firstorder fail).
    specialize (IHStep1 sth1 sth2 fv).
    specialize (IHStep2 sth3 sth4 fv).
    rewrite ?map_app, in_app_iff in *.
    destruct fv as [? [b ?]]; simpl; auto.
    destruct b as [b | b]; auto; simpl in *; [| destruct b];
      match goal with
      | |- getBool ?P = _ => destruct P
      end; simpl; auto;
        rewrite ?in_app_iff in *; simpl in *; firstorder fail.
Qed.
  
Lemma DisjMeths_1_id m1 o1 l1 m2 o2 l2:
  DisjKey (getAllRules m1) (getAllRules m2) ->
  DisjKey (getAllMethods m1) (getAllMethods m2) ->
  Step m1 o1 l1 ->
  Step m2 o2 l2 ->
  filterExecs id m1 (l1 ++ l2) = l1.
Proof.
  intros DisjRules DisjMeths Step1 Step2.
  unfold filterExecs, id.
  rewrite filter_app.
  rewrite filter_true_list at 1.
  - rewrite filter_false_list at 1.
    + rewrite ?app_nil_r; auto.
    + eapply Step_rm_not_In; eauto.
  - eapply Step_rm_In; eauto.
Qed.
  
Lemma DisjMeths_2_id m1 o1 l1 m2 o2 l2:
  DisjKey (getAllRules m1) (getAllRules m2) ->
  DisjKey (getAllMethods m1) (getAllMethods m2) ->
  Step m1 o1 l1 ->
  Step m2 o2 l2 ->
  filterExecs id m2 (l1 ++ l2) = l2.
Proof.
  intros DisjRules DisjMeths Step1 Step2.
  unfold filterExecs, id.
  rewrite filter_app.
  rewrite filter_false_list at 1.
  - rewrite filter_true_list at 1.
    + rewrite ?app_nil_r; auto.
    + eapply Step_rm_In; eauto.
  - eapply Step_rm_not_In; eauto.
    + clear - DisjRules; firstorder fail.
    + clear - DisjMeths; firstorder fail.
Qed.
  
Lemma DisjMeths_1_negb m1 o1 l1 m2 o2 l2:
  DisjKey (getAllRules m1) (getAllRules m2) ->
  DisjKey (getAllMethods m1) (getAllMethods m2) ->
  Step m1 o1 l1 ->
  Step m2 o2 l2 ->
  filterExecs negb m1 (l1 ++ l2) = l2.
Proof.
  intros DisjRules DisjMeths Step1 Step2.
  unfold filterExecs, id.
  rewrite filter_app.
  rewrite filter_false_list at 1.
  - rewrite filter_true_list at 1.
    + rewrite ?app_nil_r; auto.
    + setoid_rewrite negb_true_iff.
      eapply Step_rm_not_In; eauto.
  - setoid_rewrite negb_false_iff.
    eapply Step_rm_In; eauto.
Qed.
  
Lemma DisjMeths_2_negb m1 o1 l1 m2 o2 l2:
  DisjKey (getAllRules m1) (getAllRules m2) ->
  DisjKey (getAllMethods m1) (getAllMethods m2) ->
  Step m1 o1 l1 ->
  Step m2 o2 l2 ->
  filterExecs negb m2 (l1 ++ l2) = l1.
Proof.
  intros DisjRules DisjMeths Step1 Step2.
  unfold filterExecs, id.
  rewrite filter_app.
  rewrite filter_true_list at 1.
  - rewrite filter_false_list at 1.
    + rewrite ?app_nil_r; auto.
    + setoid_rewrite negb_false_iff.
      eapply Step_rm_In; eauto.
  - setoid_rewrite negb_true_iff.
    eapply Step_rm_not_In; eauto.
    + clear - DisjRules; firstorder fail.
    + clear - DisjMeths; firstorder fail.
Qed.

Lemma Substeps_upd_SubList_key m o l:
  Substeps m o l ->
  forall x s v, In x (map fst l) ->
                In (s, v) x ->
                In s (map fst (getRegisters m)).
Proof.
  induction 1; intros.
  - simpl in *; tauto.
  - subst.
    destruct H0; subst; simpl in *.
    + apply (in_map (fun x => (fst x, projT1 (snd x)))) in H1; simpl in *.
      specialize (HUpdGood _ H1).
      apply (in_map fst) in HUpdGood.
      rewrite map_map in HUpdGood.
      simpl in *.
      setoid_rewrite (functional_extensionality (fun x => fst x) fst) in HUpdGood; auto.
    + eapply IHSubsteps; eauto.
  - subst.
    destruct H0; subst; simpl in *.
    + apply (in_map (fun x => (fst x, projT1 (snd x)))) in H1; simpl in *.
      specialize (HUpdGood _ H1).
      apply (in_map fst) in HUpdGood.
      rewrite map_map in HUpdGood.
      simpl in *.
      setoid_rewrite (functional_extensionality (fun x => fst x) fst) in HUpdGood; auto.
    + eapply IHSubsteps; eauto.
Qed.

Lemma Substeps_upd_In m o l:
  Substeps m o l ->
  forall x, In x (map fst l) ->
            forall s: string, In s (map fst x) ->
                              In s (map fst (getRegisters m)).
Proof.
  intros.
  rewrite in_map_iff in H1; dest; subst.
  destruct x0; simpl.
  eapply Substeps_upd_SubList_key; eauto.
Qed.

Lemma Substeps_read m o l:
  Substeps m o l ->
  forall s v, In (s, v) o ->
              In s (map fst (getRegisters m)).
Proof.
  induction 1; intros.
  - apply (f_equal (map fst)) in HRegs.
    rewrite ?map_map in *.
    setoid_rewrite (functional_extensionality (fun x => fst x) fst) in HRegs; auto.
    apply (in_map fst) in H.
    simpl in *.
    congruence.
  - subst.
    apply (f_equal (map fst)) in HRegs.
    rewrite ?map_map in *.
    setoid_rewrite (functional_extensionality (fun x => fst x) fst) in HRegs; auto.
    apply (in_map fst) in H0.
    simpl in *.
    congruence.
  - subst.
    apply (f_equal (map fst)) in HRegs.
    rewrite ?map_map in *.
    setoid_rewrite (functional_extensionality (fun x => fst x) fst) in HRegs; auto.
    apply (in_map fst) in H0.
    simpl in *.
    congruence.
Qed.
  
Lemma Step_upd_SubList_key m o l:
  Step m o l ->
  forall x s v, In x (map fst l) ->
                In (s, v) x ->
                In s (map fst (getAllRegisters m)).
Proof.
  induction 1; intros.
  - eapply Substeps_upd_SubList_key; eauto.
  - eapply IHStep; eauto.
  - simpl.
    subst.
    rewrite map_app in *.
    rewrite in_app_iff in *.
    specialize (IHStep1 x s v).
    specialize (IHStep2 x s v).
    tauto.
Qed.

Lemma Step_read m o l:
  Step m o l ->
  forall s v, In (s, v) o ->
              In s (map fst (getAllRegisters m)).
Proof.
  induction 1; intros.
  - eapply Substeps_read; eauto.
  - eapply IHStep; eauto.
  - simpl.
    subst.
    rewrite map_app in *.
    rewrite in_app_iff in *.
    specialize (IHStep1 s v).
    specialize (IHStep2 s v).
    tauto.
Qed.
 
Lemma Forall2_impl A B (P Q: A -> B -> Prop):
  (forall a b, P a b -> Q a b) ->
  forall la lb,
    Forall2 P la lb ->
    Forall2 Q la lb.
Proof.
  induction la; destruct lb; simpl; auto; intros.
  - inv H0; tauto.
  - inv H0; tauto.
  - inv H0; constructor; firstorder fail.
Qed.

Lemma Forall2_map_eq A B C (f: A -> C) (g: B -> C):
  forall la lb,
    Forall2 (fun a b => f a = g b) la lb ->
    map f la = map g lb.
Proof.
  induction la; destruct lb; simpl; auto; intros.
  - inv H.
  - inv H.
  - inv H.
    f_equal; firstorder fail.
Qed.

Lemma Forall2_app_eq_length A B (P: A -> B -> Prop) :
  forall l1a l2a l1b l2b,
    Forall2 P (l1a ++ l2a) (l1b ++ l2b) ->
    length l1a = length l1b ->
    Forall2 P l1a l1b /\
    Forall2 P l2a l2b.
Proof.
  induction l1a; simpl; auto; intros.
  - apply eq_sym in H0.
    rewrite length_zero_iff_nil in H0.
    subst; simpl in *.
    split; auto.
  - destruct l1b; simpl in *; [discriminate|].
    split; inv H; [| eapply IHl1a; eauto].
    constructor; auto.
    specialize (IHl1a _ _ _ H6).
    destruct IHl1a; auto.
Qed.

Lemma same_length_map_DisjKey A B (o: list (Attribute A)):
  forall (l1 l2: list (Attribute B)),
    map fst o = map fst l1 ++ map fst l2 ->
    DisjKey l1 l2 ->
    o = filter (fun x => getBool (in_dec string_dec (fst x) (map fst l1))) o ++
               filter (fun x => getBool (in_dec string_dec (fst x) (map fst l2))) o ->
    length (map fst l1) = length (filter (fun x => getBool (in_dec string_dec (fst x) (map fst l1))) o).
Proof.
  induction o; simpl; auto; intros.
  - apply eq_sym in H.
    apply app_eq_nil in H; subst; dest; subst.
    rewrite H; auto.
  - destruct l1; simpl; rewrite ?filter_false; auto; simpl in *.
    inv H; subst.
    rewrite H3 in *.
    destruct (string_dec (fst p) (fst p)); [simpl in *| exfalso; clear - n; tauto].
    inv H1.
    assert (sth: DisjKey l1 l2) by (clear - H0; firstorder fail).
    specialize (IHo _ _ H4 sth).
    destruct (in_dec string_dec (fst p) (map fst l2)); simpl in *.
    + unfold DisjKey in *.
      specialize (H0 (fst p)); simpl in *.
      destruct H0; tauto.
    + rewrite <- H2.
      simpl in *.
      assert (sth2:
                (fun x : string * A =>
                   getBool
                     match string_dec (fst p) (fst x) with
                     | left e => left (or_introl e)
                     | right n =>
                       match in_dec string_dec (fst x) (map fst l1) with
                       | left i => left (or_intror i)
                       | right n0 => right (fun H0 : fst p = fst x \/ In (fst x) (map fst l1) => match H0 with
                                                                                                 | or_introl Hc1 => n Hc1
                                                                                                 | or_intror Hc2 => n0 Hc2
                                                                                                 end)
                       end
                     end) = (fun x : string * A =>
                               match string_dec (fst p) (fst x) with
                               | left _ => true
                               | right _ =>
                                 getBool (in_dec string_dec (fst x) (map fst l1))
                               end)). {
        extensionality x.
        destruct (string_dec (fst p) (fst x)); auto.
        destruct (in_dec string_dec (fst x) (map fst l1)); auto.
      }
      setoid_rewrite sth2 in H2.
      setoid_rewrite sth2.
      clear sth2.
      destruct (in_dec string_dec (fst p) (map fst l1)).
      * assert (sth3: (fun x: string * A => if string_dec (fst p) (fst x) then true else getBool (in_dec string_dec (fst x) (map fst l1))) =
                      fun x => getBool (in_dec string_dec (fst x) (map fst l1))). {
          extensionality x.
          destruct (string_dec (fst p) (fst x)); auto.
          rewrite <- e0.
          destruct (in_dec string_dec (fst p) (map fst l1)); auto.
          exfalso; tauto.
        }
        rewrite sth3 in *.
        specialize (IHo H2).
        auto.
      * assert (sth2: ~ In (fst p) (map fst o)). {
          rewrite H4.
          rewrite in_app_iff.
          intro.
          tauto.
        }
        assert (sth3: filter (fun x: string * A => if string_dec (fst p) (fst x) then true else getBool (in_dec string_dec (fst x) (map fst l1))) o =
                      filter (fun x => getBool (in_dec string_dec (fst x) (map fst l1))) o). {
          clear - sth2.
          generalize p sth2; clear p sth2.
          induction o; simpl; auto; intros.
          assert (sth4: ~ In (fst p) (map fst o)) by tauto.
          assert (sth5: fst a <> fst p) by tauto.
          specialize (IHo _ sth4).
          rewrite IHo.
          destruct (string_dec (fst p) (fst a)); try tauto.
          rewrite e in *; tauto.
        }
        rewrite sth3 in *.
        specialize (IHo H2).
        auto.
Qed.
  
Section SplitJoin.
  Variable m1 m2: Mod.

  Variable DisjRegs: DisjKey (getAllRegisters m1) (getAllRegisters m2).
  Variable DisjRules: DisjKey (getAllRules m1) (getAllRules m2).
  Variable DisjMethods: DisjKey (getAllMethods m1) (getAllMethods m2).

  Lemma SplitStep o l:
    Step (ConcatMod m1 m2) o l ->
    Step m1 (filterRegs id m1 o) (filterExecs id m1 l) /\
    Step m2 (filterRegs id m2 o) (filterExecs id m2 l) /\
    o = filterRegs id m1 o ++ filterRegs id m2 o /\
    MatchingExecCalls_Concat (filterExecs id m1 l) (filterExecs id m2 l) m2 /\
    MatchingExecCalls_Concat (filterExecs id m2 l) (filterExecs id m1 l) m1 /\
    (forall x y : FullLabel,
        In x (filterExecs id m1 l) ->
        In y (filterExecs id m2 l) ->
        match fst (snd x) with
        | Rle _ => match fst (snd y) with
                   | Rle _ => False
                   | Meth _ => True
                   end
        | Meth _ => True
        end) /\
    l = filterExecs id m1 l ++ filterExecs id m2 l.
  Proof.
    intros H.
    inv H; intros.
    pose proof (Step_getAllRegisters_fst HStep1) as HRegs1.
    pose proof (Step_getAllRegisters_fst HStep2) as HRegs2.
    unfold filterRegs.
    rewrite DisjRegs_1_id with (l2 := getAllRegisters m2) (o1 := o1),
                               DisjRegs_2_id with (l1 := getAllRegisters m1) (o2 := o2); auto.
    rewrite DisjMeths_1_id with (m2 := m2) (o1 := o1) (o2 := o2), DisjMeths_2_id with (m1 := m1) (o1 := o1) (o2 := o2); auto.
    Opaque MatchingExecCalls_Concat.
    repeat split; auto.
    Transparent MatchingExecCalls_Concat.
  Qed.

  Lemma Step_upd_1 o l:
    Step (ConcatMod m1 m2) o l ->
    forall x s v,
      In x (map fst l) ->
      In (s, v) x ->
      In s (map fst (getAllRegisters m1)) ->
      In x (map fst (filterExecs id m1 l)).
  Proof.
    remember (ConcatMod m1 m2) as m.
    destruct 1; try discriminate; intros.
    inv Heqm.
    pose proof (Step_getAllRegisters_fst H) as HRegs1.
    pose proof (Step_getAllRegisters_fst H0) as HRegs2.
    unfold filterRegs.
    rewrite DisjMeths_1_id with (m2 := m2) (o1 := o1) (o2 := o2); auto.
    rewrite map_app in *.
    rewrite in_app_iff in *.
    destruct H1; auto.
    pose proof (Step_upd_SubList_key H0 _ _ _ H1 H2) as sth.
    firstorder fail.
  Qed.
    
  Lemma Step_upd_2 o l:
    Step (ConcatMod m1 m2) o l ->
    forall x s v,
      In x (map fst l) ->
      In (s, v) x ->
      In s (map fst (getAllRegisters m2)) ->
      In x (map fst (filterExecs id m2 l)).
  Proof.
    remember (ConcatMod m1 m2) as m.
    destruct 1; try discriminate; intros.
    inv Heqm.
    pose proof (Step_getAllRegisters_fst H) as HRegs1.
    pose proof (Step_getAllRegisters_fst H0) as HRegs2.
    unfold filterRegs.
    rewrite DisjMeths_2_id with (m1 := m1) (o1 := o1) (o2 := o2); auto.
    rewrite map_app in *.
    rewrite in_app_iff in *.
    destruct H1; auto.
    pose proof (Step_upd_SubList_key H _ _ _ H1 H2) as sth.
    firstorder fail.
  Qed.

  Local Notation optFullType := (fun fk => option (fullType type fk)).
  
  Lemma SplitTrace o ls:
    Trace (ConcatMod m1 m2) o ls ->
    Trace m1 (filterRegs id m1 o) (map (filterExecs id m1) ls) /\
    Trace m2 (filterRegs id m2 o) (map (filterExecs id m2) ls) /\
    o = filterRegs id m1 o ++ filterRegs id m2 o /\
    mapProp
      (fun l =>
         MatchingExecCalls_Concat (filterExecs id m1 l) (filterExecs id m2 l) m2 /\
         MatchingExecCalls_Concat (filterExecs id m2 l) (filterExecs id m1 l) m1 /\
         (forall x y : FullLabel,
             In x (filterExecs id m1 l) ->
             In y (filterExecs id m2 l) ->
             match fst (snd x) with
             | Rle _ => match fst (snd y) with
                        | Rle _ => False
                        | Meth _ => True
                        end
             | Meth _ => True
             end) /\
         l = filterExecs id m1 l ++ filterExecs id m2 l) ls /\
  map fst o = map fst (getAllRegisters (ConcatMod m1 m2)).
  Proof.
    Opaque MatchingExecCalls_Concat.
    induction 1; subst; simpl.
    - unfold filterRegs, filterExecs; simpl.
      rewrite ?map_app, ?filter_app.
      unfold id in *.
      assert (sth: Forall2 (fun o' r => fst o' = fst r) o' (getAllRegisters (ConcatMod m1 m2))) by
          (eapply Forall2_impl; eauto; intros; simpl in *; tauto).
      apply Forall2_map_eq in sth.
      simpl in sth.
      rewrite map_app in sth.
      assert (DisjRegs': DisjKey (getAllRegisters m2) (getAllRegisters m1)) by
          (clear - DisjRegs; firstorder).
      match goal with
      | |- _ /\ _ /\ ?P /\ _ /\ _ => assert P by (eapply filter_map_app_sameKey; eauto)
      end.
      simpl in *.
      pose proof (same_length_map_DisjKey sth DisjRegs H) as sth2.
      rewrite H in HUpdRegs.
      apply Forall2_app_eq_length in HUpdRegs; auto; dest.
      repeat split; auto; constructor; auto; subst; rewrite ?filter_app in *.
      rewrite map_length in *.
      congruence.
    - pose proof HStep as HStep'.
      apply SplitStep in HStep.
      dest.
      repeat split; try econstructor 2; eauto.
      + unfold UpdRegs in *; dest.
        repeat split; intros.
        * unfold filterRegs, id.
          pose proof (filter_map_simple (fun x => (fst x, projT1 (snd x))) (fun x => getBool (in_dec string_dec (fst x) (map fst (getAllRegisters m1))))
                                        o) as sth_o.
          pose proof (filter_map_simple (fun x => (fst x, projT1 (snd x))) (fun x => getBool (in_dec string_dec (fst x) (map fst (getAllRegisters m1))))
                                        o') as sth_o'.
          simpl in sth_o, sth_o'.
          rewrite <- ?sth_o, <- ?sth_o'.
          rewrite H12; auto.
        * unfold filterRegs, id in H14.
          rewrite filter_In in H14; dest.
          simpl in *.
          destruct (in_dec string_dec s (map fst (getAllRegisters m1))); [simpl in *| discriminate].
          specialize (H13 _ _ H14).
          destruct H13; [left; dest | right].
          -- exists x; repeat split; auto.
             eapply Step_upd_1; eauto.
          -- split; try intro; dest.
             ++ unfold filterExecs, id in H16.
                rewrite in_map_iff in H16; dest.
                rewrite filter_In in H19; dest.
                setoid_rewrite in_map_iff at 1 in H13.
                clear - H13 H16 H19 H18.
                firstorder fail.
             ++ unfold filterRegs, id.
                rewrite filter_In.
                simpl.
                destruct (in_dec string_dec s (map fst (getAllRegisters m1))); simpl; auto.
      + unfold UpdRegs in *; dest.
        repeat split; intros.
        * unfold filterRegs, id.
          pose proof (filter_map_simple (fun x => (fst x, projT1 (snd x))) (fun x => getBool (in_dec string_dec (fst x) (map fst (getAllRegisters m2))))
                                        o) as sth_o.
          pose proof (filter_map_simple (fun x => (fst x, projT1 (snd x))) (fun x => getBool (in_dec string_dec (fst x) (map fst (getAllRegisters m2))))
                                        o') as sth_o'.
          simpl in sth_o, sth_o'.
          rewrite <- ?sth_o, <- ?sth_o'.
          rewrite H12; auto.
        * unfold filterRegs, id in H14.
          rewrite filter_In in H14; dest.
          simpl in *.
          destruct (in_dec string_dec s (map fst (getAllRegisters m2))); [simpl in *| discriminate].
          specialize (H13 _ _ H14).
          destruct H13; [left; dest | right].
          -- exists x; repeat split; auto.
             eapply Step_upd_2; eauto.
          -- split; try intro; dest.
             ++ unfold filterExecs, id in H16.
                rewrite in_map_iff in H16; dest.
                rewrite filter_In in H19; dest.
                setoid_rewrite in_map_iff at 1 in H13.
                clear - H13 H16 H19 H18.
                firstorder fail.
             ++ unfold filterRegs, id.
                rewrite filter_In.
                simpl.
                destruct (in_dec string_dec s (map fst (getAllRegisters m2))); simpl; auto.
      + apply UpdRegs_same in HUpdRegs.
        unfold UpdRegs' in *; dest.
        rewrite H12 in H4.
        simpl in H4.
        rewrite map_app in H4.
        unfold filterRegs, id.
        apply filter_map_app_sameKey; auto.
      + apply UpdRegs_same in HUpdRegs.
        unfold UpdRegs' in *; dest.
        rewrite H12 in H4.
        simpl in H4.
        auto.
    Transparent MatchingExecCalls_Concat.
  Qed.

  Lemma JoinStep o1 o2 l1 l2:
    Step m1 o1 l1 ->
    Step m2 o2 l2 ->
    (MatchingExecCalls_Concat l1 l2 m2) ->
    (MatchingExecCalls_Concat l2 l1 m1) ->
    (forall x1 x2, In x1 l1 -> In x2 l2 -> match fst (snd x1), fst (snd x2) with
                                           | Rle _, Rle _ => False
                                           | _, _ => True
                                           end) ->
    Step (ConcatMod m1 m2) (o1 ++ o2) (l1 ++ l2).
  Proof.
    intros.
    econstructor 3; eauto.
  Qed.

  Lemma JoinTrace_basic l:
    forall o1 o2,
    Trace m1 o1 (map fst l) ->
    Trace m2 o2 (map snd l) ->
    (mapProp2 (fun l1 l2 => MatchingExecCalls_Concat l1 l2 m2) l) ->
    (mapProp2 (fun l1 l2 => MatchingExecCalls_Concat l2 l1 m1) l) ->
    (mapProp2 (fun l1 l2 =>
                 (forall x1 x2 : RegsT * (RuleOrMeth * MethsT),
                     In x1 l1 -> In x2 l2 -> match fst (snd x1) with
                                             | Rle _ => match fst (snd x2) with
                                                        | Rle _ => False
                                                        | Meth _ => True
                                                        end
                                             | Meth _ => True
                                             end)) l) ->
    Trace (ConcatMod m1 m2) (o1 ++ o2) (map (fun x => fst x ++ snd x) l).
  Proof.
    induction l; simpl; intros.
    - inversion H; inversion H0; subst; try discriminate.
      constructor; auto.
      simpl.
      eapply Forall2_app in HUpdRegs0; eauto.
    - destruct a; simpl in *; dest.
      inv H; [discriminate| ]; inv H0; [discriminate|].
      inv HTrace; inv HTrace0.
      specialize (IHl _ _ HOldTrace HOldTrace0 H6 H5 H4).
      econstructor 2 with (o := o ++ o0); eauto.
      eapply JoinStep; eauto.
      unfold UpdRegs in *; dest.
      split.
      + rewrite ?map_app.
        congruence.
      + intros.
        rewrite in_app_iff in H9.
        destruct H9.
        * specialize (H8 _ _ H9).
          rewrite ?map_app.
          repeat setoid_rewrite in_app_iff.
          destruct H8; [left; dest | right; dest].
          -- exists x; split; auto.
          -- split; auto.
             intro.
             dest.
             destruct H11; [firstorder fail|].
             rewrite in_map_iff in H12; dest.
             destruct x0.
             subst.
             simpl in *.
             pose proof (Step_upd_SubList_key HStep0 _ _ _ H11 H13).
             pose proof (Step_read HStep _ _ H10).
             firstorder fail.
        * specialize (H0 _ _ H9).
          rewrite ?map_app.
          repeat setoid_rewrite in_app_iff.
          destruct H0; [left; dest | right; dest].
          -- exists x; split; auto.
          -- split; auto.
             intro.
             dest.
             destruct H11; [|firstorder fail].
             rewrite in_map_iff in H12; dest.
             destruct x0.
             subst.
             simpl in *.
             pose proof (Step_upd_SubList_key HStep _ _ _ H11 H13).
             pose proof (Step_read HStep0 _ _ H10).
             firstorder fail.
  Qed.

  Lemma JoinTrace_len l1:
    forall l2 o1 o2,
      length l1 = length l2 ->
      Trace m1 o1 l1 ->
      Trace m2 o2 l2 ->
      (mapProp_len (fun l1 l2 => MatchingExecCalls_Concat l1 l2 m2) l1 l2) ->
      (mapProp_len (fun l1 l2 => MatchingExecCalls_Concat l2 l1 m1) l1 l2) ->
      (mapProp_len (fun l1 l2 =>
                      (forall x1 x2 : RegsT * (RuleOrMeth * MethsT),
                          In x1 l1 -> In x2 l2 -> match fst (snd x1) with
                                                  | Rle _ => match fst (snd x2) with
                                                             | Rle _ => False
                                                             | Meth _ => True
                                                             end
                                                  | Meth _ => True
                                                  end)) l1 l2) ->
      Trace (ConcatMod m1 m2) (o1 ++ o2) (map (fun x => fst x ++ snd x) (List.combine l1 l2)).
  Proof.
    intros.
    eapply JoinTrace_basic; rewrite ?fst_combine, ?snd_combine; eauto;
      eapply mapProp2_len_same; eauto.
  Qed.

  Lemma JoinTrace l1:
    forall l2 o1 o2,
      length l1 = length l2 ->
      Trace m1 o1 l1 ->
      Trace m2 o2 l2 ->
      nthProp2 (fun l1 l2 => MatchingExecCalls_Concat l1 l2 m2 /\
                             MatchingExecCalls_Concat l2 l1 m1 /\
                             (forall x1 x2 : RegsT * (RuleOrMeth * MethsT),
                                 In x1 l1 -> In x2 l2 -> match fst (snd x1) with
                                                         | Rle _ => match fst (snd x2) with
                                                                    | Rle _ => False
                                                                    | Meth _ => True
                                                                    end
                                                         | Meth _ => True
                                                         end)) l1 l2 ->
      Trace (ConcatMod m1 m2) (o1 ++ o2) (map (fun x => fst x ++ snd x) (List.combine l1 l2)).
  Proof.
    intros ? ? ? ?.
    setoid_rewrite <- mapProp_len_nthProp2; auto.
    repeat rewrite mapProp_len_conj; auto.
    pose proof (@JoinTrace_len l1 l2 o1 o2 H).
    intros; dest.
    firstorder fail.
  Qed.
End SplitJoin.

Lemma InExec_dec: forall x l, {InExec x l} + {~ InExec x l}.
Proof.
  unfold InExec; intros.
  apply in_dec; intros.
  decide equality.
  - apply string_dec.
  - apply MethT_dec.
Qed.

Lemma Substeps_meth_In m o l:
  Substeps m o l ->
  forall u f cs, In (u, (Meth f, cs)) l ->
                 In (fst f) (map fst (getMethods m)).
Proof.
  induction 1; simpl; intros; subst; try tauto.
  - simpl in *.
    destruct H0.
    + inv H0.
    + eapply IHSubsteps; eauto.
  - simpl in *.
    destruct H0.
    + inv H0.
      simpl.
      apply (in_map fst _ _ HInMeths).
    + eapply IHSubsteps; eauto.
Qed.

Lemma Step_meth_In m o l:
  Step m o l ->
  forall u f cs, In (u, (Meth f, cs)) l ->
                 In (fst f) (map fst (getAllMethods m)).
Proof.
  induction 1; simpl; intros; subst; try tauto.
  - eapply Substeps_meth_In; eauto.
  - eauto.
  - rewrite map_app, in_app_iff in *.
    clear - IHStep1 IHStep2 H1;
      firstorder fail.
Qed.

Lemma Step_meth_InExec m o l:
  Step m o l ->
  forall f, InExec f l ->
            In (fst f) (map fst (getAllMethods m)).
Proof.
  intros.
  unfold InExec in *.
  rewrite in_map_iff in H0.
  dest.
  destruct x; simpl in *.
  destruct p; simpl in *; subst.
  eapply Step_meth_In; eauto.
Qed.

Lemma Trace_meth_In m o ls:
  Trace m o ls ->
  forall u f cs i l, nth_error ls i = Some l ->
                     In (u, (Meth f, cs)) l ->
                     In (fst f) (map fst (getAllMethods m)).
Proof.
  induction 1; simpl; intros; auto; destruct i; simpl in *.
  - subst; simpl in *; congruence.
  - subst; simpl in *; congruence.
  - subst.
    eapply Step_meth_In with (o := o) (u := u) (f := f) (cs := cs) in H1; eauto.
    inv H0; auto.
  - subst; simpl in *.
    eapply IHTrace; eauto.
Qed.
  
Lemma Trace_meth_In_map m o ls:
  Trace m o ls ->
  forall f i l, nth_error ls i = Some l ->
                In (Meth f) (map (fun x => fst (snd x)) l) ->
                In (fst f) (map fst (getAllMethods m)).
Proof.
  intros.
  rewrite in_map_iff in H1; dest.
  destruct x.
  destruct p.
  simpl in *; subst.
  eapply Trace_meth_In; eauto.
Qed.
  
Lemma Trace_meth_InExec m o ls:
  Trace m o ls ->
  forall f i l, nth_error ls i = Some l ->
                InExec f l ->
                In (fst f) (map fst (getAllMethods m)).
Proof.
  apply Trace_meth_In_map.
Qed.


Lemma InExec_app_iff: forall x l1 l2, InExec x (l1 ++ l2) <-> InExec x l1 \/ InExec x l2.
Proof.
  unfold InExec in *; intros.
  rewrite map_app.
  rewrite in_app_iff.
  tauto.
Qed.

Lemma InCall_app_iff: forall x l1 l2, InCall x (l1 ++ l2) <-> InCall x l1 \/ InCall x l2.
Proof.
  unfold InCall in *; intros.
  setoid_rewrite in_app_iff.
  firstorder fail.
Qed.

Lemma NotInDef_ZeroExecs_Substeps m o ls f :
  ~In (fst f) (map fst (getMethods m)) ->
  Substeps m o ls ->
  (getNumExecs f ls = 0%Z).
Proof.
  induction 2.
  - reflexivity.
  - rewrite HLabel.
    unfold getNumExecs in *; simpl; assumption.
  - rewrite HLabel.
    unfold getNumExecs.
    Opaque getNumFromExecs.
    simpl; destruct (MethT_dec f (fn, existT _ (projT1 fb) (argV, retV))).
    + destruct f; inv e.
      apply (in_map fst) in HInMeths; simpl in *; contradiction.
    + rewrite getNumFromExecs_neq_cons; auto.
    Transparent getNumFromExecs.
Qed.

Lemma NotInDef_ZeroExecs_Step m o ls f:
  ~In (fst f) (map fst (getAllMethods m)) ->
  Step m o ls ->
  (getNumExecs f ls = 0%Z).
Proof.
  induction 2; simpl in *; auto.
  - apply (NotInDef_ZeroExecs_Substeps _ H HSubsteps).
  - rewrite HLabels.
    rewrite getNumExecs_app.
    rewrite map_app, in_app_iff in H.
    assert (~In (fst f) (map fst (getAllMethods m1)) /\ ~In (fst f) (map fst (getAllMethods m2)));[tauto|]; dest.
    rewrite IHStep1, IHStep2; auto.
Qed.

Lemma Trace_meth_InExec' m o ls:
  Trace m o ls ->
  forall f i l, nth_error ls i = Some l ->
                (0 < getNumExecs f l)%Z ->
                In (fst f) (map fst (getAllMethods m)).
Proof.
  induction 1; subst; simpl; intros; auto; destruct i; simpl in *; try discriminate.
  - inv H0.
    destruct (in_dec string_dec (fst f) (map fst (getAllMethods m))); auto.
    specialize (NotInDef_ZeroExecs_Step _ n HStep) as noExec_zero.
    apply False_ind; Omega.omega.
  - eapply IHTrace; eauto.
Qed.

Lemma Step_meth_InCall_InDef_InExec m o ls:
  Step m o ls ->
  forall (f : MethT),
    In (fst f) (map fst (getAllMethods m)) ->
    (getNumCalls f ls <= getNumExecs f ls)%Z.
Proof.
  induction 1.
  - unfold MatchingExecCalls_Base in *.
    firstorder fail.
  - assumption.
  - subst.
    simpl.
    rewrite map_app.
    setoid_rewrite getNumCalls_app.
    setoid_rewrite getNumExecs_app.
    setoid_rewrite in_app_iff.
    intros.
    unfold MatchingExecCalls_Concat in *.
    specialize (getNumExecs_nonneg f l1) as P1;specialize (getNumExecs_nonneg f l2) as P2.
    destruct H1.
    + specialize (IHStep1 _ H1); destruct (Z.eq_dec (getNumCalls f l2) 0%Z).
      * rewrite e, Z.add_0_r;Omega.omega.
      * specialize (HMatching2 _ n H1); dest; Omega.omega.
    + specialize (IHStep2 _ H1); destruct (Z.eq_dec (getNumCalls f l1) 0%Z).
      * rewrite e; simpl; Omega.omega.
      * specialize (HMatching1 _ n H1); dest; Omega.omega.
Qed.

Lemma Trace_meth_InCall_InDef_InExec m o ls:
  Trace m o ls ->
  forall (f : MethT) (i : nat) (l : list (RegsT * (RuleOrMeth * MethsT))),
    nth_error ls i = Some l -> In (fst f) (map fst (getAllMethods m)) ->
    (getNumCalls f l <= getNumExecs f l)%Z.
Proof.
  induction 1; subst; auto; simpl; intros.
  - destruct i; simpl in *; try congruence.
  - destruct i; simpl in *.
    + inv H0.
      eapply Step_meth_InCall_InDef_InExec; eauto.
    + eapply IHTrace; eauto.
Qed.
  
Lemma Trace_meth_InCall_not_InExec_not_InDef m o ls:
  Trace m o ls ->
  forall (f : MethT) (i : nat) (l : list (RegsT * (RuleOrMeth * MethsT))),
    nth_error ls i = Some l ->
    ~(getNumCalls f l <= getNumExecs f l)%Z ->
    ~ In (fst f) (map fst (getAllMethods m)).
Proof.
  intros.
  intro.
  eapply Trace_meth_InCall_InDef_InExec in H2; eauto.
Qed.

Lemma InCall_dec: forall x l, InCall x l \/ ~ InCall x l.
Proof.
  unfold InCall; intros.
  induction l; simpl.
  - right.
    intro.
    dest; auto.
  - destruct IHl; dest.
    + left.
      exists x0.
      split; tauto.
    + pose proof (in_dec MethT_dec x (snd (snd a))).
      destruct H0.
      * left; exists a; tauto.
      * right; intro.
        dest.
        destruct H0; subst.
        -- auto.
        -- firstorder fail.
Qed.

Lemma InCall_dec_quant1: forall (f: string) l,
    {exists v: {x: Kind * Kind & SignT x}, In (f, v) l} + {forall v, ~ In (f, v) l}.
Proof.
  unfold InCall; intros.
  induction l; simpl.
  - right; intro; intro; auto.
  - destruct IHl.
    + left.
      dest.
      exists x; tauto.
    + assert (sth: {exists v, a = (f, v)} + {forall v, a <> (f, v)}).
      { destruct a; simpl in *.
        destruct (string_dec f s); subst.
        - left.
          exists s0; auto.
        - right; intro; intro.
          inv H.
          tauto.
      }
      destruct sth.
      * left.
        dest.
        exists x; auto.
      * right.
        intro.
        specialize (n v).
        specialize (n0 v).
        tauto.
Qed.

Lemma InCall_dec_quant2: forall f l, (exists v, InCall (f, v) l) \/ forall v, ~ InCall (f, v) l.
Proof.
  unfold InCall; intros.
  induction l; simpl.
  - right.
    intro.
    intro.
    dest; auto.
  - destruct IHl; dest.
    + left.
      exists x.
      exists x0.
      split; tauto.
    + destruct (InCall_dec_quant1 f (snd (snd a))).
      * left; dest.
        exists x.
        exists a.
        tauto.
      * right; intro; intro.
        dest.
        specialize (H v).
        specialize (n v).
        destruct H0; subst; auto.
        firstorder fail.
Qed.

Lemma TraceInclusion_refl: forall m, TraceInclusion m m.
Proof.
  unfold TraceInclusion; intros.
  exists o1, ls1.
  repeat split; auto.
  unfold nthProp2; intros.
  destruct (nth_error ls1 i); auto.
  repeat split; intros; tauto.
Qed.

Lemma TraceInclusion_trans: forall m1 m2 m3, TraceInclusion m1 m2 ->
                                               TraceInclusion m2 m3 ->
                                               TraceInclusion m1 m3.
Proof.
  unfold TraceInclusion; intros.
  specialize (H _ _ H1); dest.
  specialize (H0 _ _ H); dest.
  exists x1, x2.
  repeat split; auto.
  - congruence.
  - unfold nthProp2, WeakInclusion in *; intros.
    specialize (H3 i); specialize (H5 i).
    case_eq (nth_error ls1 i);
      case_eq (nth_error x0 i);
      case_eq (nth_error x2 i);
      intros; auto.
    + rewrite H6, H7, H8 in *.
      dest.
      split;[eauto using eq_trans|auto].
    + pose proof (nth_error_len _ _ _ H7 H6 H4); contradiction.
Qed.

Global Instance TraceEquiv_rewrite_l:
  Proper (eq ==> TraceEquiv ==> iff) TraceInclusion.
Proof.
   unfold Proper, iff, Basics.flip, Basics.impl, TraceEquiv, respectful; intros; dest; try split; intros; auto; subst;
    repeat (eapply TraceInclusion_trans; eauto).
Qed.

Global Instance TraceEquiv_rewrite_r:
  Proper (TraceEquiv ==> eq ==> iff) TraceInclusion.
Proof.
   unfold Proper, iff, Basics.flip, Basics.impl, TraceEquiv, respectful; intros; dest; try split; intros; auto; subst;
    repeat (eapply TraceInclusion_trans; eauto).
Qed.

Section Test.
  Variable m1 m2 m3 m4: Mod.
  Variable H1: TraceEquiv m1 m2.
  Variable H2: TraceEquiv m3 m4.

  Goal TraceInclusion m2 m4 <-> TraceInclusion m1 m3.
  Proof.
    rewrite H1.
    rewrite H2.
    tauto.
  Qed.

  Goal TraceInclusion m1 m4 <-> TraceInclusion m2 m3.
    rewrite H1.
    rewrite H2.
    tauto.
  Qed.
End Test.


Lemma UpdRegs_nil_upd: forall o, NoDup (map fst o) -> forall o', UpdRegs [] o o' -> o = o'.
Proof.
  unfold UpdRegs.
  intros.
  dest.
  simpl in *.
  assert (sth: forall s v, In (s, v) o' -> In (s, v) o).
  { intros.
    specialize (H1 s v H2).
    destruct H1; dest; try auto.
    tauto.
  }
  clear H1.
  generalize o' H H0 sth.
  clear o' H H0 sth.
  induction o; destruct o'; simpl; auto; intros.
  - discriminate.
  - discriminate.
  - inv H0.
    inv H.
    specialize (IHo _ H6 H4).
    destruct p, a; simpl in *; subst; auto; repeat f_equal; auto.
    + specialize (sth s s0 (or_introl eq_refl)).
      destruct sth.
      * inv H; subst; auto.
      * apply (in_map fst) in H; simpl in *; tauto.
    + eapply IHo; intros.
      specialize (sth _ _ (or_intror H)).
      destruct sth; [|auto].
      inv H0; subst.
      apply (f_equal (map fst)) in H4.
      rewrite ?map_map in *; simpl in *.
      setoid_rewrite (functional_extensionality (fun x => fst x) fst) in H4; try tauto.
      apply (in_map fst) in H; simpl in *; congruence.
Qed.

Lemma Trace_NoDup m o l:
  Trace m o l ->
  NoDup (map fst (getAllRegisters m)) ->
  NoDup (map fst o).
Proof.
  induction 1; subst.
  - intros.
    assert (sth: Forall2 (fun o' r => fst o' = fst r) o' (getAllRegisters m)) by
        (eapply Forall2_impl; eauto; intros; simpl in *; tauto).
    clear HUpdRegs.
    apply Forall2_map_eq in sth.
    congruence.
  - unfold UpdRegs in *; intros; dest.
    apply (f_equal (map fst)) in H1.
    rewrite ?map_map in *; simpl in *.
    setoid_rewrite (functional_extensionality (fun x => fst x) fst) in H1; try tauto.
    rewrite H1 in *; eapply IHTrace; eauto.
Qed.

Lemma Trace_sameRegs m o l:
  Trace m o l ->
  getKindAttr o = getKindAttr (getAllRegisters m).
Proof.
  induction 1; subst; auto.
  - assert (sth: Forall2 (fun o' r => (fun x => (fst x, projT1 (snd x))) o' = (fun x => (fst x, projT1 (snd x))) r) o' (getAllRegisters m)). {
      eapply Forall2_impl; eauto; intro; simpl in *.
      intros; dest.
      f_equal; auto.
    }
    clear HUpdRegs.
    apply Forall2_map_eq in sth.
    congruence.
  - unfold UpdRegs in *; dest. congruence.
Qed.

Lemma Step_empty m:
  forall o,
    getKindAttr o = getKindAttr (getAllRegisters m) ->
    Step m o [].
Proof.
  induction m; simpl; intros; auto.
  - constructor; auto.
    + constructor; auto.
    + unfold MatchingExecCalls_Base.
      intros; rewrite getNumCalls_nil, getNumExecs_nil; reflexivity.
  - constructor 2.
    + eapply IHm; eauto.
    + intros.
      unfold getListFullLabel_diff; auto.
  - rewrite map_app in H.
    pose proof (list_split _ _ _ _ _ H).
    dest.
    specialize (IHm1 _ H1).
    specialize (IHm2 _ H2).
    eapply ConcatModStep with (o1 := x) (o2 := x0) (l1 := []) (l2 := []); eauto.
    + unfold MatchingExecCalls_Concat; intros.
      rewrite getNumCalls_nil in H3; apply False_ind; apply H3; reflexivity.
    + unfold MatchingExecCalls_Concat; intros.
      rewrite getNumCalls_nil in H3; apply False_ind; apply H3; reflexivity.
    + intros.
      simpl in *; tauto.
Qed.

Lemma Trace_Step_empty m o l:
  Trace m o l ->
  Step m o [].
Proof.
  intros.
  apply Trace_sameRegs in H.
  apply Step_empty in H.
  auto.
Qed.

Section StepSimulation.
  Variable imp spec: Mod.
  Variable simRel: RegsT -> RegsT -> Prop.
  Variable initRel: forall rimp, Forall2 regInit rimp (getAllRegisters imp) -> exists rspec, Forall2 regInit rspec (getAllRegisters spec) /\ simRel rimp rspec.
  Variable NoDupRegs: NoDup (map fst (getAllRegisters imp)).
  
  Variable stepSimulationNonZero:
    forall oImp lImp oImp',
      Step imp oImp lImp ->
      lImp <> nil ->
      UpdRegs (map fst lImp) oImp oImp' ->
      forall oSpec,
        simRel oImp oSpec ->
        exists lSpec oSpec',
          Step spec oSpec lSpec /\
          UpdRegs (map fst lSpec) oSpec oSpec' /\
          simRel oImp' oSpec' /\ WeakInclusion lImp lSpec.

  Lemma StepSimulation':
    forall (oImp : RegsT) (lsImp : list (list FullLabel)),
      Trace imp oImp lsImp ->
      exists (oSpec : RegsT) (lsSpec : list (list FullLabel)),
        Trace spec oSpec lsSpec /\
        Datatypes.length lsImp = Datatypes.length lsSpec /\
        nthProp2 WeakInclusion lsImp lsSpec /\
        simRel oImp oSpec.
  Proof.
    induction 1; subst; simpl; auto; intros.
    - pose proof (initRel HUpdRegs) as [rspec rspecProp].
      exists rspec, []; repeat split; dest; auto.
      + econstructor 1; eauto.
      + unfold nthProp2; intros.
        destruct (nth_error [] i); auto.
        repeat split; intros; tauto.
    - dest.
      destruct l.
      + simpl in *.
        exists x, ([] :: x0); repeat split; simpl in *; auto.
        * constructor 2 with (o := x) (ls := x0) (l := []); simpl; auto.
          -- eapply Trace_Step_empty; eauto.
          -- clear.
             unfold UpdRegs; split; intros; try tauto.
             right; split; try intro; dest; auto.
        * rewrite nthProp2_cons; split; simpl; auto; repeat split; dest; simpl in *; try tauto.
        * pose proof (Trace_NoDup H NoDupRegs) as sth.
          pose proof (UpdRegs_nil_upd sth HUpdRegs); subst; auto.
      + specialize (stepSimulationNonZero HStep ltac:(intro; discriminate) HUpdRegs H3).
        destruct stepSimulationNonZero as [lSpec [oSpec' [stepSpec [updSpec [sim lSpecProp]]]]].
        exists oSpec', (lSpec :: x0); repeat split; simpl in *; auto.
        * econstructor 2; eauto.
        * simpl.
          rewrite nthProp2_cons; split; auto.
  Qed.

  Theorem StepSimulation:
    TraceInclusion imp spec.
  Proof.
    unfold TraceInclusion; intros.
    eapply StepSimulation' in H.
    dest.
    exists x, x0.
    repeat split; auto.
  Qed.
End StepSimulation.

Lemma NoMeths_Substeps m o ls:
  getMethods m = [] ->
  Substeps m o ls ->
  ls = nil \/ exists u rl cs, ls = (u, (Rle rl, cs)) :: nil.
Proof.
  intros nilMeths substeps.
  induction substeps; intros; auto; subst.
  - destruct IHsubsteps; subst.
    + right.
      repeat eexists; eauto.
    + dest; subst.
      specialize (HNoRle _ (or_introl eq_refl)); simpl in *.
      tauto.
  - rewrite nilMeths in *.
    simpl in *.
    tauto.
Qed.


Section SimulationZero.
  Variable imp spec: BaseModule.
  Variable simRel: RegsT -> RegsT -> Prop.
  Variable initRel: forall rimp, Forall2 regInit rimp (getRegisters imp) -> exists rspec, Forall2 regInit rspec (getRegisters spec) /\ simRel rimp rspec.
  Variable NoDupRegs: NoDup (map fst (getRegisters imp)).

  Variable NoMeths: getMethods imp = [].
  Variable NoMethsSpec: getMethods spec = [].

  Variable simulation:
    forall oImp uImp rleImp csImp oImp',
      Substeps imp oImp [(uImp, (Rle rleImp, csImp))] ->
      UpdRegs [uImp] oImp oImp' ->
      forall oSpec,
        simRel oImp oSpec ->
        ((getKindAttr oSpec = getKindAttr (getRegisters spec) /\ simRel oImp' oSpec /\ csImp = []) \/
         (exists uSpec rleSpec oSpec',
             Substeps spec oSpec [(uSpec, (Rle rleSpec, csImp))] /\
             UpdRegs [uSpec] oSpec oSpec' /\
             simRel oImp' oSpec')).

  Theorem simulationZero:
    TraceInclusion (Base imp) (Base spec).
  Proof.
    apply StepSimulation with (simRel := simRel); auto; intros.
    inv H.
    pose proof HSubsteps as sth.
    inv HSubsteps; simpl in *.
    - tauto.
    - pose proof (NoMeths_Substeps NoMeths HSubstep).
      destruct H; [subst | dest; subst].
      + simpl in *.
        specialize (@simulation _ _ _ _ oImp' sth H1 _ H2).
        destruct simulation; dest; subst.
        * exists nil, oSpec.
          repeat split; auto.
          constructor; auto.
          -- constructor; auto.
          -- unfold MatchingExecCalls_Base; intros; reflexivity.
          -- intros.
             right; split; try intro; dest; simpl in *; try tauto.
          -- intros; dest. inv H4.
        
        * exists [(x, (Rle x0, cs))], x1.
          repeat split; auto.
          -- constructor; auto.
             unfold MatchingExecCalls_Base; intros.
             rewrite NoMethsSpec in *; simpl in *; tauto.
          -- unfold UpdRegs in *; dest.
             auto.
          -- intros.
             unfold UpdRegs in *; dest.
             simpl in *.
             eapply H6; eauto.
          -- intros; dest.
             destruct H5;simpl in *; inv H5.
             exists rn; left; reflexivity.
      + specialize (HNoRle _ (or_introl eq_refl)); simpl in *; tauto.
    - rewrite NoMeths in *.
      simpl in *; tauto.
  Qed.
End SimulationZero.

Lemma createHide_hides: forall hides m, getHidden (createHide m hides) = hides.
Proof.
  induction hides; simpl; auto; intros; f_equal; auto.
Qed.

Lemma createHide_Regs: forall m l, getAllRegisters (createHide m l) = getRegisters m.
Proof.
  intros.
  induction l; simpl; auto; intros.
Qed.
  
Lemma createHide_Rules: forall m l, getAllRules (createHide m l) = getRules m.
Proof.
  intros.
  induction l; simpl; auto; intros.
Qed.
  
Lemma createHide_Meths: forall m l, getAllMethods (createHide m l) = getMethods m.
Proof.
  intros.
  induction l; simpl; auto; intros.
Qed.
  
Lemma createHideMod_Meths: forall m l, getAllMethods (createHideMod m l) = getAllMethods m.
Proof.
  intros.
  induction l; simpl; auto; intros.
Qed.
  
Lemma getFlat_Hide m s:
  getFlat (HideMeth m s) = getFlat m.
Proof.
  unfold getFlat; auto.
Qed.

Lemma getAllRegisters_flatten: forall m, getAllRegisters (flatten m) = getAllRegisters m.
Proof.
  unfold flatten, getFlat; intros.
  rewrite createHide_Regs.
  auto.
Qed.

Lemma WfMod_Hidden m:
  WfMod m ->
  forall s, In s (getHidden m) -> In s (map fst (getAllMethods m)).
Proof.
  induction 1; simpl; auto; intros.
  - tauto.
  - destruct H0; subst; auto.
  - rewrite map_app, in_app_iff in *.
    specialize (IHWfMod1 s); specialize (IHWfMod2 s); tauto.
Qed.

Lemma SemActionUpdSub o k a reads upds calls ret:
  @SemAction o k a reads upds calls ret ->
  SubList (getKindAttr upds) (getKindAttr o).
Proof.
  induction 1; auto; subst;
    unfold SubList in *; intros;
      rewrite ?in_app_iff in *.
  - rewrite map_app, in_app_iff in *.
    destruct H1; firstorder fail.
  - subst; firstorder; simpl in *.
    subst.
    assumption.
  - subst.
    rewrite map_app, in_app_iff in *.
    destruct H1; intuition.
  - subst.
    rewrite map_app, in_app_iff in *.
    destruct H1; intuition.
  - subst; simpl in *; intuition.
Qed.

Lemma SemActionExpandRegs o k a reads upds calls ret:
  @SemAction o k a reads upds calls ret ->
  forall o', SubList reads o' ->
             SubList (getKindAttr upds) (getKindAttr o') ->
             @SemAction o' k a reads upds calls ret.
Proof.
  intros.
  induction H; try solve [econstructor; auto].
  - subst.
    specialize (IHSemAction H0).
    econstructor; eauto.
  - subst.
    apply SubList_app_l in H0; dest.
    rewrite map_app in *.
    apply SubList_app_l in H1; dest.
    specialize (IHSemAction1 H0 H1).
    specialize (IHSemAction2 H3 H4).
    econstructor; eauto.
  - subst.
    apply SubList_cons in H0; dest.
    specialize (IHSemAction H2 H1).
    econstructor; eauto.
  - subst.
    simpl in *.
    apply SubList_cons in H1; dest.
    specialize (IHSemAction H0 H2).
    econstructor; eauto.
  - subst.
    apply SubList_app_l in H0; dest.
    rewrite map_app in *.
    apply SubList_app_l in H1; dest.
    specialize (IHSemAction1 H0 H1).
    specialize (IHSemAction2 H3 H4).
    econstructor; eauto.
  - subst.
    apply SubList_app_l in H0; dest.
    rewrite map_app in *.
    apply SubList_app_l in H1; dest.
    specialize (IHSemAction1 H0 H1).
    specialize (IHSemAction2 H3 H4).
    econstructor 8; eauto.
Qed.

Lemma Substeps_combine m1 o1 l1:
  Substeps m1 o1 l1 ->
  forall m2 o2 l2  (DisjRegs: DisjKey (getRegisters m1) (getRegisters m2)) (DisjMeths: DisjKey (getMethods m1) (getMethods m2))
         (HOneRle: forall x1 x2, In x1 l1 -> In x2 l2 -> match fst (snd x1), fst (snd x2) with
                                                         | Rle _, Rle _ => False
                                                         | _, _ => True
                                                         end),
    Substeps m2 o2 l2 ->
    Substeps (BaseMod (getRegisters m1 ++ getRegisters m2) (getRules m1 ++ getRules m2) (getMethods m1 ++ getMethods m2)) (o1 ++ o2) (l1 ++ l2).
Proof.
  induction 1; intros.
  - induction H; simpl in *.
    + constructor 1; auto; simpl.
      rewrite ?map_app; congruence.
    + econstructor 2; eauto; simpl; rewrite ?map_app; try congruence.
      * rewrite in_app_iff; right; eassumption.
      * pose proof (SemActionReadsSub HAction).
        pose proof (SemActionUpdSub HAction).
        eapply SemActionExpandRegs; eauto; unfold SubList in *; intros; rewrite ?map_app, ?in_app_iff; right.
        -- eapply H0; eauto.
        -- eapply H1; eauto.
      * unfold SubList in *; intros.
        rewrite in_app_iff; right; eapply HReadsGood; eauto.
      * unfold SubList in *; intros.
        rewrite in_app_iff; right; eapply HUpdGood; eauto.
      * eapply IHSubsteps; intros;
          unfold InCall in *; simpl in *; dest; tauto.
    + econstructor 3; eauto; simpl; rewrite ?map_app; try congruence.
      * rewrite in_app_iff; right; eassumption.
      * pose proof (SemActionReadsSub HAction).
        pose proof (SemActionUpdSub HAction).
        eapply SemActionExpandRegs; eauto; unfold SubList in *; intros; rewrite ?map_app, ?in_app_iff; right.
        -- eapply H0; eauto.
        -- eapply H1; eauto.
      * unfold SubList in *; intros.
        rewrite in_app_iff; right; eapply HReadsGood; eauto.
      * unfold SubList in *; intros.
        rewrite in_app_iff; right; eapply HUpdGood; eauto.
      * eapply IHSubsteps; intros;
          unfold InCall in *; simpl in *; dest; tauto.
  - subst; simpl.
    assert (sth_else: forall x1 x2, In x1 ls -> In x2 l2 -> match fst (snd x1), fst (snd x2) with
                                                            | Rle _, Rle _ => False
                                                            | _, _ => True
                                                            end) by (clear - HOneRle; firstorder fail).
    econstructor 2; eauto; simpl; rewrite ?map_app; try congruence.
    + inv H0; congruence.
    + rewrite in_app_iff; left; eassumption.
    + pose proof (SemActionReadsSub HAction).
      pose proof (SemActionUpdSub HAction).
      eapply SemActionExpandRegs; eauto; unfold SubList in *; intros; rewrite ?map_app, ?in_app_iff; left.
      * eapply H1; eauto.
      * eapply H2; eauto.
    + unfold SubList in *; intros.
      rewrite in_app_iff; left; eapply HReadsGood; eauto.
    + unfold SubList in *; intros.
      rewrite in_app_iff; left; eapply HUpdGood; eauto.
    + intros.
      rewrite in_app_iff in *.
      destruct H1; [eapply HDisjRegs; eauto| ].
      rewrite DisjKeyWeak_same by apply string_dec; intro; intros.
      rewrite in_map_iff in H2; dest; subst.
      pose proof (Substeps_upd_In H0 _ (in_map fst _ _ H1) _ (in_map fst _ _ H4)).
      apply (SubList_map fst) in HUpdGood.
      rewrite ?map_map in *; simpl in *.
      rewrite ?(functional_extensionality (fun x => fst x) fst) in HUpdGood by tauto.
      setoid_rewrite (functional_extensionality (fun x => fst x) fst) in HUpdGood; [|tauto].
      specialize (HUpdGood _ H3).
      clear - H2 DisjRegs HUpdGood; firstorder fail.
    + intros.
      rewrite in_app_iff in *.
      destruct H1; [eapply HNoRle; eauto| ].
      unfold SubList in *.
      specialize (HOneRle _ x (or_introl eq_refl) H1); simpl in *; assumption.
  - subst; simpl.
    assert (sth_else: forall x1 x2, In x1 ls -> In x2 l2 -> match fst (snd x1), fst (snd x2) with
                                                            | Rle _, Rle _ => False
                                                            | _, _ => True
                                                            end) by (clear - HOneRle; firstorder fail).
    econstructor 3; eauto; simpl; rewrite ?map_app; try congruence.
    + inv H0; congruence.
    + rewrite in_app_iff; left; eassumption.
    + pose proof (SemActionReadsSub HAction).
      pose proof (SemActionUpdSub HAction).
      eapply SemActionExpandRegs; eauto; unfold SubList in *; intros; rewrite ?map_app, ?in_app_iff; left.
      * eapply H1; eauto.
      * eapply H2; eauto.
    + unfold SubList in *; intros.
      rewrite in_app_iff; left; eapply HReadsGood; eauto.
    + unfold SubList in *; intros.
      rewrite in_app_iff; left; eapply HUpdGood; eauto.
    + intros.
      rewrite in_app_iff in *.
      destruct H1; [eapply HDisjRegs; eauto| ].
      rewrite DisjKeyWeak_same by apply string_dec; intro; intros.
      rewrite in_map_iff in H2; dest; subst.
      pose proof (Substeps_upd_In H0 _ (in_map fst _ _ H1) _ (in_map fst _ _ H4)).
      apply (SubList_map fst) in HUpdGood.
      rewrite ?map_map in *; simpl in *.
      rewrite ?(functional_extensionality (fun x => fst x) fst) in HUpdGood by tauto.
      setoid_rewrite (functional_extensionality (fun x => fst x) fst) in HUpdGood; [|tauto].
      specialize (HUpdGood _ H3).
      clear - H2 DisjRegs HUpdGood; firstorder fail.
Qed.

Lemma Substeps_flatten m o l:
  Substeps (BaseMod (getRegisters m) (getRules m) (getMethods m)) o l ->
  Substeps m o l.
Proof.
  induction 1; simpl; auto.
  - constructor 1; auto.
  - econstructor 2; eauto.
  - econstructor 3; eauto.
Qed.

Lemma flatten_Substeps m o l:
  Substeps m o l -> Substeps (BaseMod (getRegisters m) (getRules m) (getMethods m)) o l.
  induction 1; simpl; auto.
  - constructor 1; auto.
  - econstructor 2; eauto.
  - econstructor 3; eauto.
Qed.

Lemma Step_substitute' m o l:
  Step m o l -> forall (HWfMod: WfMod m), StepSubstitute m o l.
Proof.
  unfold StepSubstitute.
  induction 1; auto; simpl; intros; dest; unfold MatchingExecCalls_Base in *; simpl in *.
  - repeat split.
    clear HMatching.
    induction HSubsteps.
    + econstructor 1; eauto.
    + econstructor 2; eauto.
    + econstructor 3; eauto.
    + simpl; tauto.
    + intros; tauto.
  - inv HWfMod.
    specialize (IHStep HWf); dest.
    repeat split; auto.
    intros; destruct H4.
    + subst.
      apply HHidden; auto.
    + apply H2; auto.
  - inv HWfMod.
    specialize (IHStep1 HWf1).
    specialize (IHStep2 HWf2).
    dest.
    subst; repeat split; auto.
    + pose proof (Substeps_combine H4 HDisjRegs HDisjMeths HNoRle H1 (m2 := BaseMod (getAllRegisters m2) _ _)).
      simpl in *.
      assumption.
    + intros.
      rewrite getNumCalls_app, getNumExecs_app.
      rewrite map_app, in_app_iff in H7.
      destruct H7.
      * destruct (Z.eq_dec (getNumCalls f l2) 0%Z).
        -- rewrite e.
           specialize (H5 _ H7).
           specialize (getNumExecs_nonneg f l2); intros.
           Omega.omega.
        -- destruct  (HMatching2 f n H7).
           assert (getNumExecs f l2 = 0%Z) as P1;
             [destruct (HDisjMeths (fst f));[contradiction|];
              eapply NotInDef_ZeroExecs_Substeps; eauto; simpl; assumption|].
           Omega.omega.
      * destruct (Z.eq_dec (getNumCalls f l1) 0%Z).
        -- rewrite e.
           specialize (H2 _ H7).
           specialize (getNumExecs_nonneg f l1); intros.
           Omega.omega.
        -- destruct  (HMatching1 f n H7).
           assert (getNumExecs f l1 = 0%Z) as P1;
             [destruct (HDisjMeths (fst f));[|contradiction];
              eapply NotInDef_ZeroExecs_Substeps; eauto; simpl; assumption|].
           Omega.omega.
    + intros s v.
      rewrite map_app;repeat rewrite in_app_iff.
      unfold getListFullLabel_diff in *.
      rewrite getNumExecs_app, getNumCalls_app.
      intros.
      destruct H7, H8, (HDisjMeths s); try tauto.
      * assert (getNumExecs (s, v) l2 = 0%Z) as P1;
          [eapply NotInDef_ZeroExecs_Substeps; eauto; simpl; assumption|].
        destruct (Z.eq_dec (getNumCalls (s, v) l2) 0%Z);
          [specialize (H6 _ v H7 H8);Omega.omega|].
        destruct (HMatching2 _ n H7); contradiction.
      * pose proof (WfMod_Hidden HWf2 _ H8); contradiction.
      * pose proof (WfMod_Hidden HWf1 _ H8); contradiction.
      * assert (getNumExecs (s, v) l1 = 0%Z) as P1;
          [eapply NotInDef_ZeroExecs_Substeps; eauto; simpl; assumption|].
        destruct (Z.eq_dec (getNumCalls (s, v) l1) 0%Z);
          [specialize (H3 _ v H7 H8);Omega.omega|].
        destruct (HMatching1 _ n H7); contradiction.
Qed.

Lemma StepSubstitute_flatten m o l (HWfMod: WfMod m):
  Step (flatten m) o l <-> StepSubstitute m o l.
Proof.
  unfold flatten, getFlat, StepSubstitute.
  split; intros.
  - induction (getHidden m).
    + simpl in *.
      inv H.
      split; [auto| split; [auto| intros; tauto]].
    + simpl in *.
      inv H.
      specialize (IHl0 HStep); dest.
      split; [auto| split; [auto| intros]].
      rewrite createHide_Meths in *; simpl in *.
      destruct H3; [subst |clear - H1 H2 H3; firstorder fail].
      firstorder fail.
  - induction (getHidden m); simpl; auto; dest.
    + constructor; auto.
    + assert (sth: Step (createHide (BaseMod (getAllRegisters m) (getAllRules m) (getAllMethods m)) l0) o l) by firstorder fail.
      assert (sth2: forall v, In a (map fst (getAllMethods m)) -> (getListFullLabel_diff (a, v) l = 0%Z)) by firstorder fail.
      constructor; auto.
      rewrite createHide_Meths; auto.
Qed.
    
Lemma Step_substitute m o l (HWfMod: WfMod m):
  Step m o l -> Step (flatten m) o l.
Proof.
  intros Stp.
  apply (@Step_substitute') in Stp; auto.
  rewrite (@StepSubstitute_flatten) in *; auto.
Qed.

Lemma splitRegs o m1 m2 (DisjRegisters: DisjKey (getRegisters m1) (getRegisters m2)):
  getKindAttr o = getKindAttr (getRegisters m1 ++ getRegisters m2) ->
  getKindAttr (filter (fun x : string * {x : FullKind & fullType type x} => getBool (in_dec string_dec (fst x) (map fst (getRegisters m1)))) o) = getKindAttr (getRegisters m1).
Proof.
  intros HRegs.
  rewrite map_app in *.
  pose proof (filter_map_simple (fun x: string * {x: FullKind & fullType type x} => (fst x, projT1 (snd x)))
                                (fun x => getBool (in_dec string_dec (fst x) (map fst (getRegisters m1)))) o) as sth.
  simpl in sth.
  setoid_rewrite <- sth.
  setoid_rewrite HRegs.
  rewrite filter_app.
  setoid_rewrite filter_false_list at 2.
  - rewrite filter_true_list at 1.
    + rewrite app_nil_r; auto.
    + intros.
      apply (in_map fst) in H.
      rewrite map_map in H.
      simpl in *.
      setoid_rewrite (functional_extensionality (fun x => fst x) fst) in H; try tauto.
      destruct (in_dec string_dec (fst a) (map fst (getRegisters m1))); auto.
  - intros.
    apply (in_map fst) in H.
    rewrite map_map in H.
    simpl in *.
    setoid_rewrite (functional_extensionality (fun x => fst x) fst) in H; try tauto.
    destruct (in_dec string_dec (fst a) (map fst (getRegisters m1))); auto.
    specialize (DisjRegisters (fst a)).
    tauto.
Qed.

Definition strcmp (s1 s2 : string) : bool := if (string_dec s1 s2) then true else false.
Definition BaseModuleFilter (m : BaseModule)(fl : FullLabel) : bool :=
  match getRleOrMeth fl with
  | Rle rn => existsb (strcmp rn) (map fst (getRules m))
  | Meth f => existsb (strcmp (fst f)) (map fst (getMethods m))
  end.
Definition ModuleFilterLabels (m : BaseModule)(l : list FullLabel) : list FullLabel := filter (BaseModuleFilter m) l.

Lemma InRules_Filter : forall (u : RegsT)(rn : string)(rb : Action Void)(l : list FullLabel)(cs : MethsT)(m1 : BaseModule),
    In (rn, rb) (getRules m1) -> ModuleFilterLabels m1 ((u, (Rle rn, cs))::l) = ((u, (Rle rn, cs))::ModuleFilterLabels m1 l).
Proof.
  intros. unfold ModuleFilterLabels, BaseModuleFilter. simpl.
  generalize (existsb_exists (strcmp rn) (map fst (getRules m1))).
  destruct (existsb (strcmp rn) (map fst (getRules m1))); intro;[reflexivity | destruct H0; clear H0].
  assert (false=true);[apply H1; exists rn; split| discriminate].
  - apply in_map_iff; exists (rn, rb); auto.
  - unfold strcmp;destruct (string_dec rn rn);[reflexivity|contradiction].
Qed.

Lemma NotInRules_Filter : forall (u : RegsT)(rn : string)(l : list FullLabel)(cs : MethsT)(m1 : BaseModule),
    ~In rn (map fst (getRules m1)) ->  ModuleFilterLabels m1 ((u, (Rle rn, cs))::l) = ModuleFilterLabels m1 l.
Proof.
  intros. unfold ModuleFilterLabels, BaseModuleFilter. simpl.
  generalize (existsb_exists (strcmp rn) (map fst (getRules m1))).
  destruct (existsb (strcmp rn) (map fst (getRules m1))); intro H0; destruct H0;[|reflexivity].
  apply False_ind; apply H.
  assert (true=true) as TMP;[reflexivity|specialize (H0 TMP); dest].
  unfold strcmp in H2; destruct (string_dec rn x); subst;[assumption|discriminate].
Qed.

Lemma InMethods_Filter : forall (u : RegsT)(fn : string)(fb : {x : Signature & MethodT x})
                                (argV : type (fst (projT1 fb)))(retV : type (snd (projT1 fb)))
                                (l : list FullLabel)(cs : MethsT)(m1 : BaseModule),
    In (fn, fb) (getMethods m1) ->
    ModuleFilterLabels m1 ((u, (Meth (fn, existT SignT (projT1 fb) (argV, retV)), cs))::l) = ((u, (Meth (fn, existT SignT (projT1 fb) (argV, retV)), cs)):: ModuleFilterLabels m1 l).
Proof.
  intros. unfold ModuleFilterLabels, BaseModuleFilter. simpl.
  generalize (existsb_exists (strcmp fn) (map fst (getMethods m1))).
  destruct (existsb (strcmp fn) (map fst (getMethods m1))); intro;[reflexivity | destruct H0; clear H0].
  assert (false=true);[apply H1; exists fn; split| discriminate].
  - apply in_map_iff; exists (fn, fb); auto.
  - unfold strcmp;destruct (string_dec fn fn);[reflexivity|contradiction].
Qed.

Lemma NotInMethods_Filter : forall  (u : RegsT)(fn : string)(fb : {x : Signature & MethodT x})
                                  (argV : type (fst (projT1 fb)))(retV : type (snd (projT1 fb)))
                                  (l : list FullLabel)(cs : MethsT)(m1 : BaseModule),
    ~In fn (map fst (getMethods m1)) -> ModuleFilterLabels m1 ((u, (Meth (fn, existT SignT (projT1 fb) (argV, retV)), cs))::l) = ModuleFilterLabels m1 l.
Proof.
  intros. unfold ModuleFilterLabels, BaseModuleFilter. simpl.
  generalize (existsb_exists (strcmp fn) (map fst (getMethods m1))).
  destruct (existsb (strcmp fn) (map fst (getMethods m1))); intro H0; destruct H0;[|reflexivity].
  apply False_ind; apply H.
  assert (true=true) as TMP;[reflexivity|specialize (H0 TMP); dest].
  unfold strcmp in H2; destruct (string_dec fn x); subst;[assumption|discriminate].
Qed.

Lemma InCall_split_InCall f l m1 :
  InCall f (ModuleFilterLabels m1 l) -> InCall f l.
Proof.
  unfold InCall, ModuleFilterLabels.
  intros; dest.
  generalize (filter_In (BaseModuleFilter m1) x l) as TMP; intro; destruct TMP as [L R];clear R; apply L in H; destruct H.
  exists x; split; assumption.
Qed.

Lemma InExec_split_InExec f l m1 :
  InExec f (ModuleFilterLabels m1 l) -> InExec f l.
Proof.
  unfold InExec, ModuleFilterLabels.
  intros.
  apply in_map_iff; apply in_map_iff in H;dest.
  exists x; split;[assumption|].
  generalize (filter_In (BaseModuleFilter m1) x l) as TMP; intro; destruct TMP as [L R]; clear R; apply L in H0; destruct H0.
  assumption.
Qed.

Lemma InCall_perm l l' f :
  InCall f l -> Permutation l l' -> InCall f l'.
  induction 2. assumption.
  - apply (InCall_app_iff f (x::nil) l').
    apply (InCall_app_iff f (x::nil) l) in H.
    destruct H;[left|right; apply IHPermutation];assumption.
  - apply (InCall_app_iff f (x::y::nil) l).
    apply (InCall_app_iff f (y::x::nil) l) in H.
    destruct H;[left;apply (InCall_app_iff f (x::nil) (y::nil)) | right];[apply (InCall_app_iff f (y::nil) (x::nil)) in H; destruct H;[right|left]|];assumption.
  - apply (IHPermutation2 (IHPermutation1 H)).
Qed.

Lemma InExec_perm l l' f :
  InExec f l -> Permutation l l' -> InExec f l'.
  induction 2. assumption.
  - apply (InExec_app_iff f (x::nil) l').
    apply (InExec_app_iff f (x::nil) l) in H.
    destruct H;[left|right; apply IHPermutation];assumption.
  - apply (InExec_app_iff f (x::y::nil) l).
    apply (InExec_app_iff f (y::x::nil) l) in H.
    destruct H;[left;apply (InExec_app_iff f (x::nil) (y::nil)) | right];[apply (InExec_app_iff f (y::nil) (x::nil)) in H; destruct H;[right|left]|];assumption.
  - apply (IHPermutation2 (IHPermutation1 H)).
Qed.

Lemma MatchingExecCalls_Base_perm_rewrite l1 l2 m1 :
  l1 [=] l2 -> MatchingExecCalls_Base l1 m1 -> MatchingExecCalls_Base l2 m1.
Proof.
  intros HPerm HMec1 f HInDef.
  specialize (HMec1 f HInDef).
  repeat rewrite <-HPerm.
  assumption.
Qed.

Global Instance MatchingExecCalls_Base_perm_rewrite' :
  Proper (@Permutation FullLabel ==> eq ==> iff) (@MatchingExecCalls_Base) | 10.
Proof.
  repeat red; split; intros; subst; eauto using MatchingExecCalls_Base_perm_rewrite, Permutation_sym.
Qed.

Lemma MatchingExecCalls_Concat_perm1 l1 l2 l3 m1 :
  l1 [=] l2 -> MatchingExecCalls_Concat l1 l3 m1 -> MatchingExecCalls_Concat l2 l3 m1.
Proof.
  unfold MatchingExecCalls_Concat.
  intros.
  rewrite <-H.
  apply H0; auto.
  rewrite H; assumption.
Qed.

Lemma MatchingExecCalls_Concat_perm2 l1 l2 l3 m1 :
  l1 [=] l2 -> MatchingExecCalls_Concat l3 l1 m1 -> MatchingExecCalls_Concat l3 l2 m1.
Proof.
  unfold MatchingExecCalls_Concat.
  intros.
  rewrite <- H.
  apply H0; auto.
Qed.

Corollary MatchingExecCalls_Concat_rewrite l1 l2 l3 l4 m :
  l1 [=] l2 -> l3 [=] l4 -> MatchingExecCalls_Concat l1 l3 m -> MatchingExecCalls_Concat l2 l4 m.
Proof.
  eauto using MatchingExecCalls_Concat_perm1, MatchingExecCalls_Concat_perm2.
Qed.

Global Instance MatchingExecCalls_Concat_rewrite' :
  Proper (@Permutation FullLabel ==> @Permutation FullLabel ==> eq ==> iff) (@MatchingExecCalls_Concat) | 10.
Proof.
  repeat red; intros; split; intro; subst; eauto using MatchingExecCalls_Concat_rewrite, Permutation_sym.
Qed.

Lemma InExec_ModuleFilterLabels : forall (f : MethT)(m : BaseModule)(l : list FullLabel),
    In (fst f) (map fst (getMethods m)) ->
    (getNumExecs f l = getNumExecs f (ModuleFilterLabels m l)).
Proof.
  Opaque getNumFromExecs.
  intros.
  assert (existsb (strcmp (fst f)) (map fst (getMethods m)) = true);[apply (existsb_exists (strcmp (fst f))(map fst (getMethods m)));exists (fst f);split;
                                                                     [assumption|unfold strcmp; destruct (string_dec(fst f)(fst f));[reflexivity|contradiction]]|].
  induction l; auto.
  - destruct a, p, r0.
    + unfold ModuleFilterLabels, BaseModuleFilter, getNumExecs in *; simpl.
      destruct (existsb (strcmp rn) (map fst (getRules m))); simpl;
        rewrite getNumFromExecs_Rle_cons; assumption.
    + unfold ModuleFilterLabels, BaseModuleFilter, getNumExecs in *; simpl.
      destruct (MethT_dec f f0); subst;
        [rewrite H0; simpl; repeat rewrite getNumFromExecs_eq_cons; auto; rewrite IHl; reflexivity|].
      destruct (existsb (strcmp (fst f0)) (map fst (getMethods m)));
        simpl; repeat rewrite getNumFromExecs_neq_cons; auto.
  Transparent getNumFromExecs.
Qed.

Lemma getNumExecs_le_length (f : MethT) (l : list FullLabel) :
  (getNumExecs f l <= Zlength l)%Z.
Proof.
  Opaque getNumFromExecs.
  induction l.
  - reflexivity.
  - destruct a, p, r0; unfold getNumExecs in *;simpl.
    + rewrite getNumFromExecs_Rle_cons, Zlength_cons; Omega.omega.
    + destruct (MethT_dec f f0); simpl in *;[rewrite getNumFromExecs_eq_cons|rewrite getNumFromExecs_neq_cons];auto; rewrite Zlength_cons; Omega.omega.
  Transparent getNumFromExecs.
Qed.

Lemma getNumFromCalls_le_length (f : MethT) (l : MethsT):
  (getNumFromCalls f l <= Zlength l)%Z.
Proof.
  induction l.
  - reflexivity.
  - destruct (MethT_dec f a);[rewrite getNumFromCalls_eq_cons|rewrite getNumFromCalls_neq_cons]; auto; rewrite Zlength_cons; Omega.omega.
Qed.

Lemma filter_reduces_calls (f : MethT) (g : FullLabel -> bool) (l : list FullLabel) :
  (getNumCalls f (filter g l) <= getNumCalls f l)%Z.
Proof.
  induction l; simpl.
  - reflexivity.
  - specialize (getNumFromCalls_nonneg f (snd (snd a))) as P1.
    destruct (g a); repeat rewrite getNumCalls_cons; Omega.omega.
Qed.

Lemma filter_reduces_execs (f : MethT) (g : FullLabel -> bool) (l : list FullLabel) :
  (getNumExecs f (filter g l) <= getNumExecs f l)%Z.
Proof.
  Opaque getNumFromExecs.
  induction l; simpl.
  - reflexivity.
  - destruct (g a), a, p, r0; unfold getNumExecs in *; simpl in *.
    + repeat rewrite getNumFromExecs_Rle_cons; assumption.
    + destruct (MethT_dec f f0);[repeat rewrite getNumFromExecs_eq_cons|repeat rewrite getNumFromExecs_neq_cons];auto;Omega.omega.
    + rewrite getNumFromExecs_Rle_cons; assumption.
    + destruct (MethT_dec f f0);[rewrite getNumFromExecs_eq_cons|rewrite getNumFromExecs_neq_cons];auto;Omega.omega.
  Transparent getNumFromExecs.
Qed.

Lemma MatchingExecCalls_Split (l : list FullLabel) (m1 m2 : BaseModule) :
    MatchingExecCalls_Base l (concatFlat m1 m2) ->
    MatchingExecCalls_Base (ModuleFilterLabels m1 l) m1.
Proof.
  intros Mec1 f HDef.
  specialize (Mec1 f); simpl in *.
  rewrite map_app, in_app_iff in *.
  specialize (Mec1 (or_introl _ HDef)).
  unfold ModuleFilterLabels.
  specialize (filter_reduces_calls f (BaseModuleFilter m1) l) as P1.
  fold ((ModuleFilterLabels m1) l).
  rewrite <-InExec_ModuleFilterLabels; auto.
  eauto using Z.le_trans.
Qed.

Lemma MatchingExecCalls_Split2 (l : list FullLabel) (m1 m2 : BaseModule) :
    MatchingExecCalls_Base l (concatFlat m1 m2) ->
    MatchingExecCalls_Base (ModuleFilterLabels m2 l) m2.
Proof.
  intros Mec1 f HDef.
  specialize (Mec1 f); simpl in *.
  rewrite map_app, in_app_iff in *.
  specialize (Mec1 (or_intror _ HDef)).
  unfold ModuleFilterLabels.
  specialize (filter_reduces_calls f (BaseModuleFilter m2) l) as P1.
  fold ((ModuleFilterLabels m2) l).
  rewrite <-InExec_ModuleFilterLabels; auto.
  eauto using Z.le_trans.
Qed.

Lemma MatchingExecCalls_Concat_comm : forall (l l' : list FullLabel) (m1 m2 : BaseModule),
    MatchingExecCalls_Concat l l' (Base (concatFlat m1 m2)) -> MatchingExecCalls_Concat l l' (Base (concatFlat m2 m1)).
Proof.
  repeat intro.
  specialize (H f H0).
  simpl in *. apply H.
  rewrite (map_app) in *; apply in_app_iff; apply in_app_iff in H1.
  firstorder fail.
Qed.

Lemma MatchingExecCalls_Base_comm : forall (l : list FullLabel) (m1 m2 : BaseModule),
    MatchingExecCalls_Base l (concatFlat m1 m2) -> MatchingExecCalls_Base l (concatFlat m2 m1).
Proof.
  repeat intro.
  specialize (H f).
  simpl in *; apply H; auto.
  rewrite map_app, in_app_iff in *; firstorder fail.
Qed.

Lemma Kind_Kind_dec: forall k1 k2: Kind * Kind, {k1 = k2} + {k1 <> k2}.
Proof.
  decide equality; subst;
    apply Kind_dec.
Qed.

Lemma WfActionT_ReadsWellDefined : forall (k : Kind)(a : ActionT type k)(retl : type k)
                                          (m1 : BaseModule)(o readRegs newRegs : RegsT)(calls : MethsT),
    WfActionT m1 a ->
    SemAction o a readRegs newRegs calls retl ->
    SubList (getKindAttr readRegs) (getKindAttr (getRegisters m1)).
Proof.
  induction 2; intros; subst; inversion H; EqDep_subst; auto.
  - rewrite map_app. repeat intro. apply in_app_iff in H0; destruct H0.
    + apply (IHSemAction1 H3 _ H0).
    + apply (IHSemAction2 (H5 v) _ H0).
  - inversion H; EqDep_subst. repeat intro. destruct H1;[subst;assumption|apply IHSemAction; auto].
  - rewrite map_app; repeat intro. apply in_app_iff in H0; destruct H0.
    + apply (IHSemAction1 H7 _ H0).
    + apply (IHSemAction2 (H4 r1) _ H0).
  - inversion H; EqDep_subst. rewrite map_app; repeat intro. apply in_app_iff in H0; destruct H0.
    + apply (IHSemAction1 H8 _ H0).
    + apply (IHSemAction2 (H4 r1) _ H0).
  - repeat intro; auto. contradiction.
Qed.

Lemma WfActionT_WritesWellDefined : forall (k : Kind)(a : ActionT type k)(retl : type k)
                                           (m1 : BaseModule)(o readRegs newRegs : RegsT)(calls : MethsT),
    WfActionT m1 a ->
    SemAction o a readRegs newRegs calls retl ->
    SubList (getKindAttr newRegs) (getKindAttr (getRegisters m1)).
Proof.
  induction 2; intros; subst; inversion H; EqDep_subst; auto.
  - rewrite map_app. repeat intro. apply in_app_iff in H0; destruct H0.
    + apply (IHSemAction1 H3 _ H0).
    + apply (IHSemAction2 (H5 v) _ H0).
  - inversion H; EqDep_subst. repeat intro. destruct H1;[subst;assumption|apply IHSemAction; auto].
  - rewrite map_app; repeat intro. apply in_app_iff in H0; destruct H0.
    + apply (IHSemAction1 H7 _ H0).
    + apply (IHSemAction2 (H4 r1) _ H0).
  - inversion H; EqDep_subst. rewrite map_app; repeat intro. apply in_app_iff in H0; destruct H0.
    + apply (IHSemAction1 H8 _ H0).
    + apply (IHSemAction2 (H4 r1) _ H0).
  - repeat intro; auto. contradiction.
Qed.

Lemma KeyMatching : forall (l : RegsT) (a b : string * {x : FullKind & fullType type x}),
    NoDup (map fst l) -> In a l -> In b l -> fst a = fst b -> a = b.
Proof.
  induction l; intros.
  - inversion H0.
  - destruct H0; destruct H1.
    + symmetry; rewrite <- H1; assumption.
    + rewrite (map_cons fst) in H.
      inversion H; subst.
      apply (in_map fst l b) in H1.
      apply False_ind. apply H5.
      destruct a0; destruct b; simpl in *.
      rewrite H2; assumption.
    + rewrite (map_cons fst) in H.
      inversion H; subst.
      apply (in_map fst l a0) in H0.
      apply False_ind; apply H5.
      destruct a0, b; simpl in *.
      rewrite <- H2; assumption.
    + inversion H; subst.
      apply IHl; auto.
Qed.

Lemma KeyRefinement : forall (l l' : RegsT) (a : string * {x: FullKind & fullType type x}),
    NoDup (map fst l) -> SubList l' l -> In a l -> In (fst a) (map fst l') -> In a l'.
Proof.
  induction l'; intros; inversion H2; subst.
  - assert (In a (a::l')) as TMP;[left; reflexivity|specialize (H0 _ TMP); rewrite (KeyMatching _ _ _ H H0 H1 H3); left; reflexivity].
  - right; apply IHl'; auto.
    repeat intro.
    apply (H0 x (or_intror _ H4)).
Qed.

Lemma GKA_fst : forall (A B : Type)(P : B -> Type)(o : list (A * {x : B & P x})),
    (map fst o) = (map fst (getKindAttr o)).
Proof.
  induction o; simpl.
  - reflexivity.
  - rewrite IHo.
    reflexivity.
Qed.

Lemma NoDupKey_Expand : forall (A B : Type)(l1 l2 : list (A * B)),
    NoDup (map fst l1) ->
    NoDup (map fst l2) ->
    DisjKey l1 l2 ->
    NoDup (map fst (l1++l2)).
Proof.
  intros; rewrite (map_app fst).
  induction l1; auto.
  inversion_clear H.
  destruct (H1 (fst a)).
  - apply False_ind. apply H; left; reflexivity.
  - assert (~(In (fst a) ((map fst l1)++(map fst l2)))).
    + intro in_app12; apply in_app_iff in in_app12; destruct in_app12;[apply H2|apply H]; assumption.
    + assert (DisjKey l1 l2); repeat intro.
      * destruct (H1 k);[left|right];intro; apply H5;simpl;auto.
      * apply (NoDup_cons (fst a) (l:=(map fst l1 ++ map fst l2)) H4 (IHl1 H3 H5)).
Qed.

Lemma WfActionT_SemAction : forall (k : Kind)(a : ActionT type k)(retl : type k)
                                   (m1 : BaseModule)(o readRegs newRegs : RegsT)(calls : MethsT),
    WfActionT m1 a ->
    NoDup (map fst o) ->
    SemAction o a readRegs newRegs calls retl ->
    (forall (o1 : RegsT),
        SubList o1 o ->
        getKindAttr o1 = getKindAttr (getRegisters m1) ->
        SemAction o1 a readRegs newRegs calls retl).
  induction 3; intro; subst; inversion H; EqDep_subst.
  - intros TMP1 TMP2; specialize (IHSemAction (H4 mret) o1 TMP1 TMP2).
    econstructor 1; eauto.
  - intros TMP1 TMP2; specialize (IHSemAction (H4 (evalExpr e)) o1 TMP1 TMP2).
    econstructor 2; eauto.
  - intros TMP1 TMP2; specialize (IHSemAction1 (H4) o1 TMP1 TMP2); specialize (IHSemAction2 (H6 v) o1 TMP1 TMP2).
    econstructor 3; eauto.
  - intros TMP1 TMP2; specialize (IHSemAction (H4 valueV) o1 TMP1 TMP2).
    econstructor 4; eauto.
  - intros TMP1 TMP2; specialize (IHSemAction (H5 regV) o1 TMP1 TMP2).
    econstructor 5; eauto.
    apply (KeyRefinement (r, existT (fullType type) regT regV) H0 TMP1 HRegVal).
    rewrite <- TMP2 in H7; apply (in_map fst) in H7; specialize (GKA_fst (A:=string)(fullType type) o1); intro.
    simpl in *.
    setoid_rewrite H2; assumption.
  - intros TMP1 TMP2; specialize (IHSemAction H5 o1 TMP1 TMP2).
    econstructor 6; eauto.
    rewrite TMP2; assumption.
  - intros TMP1 TMP2; specialize (IHSemAction1 H8 o1 TMP1 TMP2); specialize (IHSemAction2 (H5 r1) o1 TMP1 TMP2).
    econstructor 7; eauto.
  - intros TMP1 TMP2; specialize (IHSemAction1 H9 o1 TMP1 TMP2); specialize (IHSemAction2 (H5 r1) o1 TMP1 TMP2).
    econstructor 8; eauto.
  - intros TMP1 TMP2; specialize (IHSemAction H4 o1 TMP1 TMP2).
    econstructor 9; eauto.
  - intros; econstructor 10; eauto.
Qed.

Lemma app_sublist_l : forall {A : Type} (l1 l2 l : list A),
    l = l1++l2 -> SubList l1 l.
Proof.
  repeat intro.
  rewrite H.
  apply (in_app_iff l1 l2 x); left; assumption.
Qed.

Lemma app_sublist_r : forall {A : Type} (l1 l2 l : list A),
    l = l1++l2 -> SubList l2 l.
Proof.
  repeat intro.
  rewrite H.
  apply (in_app_iff l1 l2 x); right; assumption.
Qed.

Section SplitSubsteps.
  Variable m1 m2: BaseModule.
  Variable DisjRegs: DisjKey (getRegisters m1) (getRegisters m2).
  Variable DisjRules: DisjKey (getRules m1) (getRules m2).
  Variable DisjMeths: DisjKey (getMethods m1) (getMethods m2).

  Variable WfMod1: WfBaseModule m1.
  Variable WfMod2: WfBaseModule m2.
  
  Lemma filter_perm o l :
    Substeps (concatFlat m1 m2) o l ->
    Permutation l ((ModuleFilterLabels m1 l)++(ModuleFilterLabels m2 l)).
    induction 1; subst.
    - simpl; apply Permutation_refl.
    - apply in_app_iff in HInRules.
      destruct HInRules as [HInRules | HInRules]; rewrite (InRules_Filter _ _ _ _ _ _ HInRules).
      + destruct (DisjRules rn).
        * generalize (in_map_iff fst (getRules m1) rn). intro TMP; destruct TMP as [L R];clear L.
          assert (exists x, fst x = rn /\ In x (getRules m1));[exists (rn, rb); auto| specialize (R H1); contradiction].
        * rewrite (NotInRules_Filter _ _ _ _ _ H0).
          constructor. assumption.
      + destruct (DisjRules rn).
        * rewrite (NotInRules_Filter _ _ _ _ _ H0).
          apply (Permutation_cons_app _ _ _ IHSubsteps).
        * generalize (in_map_iff fst (getRules m2) rn). intro TMP; destruct TMP as [L R];clear L.
          assert (exists x, fst x = rn /\ In x (getRules m2));[exists (rn, rb); auto | specialize (R H1); contradiction].
    - apply in_app_iff in HInMeths.
      destruct HInMeths as [HInMeths | HInMeths]; rewrite (InMethods_Filter _ _ _ _ _ _ _ _ HInMeths).
      + destruct (DisjMeths fn).
        * generalize (in_map_iff fst (getMethods m1) fn). intro TMP; destruct TMP as [L R]; clear L.
          assert (exists x, fst x = fn /\ In x (getMethods m1)); [exists (fn, fb); auto| specialize (R H1); contradiction].
        * rewrite (NotInMethods_Filter _ _ _ _ _ _ _ _ H0).
          constructor. assumption.
      + destruct (DisjMeths fn).
        * rewrite (NotInMethods_Filter _ _ _ _ _ _ _ _ H0).
          apply (Permutation_cons_app _ _ _ IHSubsteps).
        * generalize (in_map_iff fst (getMethods m2) fn). intro TMP; destruct TMP as [L R]; clear L.
          assert (exists x, fst x = fn /\ In x (getMethods m2)); [exists (fn, fb); auto| specialize (R H1); contradiction].
  Qed.


  Lemma MatchingExecCalls_Mix2 : forall (l : list FullLabel) (o : RegsT),
      Substeps (concatFlat m1 m2) o l ->
      MatchingExecCalls_Base l (concatFlat m1 m2) ->
      MatchingExecCalls_Concat (ModuleFilterLabels m1 l) (ModuleFilterLabels m2 l) (Base m2).
  Proof.
    repeat intro. split;[auto|].
    rewrite <- getNumCalls_app.
    rewrite <- (filter_perm H).
    specialize (H0 f); simpl in *;rewrite map_app, in_app_iff in H0.
    specialize (H0 (or_intror _ H2)).
    rewrite <-InExec_ModuleFilterLabels; auto.
  Qed.


  Lemma MatchingExecCalls_Mix1 : forall (l : list FullLabel) (o : RegsT),
      Substeps (concatFlat m1 m2) o l ->
      MatchingExecCalls_Base l (concatFlat m1 m2) ->
      MatchingExecCalls_Concat (ModuleFilterLabels m2 l) (ModuleFilterLabels m1 l) (Base m1).
  Proof.
    repeat intro. split;[auto|].
    rewrite Z.add_comm.
    rewrite <- getNumCalls_app.
    rewrite <- (filter_perm H).
    specialize (H0 f); simpl in *;rewrite map_app, in_app_iff in H0.
    specialize (H0 (or_introl _ H2)).
    rewrite <-InExec_ModuleFilterLabels; auto.
  Qed.
  
  Lemma split_Substeps1 o l:
    NoDup (map fst (getRegisters m1)) ->
    NoDup (map fst (getRegisters m2)) ->
    Substeps (concatFlat m1 m2) o l ->
    (exists o1 o2, getKindAttr o1 = getKindAttr (getRegisters m1) /\
                   getKindAttr o2 = getKindAttr (getRegisters m2) /\
                   o = o1++o2 /\
                   Substeps m1 o1 (ModuleFilterLabels m1 l) /\
                   Substeps m2 o2 (ModuleFilterLabels m2 l)).
  Proof.
    unfold concatFlat; induction 3; simpl in *.
    - rewrite map_app in *; apply list_split in HRegs; dest.
      exists x, x0;split;[|split;[|split;[|split;[constructor|constructor]]]];assumption.
    - rewrite map_app in *;apply in_app_iff in HInRules; specialize (DisjRules rn).
      assert (NoDup (map fst o));[setoid_rewrite GKA_fst;setoid_rewrite HRegs; rewrite <- map_app; rewrite <- GKA_fst; apply (NoDupKey_Expand H H0 DisjRegs)|].
      destruct HInRules as [HInRules|HInRules];generalize (in_map fst _ _ HInRules);destruct DisjRules;try contradiction.
      + subst; dest; exists x, x0;split;[|split;[|split;[|split]]];auto.
        rewrite (InRules_Filter _ _ _ _ _ _ HInRules).
        destruct (WfMod1) as [WfMod_Rle1 WfMod_Meth1];destruct (WfMod2) as [WfMod_Rle2 WfMod_Meth2].
        specialize (WfActionT_ReadsWellDefined (WfMod_Rle1 _ HInRules) HAction) as Reads_sublist; specialize (WfActionT_WritesWellDefined (WfMod_Rle1 _ HInRules) HAction) as Writes_sublist.
        constructor 2 with (rn:= rn)(rb:=rb)(reads:=reads)(u:=u)(cs:=cs)(ls:=(ModuleFilterLabels m1 ls)); auto.
        * specialize (app_sublist_l _ _ H6) as SL_o_x.
          specialize (WfMod_Rle1 (rn, rb) HInRules); specialize (WfActionT_SemAction WfMod_Rle1 H2 HAction SL_o_x H4).
          simpl; auto.
        * unfold ModuleFilterLabels;intros;apply HDisjRegs;
            destruct (filter_In (BaseModuleFilter m1) x1 ls) as [L R];
            destruct (L H10);assumption.
        * intros; apply HNoRle;
            destruct (filter_In (BaseModuleFilter m1) x1 ls) as [L R];
            destruct (L H10);assumption.
        * rewrite (NotInRules_Filter _ _ _ _ _ H3); assumption.
      + subst; dest; exists x, x0; split;[|split;[|split;[|split]]];auto.
        rewrite (NotInRules_Filter _ _ _ _ _ H3); assumption.
        rewrite (InRules_Filter _ _ _ _ _ _ HInRules).
        destruct (WfMod1) as [WfMod_Rle1 WfMod_Meth1];destruct (WfMod2) as [WfMod_Rle2 WfMod_Meth2]; specialize (WfActionT_ReadsWellDefined (WfMod_Rle2 _ HInRules) HAction) as Reads_sublist; specialize (WfActionT_WritesWellDefined (WfMod_Rle2 _ HInRules) HAction) as Writes_sublist.
        constructor 2 with (rn:= rn)(rb:=rb)(reads:=reads)(u:=u)(cs:=cs)(ls:=(ModuleFilterLabels m2 ls)); auto.
        * specialize (app_sublist_r _ _ H6) as SL_o_x.
          specialize (WfMod_Rle2 (rn, rb) HInRules); specialize (WfActionT_SemAction WfMod_Rle2 H2 HAction SL_o_x H5).
          simpl; auto.
        * unfold ModuleFilterLabels;intros;apply HDisjRegs;
            destruct (filter_In (BaseModuleFilter m2) x1 ls) as [L R];
            destruct (L H10);assumption.
        * intros; apply HNoRle;
            destruct (filter_In (BaseModuleFilter m2) x1 ls) as [L R];
            destruct (L H10);assumption.
    - rewrite map_app in *;apply in_app_iff in HInMeths; specialize (DisjMeths fn).
      assert (NoDup (map fst o));[setoid_rewrite GKA_fst;setoid_rewrite HRegs; rewrite <- map_app; rewrite <- GKA_fst; apply (NoDupKey_Expand H H0 DisjRegs)|].
      destruct HInMeths as [HInMeths|HInMeths];generalize (in_map fst _ _ HInMeths);destruct DisjMeths;try contradiction;intros.
      + subst; dest; exists x, x0;split;[|split;[|split;[|split]]];auto.
        * rewrite (InMethods_Filter _ _ _ _ _ _ _ _ HInMeths).
          destruct (WfMod1) as [WfMod_Rle1 [WfMod_Meth1 _]];destruct (WfMod2) as [WfMod_Rle2 [WfMod_Meth2 _]].
          specialize (WfActionT_ReadsWellDefined (WfMod_Meth1 (fn, fb) HInMeths argV) HAction) as Reads_sublist.
          specialize (WfActionT_WritesWellDefined (WfMod_Meth1 (fn, fb) HInMeths argV) HAction) as Writes_sublist.
          constructor 3 with (fn:=fn)(fb:=fb)(reads:=reads)(u:=u)(cs:=cs)(argV:=argV)(retV:=retV)(ls:=(ModuleFilterLabels m1 ls)); auto.
          -- specialize (app_sublist_l _ _ H7) as SL_o_x.
             specialize (WfMod_Meth1 (fn, fb) HInMeths argV); specialize (WfActionT_SemAction WfMod_Meth1 H2 HAction SL_o_x H5).
             simpl; auto.
          -- intros; apply HDisjRegs;
               destruct (filter_In (BaseModuleFilter m1) x1 ls) as [L R];
               destruct (L H10); assumption.
        * rewrite (NotInMethods_Filter _ _ _ _ _ _ _ _ H3); assumption.
      + subst; dest; exists x, x0;split;[|split;[|split;[|split]]]; auto.
        * rewrite (NotInMethods_Filter _ _ _ _ _ _ _ _ H3); assumption.
        * rewrite (InMethods_Filter _ _ _ _ _ _ _ _ HInMeths).
          destruct (WfMod1) as [WfMod_Rle1 [WfMod_Meth1 _]];destruct (WfMod2) as [WfMod_Rle2 [WfMod_Meth2 _]].
          specialize (WfActionT_ReadsWellDefined (WfMod_Meth2 (fn, fb) HInMeths argV) HAction) as Reads_sublist.
          specialize (WfActionT_WritesWellDefined (WfMod_Meth2 (fn, fb) HInMeths argV) HAction) as Writes_sublist.
          constructor 3 with (fn:=fn)(fb:=fb)(reads:=reads)(u:=u)(cs:=cs)(argV:=argV)(retV:=retV)(ls:=(ModuleFilterLabels m2 ls)); auto.
          -- specialize (app_sublist_r _ _ H7) as SL_o_x.
             specialize (WfMod_Meth2 (fn, fb) HInMeths argV); specialize (WfActionT_SemAction WfMod_Meth2 H2 HAction SL_o_x H6).
             simpl; auto.
          -- intros; apply HDisjRegs;
               destruct (filter_In (BaseModuleFilter m2) x1 ls) as [L R];
               destruct (L H10); assumption.
  Qed.
  
  Lemma split_Substeps2 o l:
    Substeps (concatFlat m1 m2) o l ->
      (forall x y : FullLabel,
          In x (ModuleFilterLabels m1 l) ->
          In y (ModuleFilterLabels m2 l) ->
          match fst (snd x) with
          | Rle _ => match fst (snd y) with
                     | Rle _ => False
                     | Meth _ => True
                     end
          | Meth _ => True
          end).
  Proof.
    induction 1; intros; auto; subst.
    - intros; contradiction.
    - simpl in HInRules.
      destruct (in_app_or _ _ _ HInRules) as [Rle_in | Rle_in]; specialize (in_map fst _ _ Rle_in) as map_Rle_in; destruct (DisjRules rn); try contradiction; rewrite (InRules_Filter u _ _ ls cs _ Rle_in) in *;rewrite (NotInRules_Filter u _ ls cs _ H2) in *; intros.
      + destruct H0.
        * rewrite <- H0; simpl.
          apply HNoRle.
          unfold ModuleFilterLabels in H1; apply filter_In in H1; destruct H1; assumption.
        * eapply IHSubsteps; eauto.
      + destruct H1.
        * rewrite <- H1; simpl.
          apply HNoRle.
          unfold ModuleFilterLabels in H0; apply filter_In in H0; destruct H0; assumption.
        * eapply IHSubsteps; eauto.
    - simpl in HInMeths; rewrite in_app_iff in HInMeths; destruct HInMeths, (DisjMeths fn);specialize (in_map fst _ _ H2) as P1 ; try contradiction.
      + setoid_rewrite (NotInMethods_Filter u _ fb argV retV ls cs _ H3) in H1.
        setoid_rewrite (InMethods_Filter _ _ _ _ _ _ _ _ H2) in H0.
        destruct H0;[subst;simpl in *;auto|].
        apply IHSubsteps; auto.
      + setoid_rewrite (NotInMethods_Filter u _ fb argV retV ls cs _ H3) in H0.
        setoid_rewrite (InMethods_Filter _ _ _ _ _ _ _ _ H2) in H1.
        destruct H1;[subst;simpl in *;destruct x,p,r0;simpl;auto|].
        apply IHSubsteps;auto.
  Qed.

End SplitSubsteps.

Definition PWeakInclusion (l1 l2 : list FullLabel) : Prop := 
     (forall f : MethT, InExec f l1 /\ ~ InCall f l1 <-> InExec f l2 /\ ~ InCall f l2) /\
     (forall f : MethT, ~ InExec f l1 /\ InCall f l1 <-> ~ InExec f l2 /\ InCall f l2) /\
     (forall f : MethT, InExec f l1 /\ InCall f l1 \/ (forall v, ~ InExec (fst f, v) l1 ) /\ (forall v, ~ InCall (fst f, v) l1) <-> InExec f l2 /\ InCall f l2 \/ (forall v, ~ InExec (fst f, v) l2) /\ (forall v, ~ InCall (fst f, v) l2))
     /\ ((exists rle : string, In (Rle rle) (map getRleOrMeth l2)) -> exists rle : string, In (Rle rle) (map getRleOrMeth l1)).


Lemma InExec_app_comm : forall l1 l2 e, InExec e (l1++l2) -> InExec e (l2++l1).
Proof.
  intros.
  apply InExec_app_iff.
  apply InExec_app_iff in H.
  firstorder.
Qed.

Lemma InCall_app_comm : forall l1 l2 e, InCall e (l1++l2) -> InCall e (l2++l1).
Proof.
  intros.
  apply InCall_app_iff.
  apply InCall_app_iff in H.
  firstorder.
Qed.

Lemma WeakInclusion_app_comm : forall l1 l2, WeakInclusion (l1++l2)(l2++l1).
Proof.
  intros.
  unfold WeakInclusion;split;intros.
  - unfold getListFullLabel_diff; repeat rewrite getNumExecs_app, getNumCalls_app; ring.
  - dest; exists x; rewrite map_app,in_app_iff in *; firstorder fail.
Qed.

Definition WeakEquality (l1 l2 : list FullLabel) : Prop :=
  WeakInclusion l1 l2 /\ WeakInclusion l2 l1.

Lemma commutative_Concat : forall m1 m2 o l,
    Step (ConcatMod m1 m2) o l ->
    exists l' o',
      Step (ConcatMod m2 m1) o' l' /\
      WeakEquality l l'.
Proof.
  intros.
  inversion_clear H.
  exists (l2++l1).
  exists (o2++o1).
  split.
  econstructor; try eassumption.
  intros.
  generalize (HNoRle y x H0 H).
  intros.
  destruct x. subst.
  destruct y. simpl in *.
  destruct p. destruct p0.
  simpl in *.
  destruct r2. assumption. destruct r1. assumption. assumption.
  reflexivity.
  reflexivity.
  subst.
  split.
  apply WeakInclusion_app_comm.
  apply WeakInclusion_app_comm.
Qed.

Lemma WeakInclusionRefl : forall l, WeakInclusion l l.
  intros.
  unfold WeakInclusion.
  split;intros; try assumption.
  reflexivity.
Qed.

Corollary WeakEqualityRefl : forall l, WeakEquality l l.
  intros.
  unfold WeakEquality.
  split; apply WeakInclusionRefl.
Qed.

Lemma WeakInclusionTrans : forall l1 l2 l3, WeakInclusion l1 l2 -> WeakInclusion l2 l3 -> WeakInclusion l1 l3.
  intros.
  unfold WeakInclusion in *.
  dest.
  split;intros;eauto using eq_trans.
Qed.

Corollary WeakEqualityTrans : forall l1 l2 l3, WeakEquality l1 l2 -> WeakEquality l2 l3 -> WeakEquality l1 l3.
  unfold WeakEquality; intros;dest; split; eauto using WeakInclusionTrans.
Qed.

Lemma WeakEqualitySym : forall l1 l2, WeakEquality l1 l2 -> WeakEquality l2 l1.
  intros.
  firstorder.
Qed.

Lemma WfNoDups m (HWfMod : WfMod m) :
    NoDup (map fst (getAllRegisters m)) /\
    NoDup (map fst (getAllMethods m))   /\
    NoDup (map fst (getAllRules m)).
Proof.
  specialize (HWfMod).
  induction m.
  - inv HWfMod.
    inv HWfBaseModule.
    dest.
    tauto.
  - inversion HWfMod; subst; apply IHm in HWf.
    assumption.
  - inversion HWfMod;subst;destruct (IHm1 HWf1) as [ND_Regs1 [ND_Meths1 ND_Rles1]];destruct (IHm2 HWf2) as [ND_Regs2 [ND_Meths2 ND_Rles2]];split;[|split].
    + simpl;rewrite map_app.
      induction (getAllRegisters m1); simpl;[assumption|].
      constructor.
      * intro.
        destruct (HDisjRegs (fst a));apply H0;[left; reflexivity|].
        inversion_clear ND_Regs1.
        apply in_app_or in H; destruct H; contradiction.
      * apply (IHl).
        intro;split;[|split];auto.
        -- inversion_clear ND_Regs1; assumption.
        -- unfold DisjKey; intro; destruct (HDisjRegs k);[left|right]; intro; apply H; auto.
           right; assumption.
        -- inversion_clear ND_Regs1; assumption.
    + simpl;rewrite map_app.
      induction (getAllMethods m1); simpl;[assumption|].
      constructor.
      * intro.
        destruct (HDisjMeths (fst a));apply H0;[left; reflexivity|].
        inversion_clear ND_Meths1.
        apply in_app_or in H; destruct H; contradiction.
      * apply (IHl).
        intro;split;[|split];auto.
        -- inversion_clear ND_Meths1; assumption.
        -- unfold DisjKey; intro; destruct (HDisjMeths k);[left|right]; intro; apply H; auto.
           right; assumption.
        -- inversion_clear ND_Meths1; assumption.
    + simpl;rewrite map_app.
      induction (getAllRules m1); simpl;[assumption|].
      constructor.
      * intro.
        destruct (HDisjRules (fst a));apply H0;[left; reflexivity|].
        inversion_clear ND_Rles1.
        apply in_app_or in H; destruct H; contradiction.
      * apply (IHl).
        intro;split;[|split];auto.
        -- inversion_clear ND_Rles1; assumption.
        -- unfold DisjKey; intro; destruct (HDisjRules k);[left|right]; intro; apply H; auto.
           right; assumption.
        -- inversion_clear ND_Rles1; assumption.
Qed.

Lemma WfMod_WfBaseMod_flat m (HWfMod : WfMod m):
  WfBaseModule (getFlat m).
Proof.
  specialize (HWfMod).
  unfold getFlat;induction m.
  - simpl; inversion HWfMod; subst; destruct HWfBaseModule.
    unfold WfBaseModule in *; split; intros.
    + specialize (H rule H1).
      induction H; econstructor; eauto.
    + dest; intros.
      repeat split; auto; intros.
      specialize (H0 meth H4 v).
      induction H0; econstructor; eauto.
  - inversion_clear HWfMod.
    specialize (IHm HWf).
    assumption.
  - inversion_clear HWfMod.
    specialize (IHm1 HWf1).
    specialize (IHm2 HWf2).
    simpl in *.
    constructor;simpl; repeat split; auto; intros; try destruct (in_app_or _ _ _ H) as [In1 | In1].
    + destruct IHm1 as [Rle Meth]; clear Meth; specialize (Rle _ In1).
      induction Rle; econstructor; eauto; setoid_rewrite map_app; apply in_or_app;left; assumption.
    + destruct IHm2 as [Rle Meth]; clear Meth; specialize (Rle _ In1).
      induction Rle; econstructor; eauto; setoid_rewrite map_app; apply in_or_app;right; assumption.
    + destruct IHm1 as [Rle [Meth _]]; clear Rle; specialize (Meth _ In1 v).
      induction Meth; econstructor; eauto; setoid_rewrite map_app; apply in_or_app;left; assumption.
    + destruct IHm2 as [Rle [Meth _]]; clear Rle; specialize (Meth _ In1 v).
      induction Meth; econstructor; eauto; setoid_rewrite map_app; apply in_or_app;right;assumption.
    + inv IHm1; inv IHm2; dest; apply NoDup_DisjKey; auto.
    + inv IHm1; inv IHm2; dest; apply NoDup_DisjKey; auto.
    + inv IHm1; inv IHm2; dest; apply NoDup_DisjKey; auto.
Qed.

Lemma WfConcatNotInCalls : forall (m : Mod)(o : RegsT)(k : Kind)(a : ActionT type k)
                                  (readRegs newRegs : RegsT)(cs : MethsT)(fret : type k)
                                  (f : MethT),
    WfConcatActionT a m ->
    SemAction o a readRegs newRegs cs fret ->
    In (fst f) (getHidden m) ->
    ~In f cs.
Proof.
  intros.
  induction H0; subst; eauto; inversion H; EqDep_subst; eauto.
  - specialize (IHSemAction (H8 mret)).
    intro TMP; destruct TMP;[subst; contradiction|contradiction].
  - intro TMP; apply in_app_or in TMP; destruct TMP.
    + eapply IHSemAction1; eauto.
    + eapply IHSemAction2; eauto.
  - intro TMP; apply in_app_or in TMP; destruct TMP.
    + eapply IHSemAction1; eauto.
    + eapply IHSemAction2; eauto.
  - intro TMP; apply in_app_or in TMP; destruct TMP.
    + eapply IHSemAction1; eauto.
    + eapply IHSemAction2; eauto.
Qed.

Lemma getNumFromCalls_notIn f cs :
  ~In f cs ->
  (getNumFromCalls f cs = 0%Z).
Proof.
  induction cs; intros; auto.
  destruct (MethT_dec f a);[subst;apply False_ind; apply H;left|rewrite getNumFromCalls_neq_cons];auto.
  apply IHcs; intro; apply H; right; assumption.
Qed.

Lemma WfConcats : forall (m1 m2 : Mod) (o : RegsT)(l : list FullLabel),
    (WfConcat m2 m1) ->
    Substeps (getFlat m2) o l ->
    (forall (s: string)(v : {x : Kind*Kind & SignT x}), In s (getHidden m1) -> (getNumCalls (s, v) l = 0%Z)).
Proof.
  intros.
  induction H0; subst.
  - reflexivity.
  - specialize (H).
    inversion H; simpl in HInRules;specialize (H2 _ HInRules).
    rewrite getNumCalls_cons; rewrite IHSubsteps;simpl.
    assert (In (fst (s, v)) (getHidden m1)) as P1;auto.
    rewrite (getNumFromCalls_notIn _ _ (WfConcatNotInCalls _ H2 HAction P1)); ring.
  - specialize (H).
    inversion H; simpl in HInMeths;specialize (H3 _ HInMeths argV).
    rewrite getNumCalls_cons; rewrite IHSubsteps;simpl.
    assert (In (fst (s, v)) (getHidden m1)) as P1;auto.
    rewrite (getNumFromCalls_notIn _ _ (WfConcatNotInCalls _ H3 HAction P1)); ring.
Qed.

Lemma WfConcats_Substeps : forall (m1 : Mod) m2 (o : RegsT)(l : list FullLabel),
    (WfConcat (Base m2) m1) ->
    Substeps m2 o l ->
    forall f, In (fst f) (getHidden m1) -> (getNumCalls f l = 0%Z).
Proof.
  intros.
  induction H0; subst.
  - reflexivity.
  - specialize (H).
    inversion H; simpl in HInRules;specialize (H2 _ HInRules).
    rewrite getNumCalls_cons; rewrite IHSubsteps;simpl.
    assert (In (fst f) (getHidden m1)) as P1;auto.
    rewrite (getNumFromCalls_notIn _ _ (WfConcatNotInCalls _ H2 HAction P1)); ring.
  - specialize (H).
    inversion H; simpl in HInMeths;specialize (H3 _ HInMeths argV).
    rewrite getNumCalls_cons; rewrite IHSubsteps;simpl.
    assert (In (fst f) (getHidden m1)) as P1;auto.
    rewrite (getNumFromCalls_notIn _ _ (WfConcatNotInCalls _ H3 HAction P1)); ring.
Qed.



Lemma WfConcats_Step : forall (m1 m2 : Mod) (o : RegsT) (l : list FullLabel),
    (WfConcat m2 m1) ->
    Step m2 o l ->
    (forall f, In (fst f) (getHidden m1) -> (getNumCalls f l = 0%Z)).
Proof.
  intros.
  induction H0; subst.
  - eapply WfConcats_Substeps; eauto.
  - unfold WfConcat in *; simpl in *.
    specialize (IHStep H); auto.
  - unfold WfConcat in *; simpl in *.
    setoid_rewrite in_app_iff in H.
    assert (sth1: (forall rule : RuleT, In rule (getAllRules m0) -> WfConcatActionT (snd rule type) m1) /\
               (forall meth : string * {x : Signature & MethodT x},
                   In meth (getAllMethods m0) -> forall v : type (fst (projT1 (snd meth))), WfConcatActionT (projT2 (snd meth) type v) m1)) by
        (firstorder fail).
    assert (sth2: (forall rule : RuleT, In rule (getAllRules m2) -> WfConcatActionT (snd rule type) m1) /\
               (forall meth : string * {x : Signature & MethodT x},
                   In meth (getAllMethods m2) -> forall v : type (fst (projT1 (snd meth))), WfConcatActionT (projT2 (snd meth) type v) m1) ) by
        (firstorder fail).
    specialize (IHStep1 sth1).
    specialize (IHStep2 sth2).
    rewrite getNumCalls_app; Omega.omega.
Qed.

Lemma WfConcats_Trace : forall (m1 m2 : Mod) (o : RegsT) ls (l : list FullLabel),
    Trace m2 o ls ->
    (WfConcat m2 m1) ->
    forall i,
      nth_error ls i = Some l ->
      (forall f, In (fst f) (getHidden m1) -> (getNumCalls f l = 0%Z)).
Proof.
  induction 1; subst; auto; intros.
  - destruct i; discriminate.
  - destruct i; simpl in *.
    + inv H1.
      eapply WfConcats_Step; eauto.
    + eapply IHTrace; eauto.
Qed.
    

Lemma substitute_Step' m (HWfMod: WfMod m):
  forall o l,
    StepSubstitute m o l ->
    exists l', Permutation l l' /\
               Step m o l'.
Proof.
  unfold StepSubstitute.
  induction m; simpl in *; intros; dest.
  - exists l; split;[apply Permutation_refl|constructor; auto].
    eapply Substeps_flatten; eauto.
  - assert (exists l' : list FullLabel, l [=] l' /\ Step m o l');[apply IHm;auto|dest;exists x;split;auto].
    + intros;
        specialize (HWfMod);
        inv HWfMod; auto.
    + constructor 2; auto.
      intros.
      unfold getListFullLabel_diff in *;rewrite <-H2.
      apply H1; auto.
  - assert (HWf1: WfMod m1) by (intros; specialize (HWfMod); inv HWfMod; auto).
    assert (HWf2: WfMod m2) by (intros; specialize (HWfMod); inv HWfMod; auto).
    specialize (IHm1 HWf1).
    specialize (IHm2 HWf2).
    destruct (WfNoDups HWf1) as [ND_Regs1 [ND_Meths1 ND_Rules1]].
    destruct (WfNoDups HWf2) as [ND_Regs2 [ND_Meths2 ND_Rules2]].
    specialize (WfMod_WfBaseMod_flat HWf1) as WfBaseMod1.
    specialize (WfMod_WfBaseMod_flat HWf2) as WfBaseMod2.
    pose proof (HWfMod) as hwfmod2.
    assert (WfConcat1: WfConcat m1 m2 ) by (intros; specialize (HWfMod); inv HWfMod; auto).
    assert (WfConcat2: WfConcat m2 m1 ) by (intros; specialize (HWfMod); inv HWfMod; auto).
    inv hwfmod2.
    pose proof (@split_Substeps1 (getFlat m1) (getFlat m2) HDisjRegs HDisjRules HDisjMeths WfBaseMod1 WfBaseMod2 _ _  ND_Regs1 ND_Regs2 H);dest.
    assert (Substeps (BaseMod (getAllRegisters m1) (getAllRules m1) (getAllMethods m1)) x (ModuleFilterLabels (getFlat m1) l) /\
            MatchingExecCalls_Base (ModuleFilterLabels (getFlat m1) l) (getFlat m1) /\
            (forall (s : string) (v : {x : Kind * Kind & SignT x}), In s (map fst (getAllMethods m1)) ->
                                                                    In s (getHidden m1) ->
                                                                    (getListFullLabel_diff (s, v) (ModuleFilterLabels (getFlat m1) l) = 0%Z))).
    + split;unfold getFlat at 1 in H5. assumption.
      split.
      * unfold getFlat in H0. simpl in H0.
        unfold getFlat; simpl.
        assert (MatchingExecCalls_Base l (concatFlat (getFlat m1) (getFlat m2)));[unfold concatFlat, getFlat;simpl; assumption|].
        apply (MatchingExecCalls_Split H7).
      * intros; specialize (WfConcats WfConcat2 H6 _ v H8) as P1.
        rewrite map_app in H1.
        specialize (H1 s v (in_or_app _ _ s (or_introl H7)) (in_or_app _ _ s (or_introl H8))); unfold getListFullLabel_diff in *.
        assert (DisjKey (getRules (getFlat m1)) (getRules (getFlat m2))) as P2;[repeat intro; apply HDisjRules|].
        assert (DisjKey (getMethods (getFlat m1))(getMethods (getFlat m2))) as P3;[repeat intro;apply HDisjMeths|].
        specialize (filter_perm P2 P3 H) as P4.
        rewrite P4, getNumExecs_app, getNumCalls_app in H1.
        setoid_rewrite P1 in H1.
        destruct (P3 s) as [P5|P5];[simpl in P5;contradiction|].
        assert (~In (fst (s,v)) (map fst (getMethods (getFlat m2)))) as P6;auto.
        setoid_rewrite (NotInDef_ZeroExecs_Substeps _ P6 H6) in H1; rewrite <-H1.
        repeat rewrite Z.add_0_r.
        reflexivity.
    + assert (Substeps (BaseMod (getAllRegisters m2) (getAllRules m2) (getAllMethods m2)) x0 (ModuleFilterLabels (getFlat m2) l) /\
              MatchingExecCalls_Base (ModuleFilterLabels (getFlat m2) l) (getFlat m2) /\
              (forall (s : string) (v : {x : Kind * Kind & SignT x}), In s (map fst (getAllMethods m2)) ->
                                                                      In s (getHidden m2) ->
                                                                      (getListFullLabel_diff (s, v) (ModuleFilterLabels (getFlat m2) l) = 0%Z))).
      * split;unfold getFlat at 1 in H6. assumption.
        split.
        -- unfold getFlat in H0. simpl in H0.
           unfold getFlat; simpl.
           assert (MatchingExecCalls_Base l (concatFlat (getFlat m1) (getFlat m2)));[unfold concatFlat, getFlat;simpl; assumption|].
           apply MatchingExecCalls_Base_comm in H8.
           eapply (MatchingExecCalls_Split H8).
        -- intros; specialize (WfConcats WfConcat1 H5 _ v H9) as P1.
           rewrite map_app in H1.
           specialize (H1 s v (in_or_app _ _ s (or_intror H8)) (in_or_app _ _ s (or_intror H9))); unfold getListFullLabel_diff in *.
           assert (DisjKey (getRules (getFlat m1)) (getRules (getFlat m2))) as P2;[repeat intro; apply HDisjRules|].
           assert (DisjKey (getMethods (getFlat m1))(getMethods (getFlat m2))) as P3;[repeat intro;apply HDisjMeths|].
           specialize (filter_perm P2 P3 H) as P4.
           rewrite P4, getNumExecs_app, getNumCalls_app in H1.
           setoid_rewrite P1 in H1.
           destruct (P3 s) as [P5|P5];[|simpl in P5;contradiction].
           assert (~In (fst (s,v)) (map fst (getMethods (getFlat m1)))) as P6;auto.
           setoid_rewrite (NotInDef_ZeroExecs_Substeps _ P6 H5) in H1; rewrite <-H1.
           repeat rewrite Z.add_0_r.
           reflexivity.
      * specialize (IHm1 x (ModuleFilterLabels (getFlat m1) l) H7).
        specialize (IHm2 x0 (ModuleFilterLabels (getFlat m2) l) H8). dest.
        exists (x2++x1).
        split.
        -- specialize (filter_perm (m1:=(getFlat m1)) (m2:=(getFlat m2)) HDisjRules HDisjMeths H).
           intro.
           specialize (Permutation_app H15 H13).
           intro.
           apply (Permutation_trans H17 H18).
        -- econstructor; eauto; specialize (split_Substeps2 (m1:=(getFlat m1)) (m2:=(getFlat m2)) HDisjRules HDisjMeths (o:=o)(l:=l) H); intros.
           ++ repeat intro.
              split.
              ** intro;specialize (WfConcats WfConcat1 H5 _ (snd f) H20);intro.
                 rewrite <-H15 in H18; destruct f; simpl in *; contradiction.
              ** assert (MatchingExecCalls_Base l (concatFlat (getFlat m1) (getFlat m2)));[apply H0|].
                 rewrite <-H15, <-H13.
                 assert (DisjKey (getRules (getFlat m1)) (getRules (getFlat m2))) as P1; auto.
                 assert (DisjKey (getMethods (getFlat m1)) (getMethods (getFlat m2))) as P2; auto.
                 specialize (MatchingExecCalls_Mix2 P1 P2 H H20) as P3.
                 rewrite <-H15 in H18.
                 specialize (P3 _ H18 H19); dest; assumption.
           ++ repeat intro.
              split.
              ** intro; specialize (WfConcats WfConcat2 H6 _ (snd f) H20); intro.
                 rewrite <-H13 in H18; destruct f; simpl in *; contradiction.
              ** assert (MatchingExecCalls_Base l (concatFlat (getFlat m1) (getFlat m2)));[apply H0|].
                 rewrite <- H15, <-H13.
                 assert (DisjKey (getRules (getFlat m1)) (getRules (getFlat m2))) as P1; auto.
                 assert (DisjKey (getMethods (getFlat m1)) (getMethods (getFlat m2))) as P2; auto.
                 specialize (MatchingExecCalls_Mix1 P1 P2 H H20) as P3.
                 rewrite <-H13 in H18.
                 specialize (P3 _ H18 H19); dest; assumption.
           ++  rewrite <- H15 in H18; rewrite <- H13 in H19.
               specialize (H17 _ _ H18 H19); assumption.
Qed.

Lemma WeakInclusionsRefl l : WeakInclusions l l.
Proof.
  induction l; constructor.
  - assumption.
  - apply WeakInclusionRefl.
Qed.

Corollary WeakEqualitiesRefl l : WeakEqualities l l.
Proof.
  unfold WeakEqualities; split; apply WeakInclusionsRefl.
Qed.

Lemma WeakInclusionsTrans : forall (l1 l2 l3 : list (list FullLabel)), WeakInclusions l1 l2 -> WeakInclusions l2 l3 -> WeakInclusions l1 l3.
Proof.
  induction l1, l2, l3; intros; auto; try inversion H; try inversion H0; subst.
  constructor.
  - apply (IHl1 _ _ H4 H10).
  - apply (WeakInclusionTrans H6 H12).
Qed.

Corollary WeakEqualitesTrans ls1 ls2 ls3 : WeakEqualities ls1 ls2 -> WeakEqualities ls2 ls3 -> WeakEqualities ls1 ls3.
Proof.
  unfold WeakEqualities; intros; dest; split; eapply WeakInclusionsTrans; eauto.
Qed.

Lemma WeakEqualitiesSymm ls1 ls2 : WeakEqualities ls1 ls2 -> WeakEqualities ls2 ls1.
Proof.
  firstorder.
Qed.

Lemma WeakInclusionsLen_consistent ls1 ls2 : WeakInclusions ls1 ls2 -> length ls1 = length ls2.
Proof.
  induction 1; simpl; auto.
Qed.

Lemma WeakInclusions_WeakInclusion : forall (ls1 ls2 : list (list FullLabel)),  WeakInclusions ls1 ls2 -> nthProp2 WeakInclusion ls1 ls2.
Proof.
  induction ls1, ls2; unfold nthProp2; intros; try destruct (nth_error nil i); auto; try inversion H; subst.
  -  apply WeakInclusionRefl.
  - destruct i; simpl;[|apply IHls1];assumption.
Qed.

Lemma WeakInclusion_WeakInclusions : forall (ls1 ls2 : list (list FullLabel)),
    length ls1 = length ls2 -> nthProp2 WeakInclusion ls1 ls2 -> WeakInclusions ls1 ls2.
Proof.
  induction ls1, ls2; intros; try constructor; try inversion H; try  apply nthProp2_cons in H0; try destruct H0;[apply (IHls1 _ H2 H0)|assumption].
Qed.

Definition TraceList (m : Mod) (ls : list (list FullLabel)) :=
  (exists (o : RegsT), Trace m o ls).

Definition TraceInclusion' (m m' : Mod) :=
  forall (o : RegsT)(ls : list (list FullLabel)), Trace m o ls -> exists (ls': list (list FullLabel)), TraceList m' ls' /\ WeakInclusions ls ls'.

Lemma TraceInclusion'_TraceInclusion : forall (m m' : Mod), TraceInclusion' m m' -> TraceInclusion m m'.
Proof.
  unfold TraceInclusion', TraceInclusion; intros; generalize (H o1 ls1 H0); unfold TraceList; intros; dest;exists x0, x.
  repeat split.
  - assumption.
  - apply (WeakInclusionsLen_consistent H2).
  - apply WeakInclusions_WeakInclusion;assumption.
Qed.

Lemma TraceInclusion_TraceInclusion' : forall (m m' : Mod), TraceInclusion m m' -> TraceInclusion' m m'.
Proof.
  unfold TraceInclusion'; intros; generalize (H _ _ H0); intros; dest; unfold TraceList; exists x0.
  split.
  - exists x; assumption.
  - apply (WeakInclusion_WeakInclusions H2 H3).
Qed.

Lemma PermutationInCall : forall (l l' : list FullLabel), Permutation l l' -> (forall (f : MethT), InCall f l <-> InCall f l').
Proof.
  induction 1.
  - firstorder.
  - intro; split; intros; try assumption.
    + apply (InCall_app_iff f (x::nil) l'); apply (InCall_app_iff f (x::nil) l) in H0.
      destruct H0;[left|right;apply IHPermutation];assumption.
    + apply (InCall_app_iff f (x::nil) l); apply (InCall_app_iff f (x::nil) l') in H0.
      destruct H0;[left|right;apply IHPermutation];assumption.
  - split; intros.
    + apply (InCall_app_iff f (x::y::nil) l); apply (InCall_app_iff f (y::x::nil) l) in H.
      destruct H;[left;simpl|right];firstorder.
    +  apply (InCall_app_iff f (y::x::nil) l); apply (InCall_app_iff f (x::y::nil) l) in H;firstorder.
  - intros; split;intros.
    + apply IHPermutation2; apply IHPermutation1; assumption.
    + apply IHPermutation1; apply IHPermutation2; assumption.
Qed.

Corollary neg_PermutationInCall : forall (l l' : list FullLabel), Permutation l l' -> (forall (f : MethT), ~InCall f l <-> ~InCall f l').
Proof.
  intros; split; repeat intro; apply H0;specialize (Permutation_sym H) as TMP;  eapply PermutationInCall; eauto.
Qed.

Lemma PermutationInExec : forall (l l' : list FullLabel), Permutation l l' -> (forall (f : MethT), InExec f l <-> InExec f l').
Proof.
  induction 1; firstorder.
Qed.

Corollary neg_PermutationInExec : forall (l l' : list FullLabel), Permutation l l' -> (forall (f : MethT), ~InExec f l <-> ~InExec f l').
Proof.
  intros; split; repeat intro; apply H0; specialize (Permutation_sym H) as TMP; eapply PermutationInExec; eauto.
Qed.

Lemma PermutationWI : forall (l l' : list FullLabel), Permutation l l' -> WeakInclusion l l'.
Proof.
  unfold WeakInclusion; repeat split; intros.
  - unfold getListFullLabel_diff; rewrite H; reflexivity.
  - setoid_rewrite H; assumption.
Qed.

Corollary PermutationWE : forall (l l' : list FullLabel), Permutation l l' -> WeakEquality l l'.
Proof.
  intros;unfold WeakEquality; split;[apply PermutationWI|apply PermutationWI;apply Permutation_sym];assumption.
Qed.

Lemma substitute_Step m o l (HWfMod: WfMod m):
  Step (flatten m) o l ->
  exists l',
    Permutation l l' /\
    Step m o l'.
Proof.
  rewrite (@StepSubstitute_flatten) in *; auto.
  apply substitute_Step'; auto.
Qed.

Inductive PermutationEquivLists {A : Type} : (list (list A)) -> (list (list A)) -> Prop :=
|PermutationEquiv_nil : PermutationEquivLists nil nil
|PermutationEquiv_cons ls ls' l l' : PermutationEquivLists ls ls' -> Permutation l l' -> PermutationEquivLists (l::ls) (l'::ls').

Lemma PermutationEquivLists_WeakInclusions : forall (ls ls' : list (list FullLabel)),
    PermutationEquivLists ls ls' -> WeakInclusions ls ls'.
Proof.
  induction 1.
  - constructor.
  - constructor; auto.
    apply PermutationWI; assumption.
Qed.

Lemma UpdRegs_perm u u' o o' : UpdRegs u o o' -> Permutation u u' -> UpdRegs u' o o'.
Proof.
  unfold UpdRegs; intros; dest.
  split; auto.
  intros.
  specialize (H1 s v H2).
  destruct H1;[left|right].
  - dest; exists x;split;auto.
    eapply Permutation_in; eauto.
  - destruct H1; split;[intro; apply H1|assumption].
    dest; exists x; split;[|assumption].
    apply Permutation_sym in H0.
    eapply Permutation_in; eauto.
Qed.
    
Lemma SameTrace m1 m2:
  (forall o1 l, Trace m1 o1 l -> exists o2, Trace m2 o2 l) ->
  TraceInclusion m1 m2.
Proof.
  unfold TraceInclusion; intros.
  pose proof (H _ _ H0); dest.
  exists x, ls1; auto.
  repeat split; auto.
  - unfold nthProp2; intros.
    destruct (nth_error ls1 i); auto.
    repeat split; tauto.
Qed.

Lemma WfMod_createHide l: forall m, WfMod (createHide m l) <-> (SubList l (map fst (getMethods m)) /\ WfMod (Base m)).
Proof.
  split.
  - induction l; simpl; intros; split; unfold SubList; simpl; intros; try tauto.
    + inv H.
      destruct H0; subst; rewrite createHide_Meths in *; firstorder fail.
    + inv H.
      destruct (IHl HWf); assumption.
  - unfold SubList; induction l; simpl; intros; try tauto; dest; constructor.
    + rewrite createHide_Meths; apply (H a); left; reflexivity.
    + apply IHl; intros; split;auto.
Qed.

Lemma WfMod_createHideMod l: forall m, WfMod (createHideMod m l) <-> (SubList l (map fst (getAllMethods m)) /\ WfMod m).
Proof.
  split.
  - induction l; simpl; intros; split; unfold SubList; simpl; intros; try tauto.
    + inv H.
      destruct H0; subst; rewrite createHideMod_Meths in *; firstorder fail.
    + inv H.
      destruct (IHl HWf); assumption.
  - unfold SubList; induction l; simpl; intros; try tauto; dest; constructor.
    + rewrite createHideMod_Meths; apply (H a); left; reflexivity.
    + apply IHl; intros; split;auto.
Qed.

Lemma WfActionT_flatten m k :
  forall (a : ActionT type k),
    WfActionT m a <-> WfActionT (getFlat (Base m)) a.
Proof.
  split; induction 1; econstructor; eauto.
Qed.

Theorem flatten_WfMod m: WfMod m -> WfMod (flatten m).
Proof.
  unfold flatten.
  induction 1; simpl; auto; intros.
  - constructor; auto.
    unfold getFlat.
    induction HWfBaseModule.
    constructor; intros.
    + specialize (H rule H1).
      apply WfActionT_flatten in H.
      assumption.
    + dest; intros.
      repeat split; auto; intros.
      specialize (H0 meth H4 v).
      apply WfActionT_flatten in H0.
      assumption.
  - constructor; auto.
    rewrite createHide_Meths.
    auto.
  - unfold getFlat in *; simpl.
    rewrite WfMod_createHide in *; dest; simpl in *.
    split.
    + rewrite map_app.
      unfold SubList in *; intros.
      rewrite in_app_iff in *.
      specialize (H3 x).
      specialize (H1 x).
      tauto.
    + constructor;inversion H4; inversion H2; inversion HWfBaseModule; inversion HWfBaseModule0; subst.
      * split; intros.
        -- destruct (in_app_or _ _ _ H6).
           ++ specialize (H5 _ H7).
              induction H5; econstructor; eauto; simpl; rewrite map_app; apply in_or_app; left; assumption.
           ++ specialize (H9 _ H7).
              induction H9; econstructor; eauto; simpl; rewrite map_app; apply in_or_app; right; assumption.
        -- repeat split; simpl; intros; dest.
           ++ destruct (in_app_or _ _ _ H6).
              ** specialize (H8 _ H16 v).
                 induction H8; econstructor; eauto; simpl; rewrite map_app; apply in_or_app; left; assumption.
              ** specialize (H7 _ H16 v).
                 induction H7; econstructor; eauto; simpl; rewrite map_app; apply in_or_app; right; assumption.
           ++ eapply NoDup_DisjKey; eauto.
           ++ eapply NoDup_DisjKey; eauto.
           ++ eapply NoDup_DisjKey; eauto.
Qed.

Definition flatten_ModWf m: ModWf :=
  (Build_ModWf (flatten_WfMod (wfMod m))).

Section TraceSubstitute.
  Variable m: ModWf.

  Lemma Trace_flatten_same1: forall o l,  Trace m o l -> Trace (flatten m) o l.
  Proof.
    induction 1; subst.
    - constructor 1; auto.
      unfold flatten.
      rewrite createHide_Regs.
      auto.
    - apply (@Step_substitute) in HStep; auto.
      + econstructor 2; eauto.
      + destruct m; auto.
  Qed.

  Lemma Trace_flatten_same2: forall o l, Trace (flatten m) o l -> (exists l', (PermutationEquivLists l l') /\ Trace m o l').
  Proof.
    induction 1; subst.
    - rewrite getAllRegisters_flatten in *.
      exists nil;split;constructor 1; auto.
    - apply substitute_Step in HStep;auto; dest.
      exists (x0::x);split.
      + constructor; auto.
      + econstructor 2; eauto.
        apply (Permutation_map fst) in H2.
        eapply UpdRegs_perm; eauto.
      + destruct m; auto.
  Qed.

  Theorem TraceInclusion_flatten_r: TraceInclusion m (flatten_ModWf m).
  Proof.
    unfold TraceInclusion; intros.
    exists o1, ls1.
    repeat split; auto; intros; unfold nthProp2; intros; try destruct (nth_error ls1 i); auto; repeat split; intros; try firstorder.
    apply Trace_flatten_same1; auto.
  Qed.

  Theorem TraceInclusion_flatten_l: TraceInclusion (flatten_ModWf m) m.
  Proof.
    apply TraceInclusion'_TraceInclusion.
    unfold TraceInclusion'; intros.
    apply Trace_flatten_same2 in H.
    dest.
    exists x.
    split.
    - unfold TraceList; exists o; auto.
    - apply PermutationEquivLists_WeakInclusions.
      assumption.
  Qed.
End TraceSubstitute.

Lemma word0_neq: forall w : word 1, w <> WO~0 -> w = WO~1.
Proof.
  intros.
  shatter_word w.
  destruct x; auto.
  tauto.
Qed.

Section test.
  Variable ty: Kind -> Type.
  Definition Slt2 n (e1 e2: Expr ty (SyntaxKind (Bit (n + 1)))) :=
    ITE (Eq (UniBit (TruncMsb n 1) e1) (Const ty WO~0))
        (ITE (Eq (UniBit (TruncMsb n 1) e2) (Const ty WO~0)) (BinBitBool (LessThan _) e1 e2) (Const ty false))
        (ITE (Eq (UniBit (TruncMsb n 1) e2) (Const ty WO~1)) (BinBitBool (LessThan _) e1 e2) (Const ty true)).
End test.

Lemma Slt_same n e1 e2: evalExpr (Slt2 n e1 e2) = evalExpr (Slt n e1 e2).
Proof.
  unfold Slt2, Slt.
  simpl.
  destruct (weq (split2 n 1 (evalExpr e1)) WO~0); simpl; auto.
  - rewrite e.
    destruct (weq (split2 n 1 (evalExpr e2)) WO~0); simpl; auto.
    + rewrite e0.
      destruct (wlt_dec (evalExpr e1) (evalExpr e2)); simpl; auto.
    + destruct (wlt_dec (evalExpr e1) (evalExpr e2)); simpl; auto.
      * destruct (weq WO~0 (split2 n 1 (evalExpr e2))); simpl; auto.
      * destruct (weq WO~0 (split2 n 1 (evalExpr e2))); simpl; auto.
        apply word0_neq in n0.
        pre_word_omega.
        rewrite wordToNat_split2 in *.
        pose proof (pow2_zero n) as sth0.
        rewrite Nat.div_small_iff in e by lia.
        assert (sth: 0 < #(evalExpr e2) / pow2 n) by lia.
        rewrite Nat.div_str_pos_iff in sth; lia.
  - destruct (weq (split2 n 1 (evalExpr e2)) WO~0); simpl; auto.
    + rewrite e.
      destruct (wlt_dec (evalExpr e1) (evalExpr e2)); simpl; auto.
      * destruct (weq (split2 n 1 (evalExpr e1)) WO~0); simpl; auto.
        apply word0_neq in n1.
        pre_word_omega.
        rewrite wordToNat_split2 in *.
        pose proof (pow2_zero n) as sth0.
        rewrite Nat.div_small_iff in e by lia.
        assert (sth: 0 < #(evalExpr e1) / pow2 n) by lia.
        rewrite Nat.div_str_pos_iff in sth; lia.
      * destruct (weq (split2 n 1 (evalExpr e1)) WO~0); simpl; auto.
        tauto.
    + apply word0_neq in n0.
      apply word0_neq in n1.
      rewrite ?n0, ?n1.
      simpl.
      destruct (wlt_dec (evalExpr e1) (evalExpr e2)); simpl; auto.
Qed.

Lemma mergeSeparatedBaseFile_noHides (rfl : list RegFileBase) :
  getHidden (mergeSeparatedBaseFile rfl) = nil.
Proof.
  induction rfl; auto.
Qed.

Lemma mergeSeparatedBaseMod_noHides (bl : list BaseModule) :
  getHidden (mergeSeparatedBaseMod bl) = nil.
Proof.
  induction bl; auto.
Qed.

Lemma getHidden_createHideMod (m : Mod) (hides : list string) :
  getHidden (createHideMod m hides) = hides++(getHidden m).
Proof.
  induction hides; auto.
  - simpl; rewrite IHhides; reflexivity.
Qed.

Lemma getAllRegisters_createHideMod (m : Mod) (hides : list string) :
  getAllRegisters (createHideMod m hides) = getAllRegisters m.
Proof.
  induction hides; auto.
Qed.

Lemma getAllRegisters_mergeBaseFile (rfl : list RegFileBase) :
  getAllRegisters (mergeSeparatedBaseFile rfl) = (concat (map getRegFileRegisters rfl)).
Proof.
  induction rfl;auto.
  simpl; rewrite IHrfl; reflexivity.
Qed.

Lemma getAllRegisters_mergeBaseMod (bl : list BaseModule) :
  getAllRegisters (mergeSeparatedBaseMod bl) = (concat (map getRegisters bl)).
Proof.
  induction bl; auto.
  simpl; rewrite IHbl; reflexivity.
Qed.

Lemma getAllMethods_createHideMod (m : Mod) (hides : list string) :
  getAllMethods (createHideMod m hides) = getAllMethods m.
Proof.
  induction hides; auto.
Qed.

Lemma getAllMethods_mergeBaseFile (rfl : list RegFileBase) :
  getAllMethods (mergeSeparatedBaseFile rfl) = (concat (map getRegFileMethods rfl)).
Proof.
  induction rfl;auto.
  simpl; rewrite IHrfl; reflexivity.
Qed.

Lemma getAllMethods_mergeBaseMod (bl : list BaseModule) :
  getAllMethods (mergeSeparatedBaseMod bl) = (concat (map getMethods bl)).
Proof.
  induction bl; auto.
  simpl; rewrite IHbl; reflexivity.
Qed.

Lemma getAllRules_createHideMod (m : Mod) (hides : list string) :
  getAllRules (createHideMod m hides) = getAllRules m.
Proof.
  induction hides; auto.
Qed.

Lemma getAllRules_mergeBaseFile (rfl : list RegFileBase) :
  getAllRules (mergeSeparatedBaseFile rfl) = nil.
Proof.
  induction rfl;auto.
Qed.

Lemma getAllRules_mergeBaseMod (bl : list BaseModule) :
  getAllRules (mergeSeparatedBaseMod bl) = (concat (map getRules bl)).
Proof.
  induction bl; auto.
  simpl; rewrite IHbl; reflexivity.
Qed.


Lemma separateBaseMod_flatten (m : Mod) :
  getAllRegisters m [=] getAllRegisters (mergeSeparatedMod (separateMod m)).
Proof.
  unfold mergeSeparatedMod.
  rewrite getAllRegisters_createHideMod.
  unfold separateMod; simpl.
  rewrite getAllRegisters_mergeBaseFile, getAllRegisters_mergeBaseMod.
  induction m.
  - destruct m; simpl; repeat rewrite app_nil_r; reflexivity.
  - simpl; assumption.
  - simpl in *.
    destruct (separateBaseMod m1), (separateBaseMod m2).
    simpl in *.
    repeat rewrite map_app, concat_app; rewrite IHm1, IHm2.
    repeat rewrite <- app_assoc; apply Permutation_app_head.
    repeat rewrite app_assoc; apply Permutation_app_tail.
    apply Permutation_app_comm.
Qed.

Lemma separateBaseModule_flatten_Methods (m : Mod) :
  getAllMethods m [=] getAllMethods (mergeSeparatedMod (separateMod m)).
Proof.
  unfold mergeSeparatedMod.
  rewrite getAllMethods_createHideMod.
  unfold separateMod; simpl.
  rewrite getAllMethods_mergeBaseFile, getAllMethods_mergeBaseMod.
  induction m.
  - destruct m; simpl; repeat rewrite app_nil_r; reflexivity.
  - simpl; assumption.
  - simpl in *.
    destruct (separateBaseMod m1), (separateBaseMod m2).
    simpl in *.
    repeat rewrite map_app, concat_app; rewrite IHm1, IHm2.
    repeat rewrite <- app_assoc; apply Permutation_app_head.
    repeat rewrite app_assoc; apply Permutation_app_tail.
    apply Permutation_app_comm.
Qed.

Lemma separateBaseModule_flatten_Rules (m : Mod) :
  getAllRules m [=] getAllRules (mergeSeparatedMod (separateMod m)).
Proof.
  unfold mergeSeparatedMod.
  rewrite getAllRules_createHideMod.
  unfold separateMod; simpl.
  rewrite getAllRules_mergeBaseFile, getAllRules_mergeBaseMod; simpl.
  induction m.
  - destruct m; simpl; repeat rewrite app_nil_r; reflexivity.
  - simpl; assumption.
  - simpl in *.
    destruct (separateBaseMod m1), (separateBaseMod m2).
    simpl in *.
    repeat rewrite map_app, concat_app; rewrite IHm1, IHm2.
    reflexivity.
Qed.

Lemma separateBaseModule_flatten_Hides (m : Mod) :
  getHidden m [=] getHidden (mergeSeparatedMod (separateMod m)).
Proof.
  unfold mergeSeparatedMod.
  rewrite getHidden_createHideMod;simpl.
  rewrite mergeSeparatedBaseFile_noHides.
  rewrite mergeSeparatedBaseMod_noHides.
  repeat rewrite app_nil_r.
  reflexivity.
Qed.

Lemma dec_def_notHidden f m:
  (In f (map fst (getAllMethods m)) /\ ~ In f (getHidden m)) \/
  (~ In f (map fst (getAllMethods m))) \/ (In f (map fst (getAllMethods m)) /\ In f (getHidden m)).
Proof.
  destruct (in_dec string_dec f (map fst (getAllMethods m))), (in_dec string_dec f (getHidden m)); auto.
Qed.

Lemma NotInDef_ZeroExecs_Trace:
  forall (m : Mod) (o : RegsT) lss (ls : list FullLabel) (f : string * {x : Kind * Kind & SignT x}),
    Trace m o lss ->
    ~ In (fst f) (map fst (getAllMethods m)) ->
    forall i,
      nth_error lss i = Some ls ->
      getNumExecs f ls = 0%Z.
Proof.
  induction 1; subst; simpl; auto; intros; simpl in *.
  - destruct i; simpl in *; discriminate.
  - specialize (IHTrace H0).
    destruct i; simpl in *.
    + inv H1.
      eapply NotInDef_ZeroExecs_Step; eauto.
    + eauto.
Qed.


Section ModularSubstitution.
  Variable a b a' b': Mod.
  Variable SameList_a: forall x, (In x (map fst (getAllMethods a)) /\
                                  ~ In x (getHidden a)) <->
                                 (In x (map fst (getAllMethods a')) /\
                                  ~ In x (getHidden a')).
  Variable SameList_b: forall x, (In x (map fst (getAllMethods b)) /\
                                  ~ In x (getHidden b)) <->
                                 (In x (map fst (getAllMethods b')) /\
                                  ~ In x (getHidden b')).

  Variable wfAConcatB: WfMod (ConcatMod a b).
  Variable wfA'ConcatB': WfMod (ConcatMod a' b').

  Theorem ModularSubstitution: TraceInclusion a a' ->
                             TraceInclusion b b' ->
                             TraceInclusion (ConcatMod a b) (ConcatMod a' b').
  Proof.
    assert (WfConcat1: WfConcat a b) by (intros; specialize (wfAConcatB); inv wfAConcatB; auto).
    assert (WfConcat2: WfConcat b a) by (intros; specialize (wfAConcatB); inv wfAConcatB; auto).
    assert (WfConcat0: WfConcat a' b') by (intros; specialize (wfA'ConcatB'); inv wfA'ConcatB'; auto).
    assert (WfConcat3: WfConcat b' a') by (intros; specialize (wfA'ConcatB'); inv wfA'ConcatB'; auto).
    pose proof (wfAConcatB) as wfAConcatB_dup.
    pose proof (wfA'ConcatB') as wfA'ConcatB'_dup.
    inv wfAConcatB_dup.
    inv wfA'ConcatB'_dup.
    unfold TraceInclusion, WeakInclusion,getListFullLabel_diff in *; intros.
    pose proof (SplitTrace HDisjRegs HDisjRules HDisjMeths H1); dest.
    specialize (@H _ _ H2).
    specialize (@H0 _ _ H3).
    dest.
    exists (x1 ++ x).
    exists (map (fun x => fst x ++ snd x) (List.combine x2 x0)).
    pose proof H9 as sth1.
    pose proof H7 as sth2.
    rewrite map_length in H9, H7.
    rewrite H9 in H7.
    rewrite mapProp_nthProp in H5.
    repeat split.
    - apply JoinTrace; auto; unfold nthProp, nthProp2 in *; intros; auto.
      specialize (H10 i); specialize (H8 i); specialize (H5 i).
      rewrite nth_error_map in H10, H8;
        case_eq (nth_error x2 i);
        case_eq (nth_error x0 i);
        case_eq (nth_error ls1 i);
        intros;
        try congruence; auto;
          [rewrite H11, H12, H13 in *; dest|
           solve [exfalso; apply (nth_error_len _ _ _ H11 H13 H9)]].
      Opaque MatchingExecCalls_Concat.
      repeat split; intros.
      Transparent MatchingExecCalls_Concat.
      + unfold MatchingExecCalls_Concat in *; intros.
        repeat match goal with
               | H : forall (x: MethT), _ |- _ => specialize (H f)
               end; try specialize (HDisjMeths (fst f));
          try specialize (HDisjMeths0 (fst f));
          try specialize (SameList_a (fst f));
          try specialize (SameList_b (fst f));
          try specialize (Subset_a (fst f));
          try specialize (Subset_b (fst f)).
        specialize (getNumExecs_nonneg f l1) as P1;
          rewrite Z.lt_eq_cases in P1; destruct P1;
            [specialize (Trace_meth_InExec' H _ _ H13 H21) as P2; clear - HDisjMeths0 P2 H20; tauto|].
        specialize (getNumCalls_nonneg f l1) as P1; rewrite Z.lt_eq_cases in P1; destruct P1;[|symmetry in H22; contradiction].
        rewrite <- H21 in H10; simpl in H10.
        specialize (getNumExecs_nonneg f (filterExecs id a l)) as P1.
        specialize (getNumCalls_nonneg f (filterExecs id a l)) as P2.
        assert (getNumCalls f (filterExecs id a l) <> 0%Z);[clear - P1 P2 H22 H10;Omega.omega|].
        specialize (H5 H23).
        assert (helper: (getNumExecs f (filterExecs id a l) < getNumCalls f (filterExecs id a l))%Z) by Omega.omega.
        pose proof (Trace_meth_InCall_InDef_InExec H2 f i) as sth10.
        pose proof (map_nth_error (filterExecs id a) _ _ H11) as sth11.
        specialize (sth10 _ sth11).
        pose proof (in_dec string_dec (fst f) (map fst (getAllMethods a))) as [th1 | th2].
        * clear - H11 H2 helper th1 sth10 sth11.
          specialize (sth10 th1).
          pose proof (Trace_meth_InCall_InDef_InExec H2 f i) as sth0.
          Omega.omega.
        * pose proof (NotInDef_ZeroExecs_Trace f H2 th2 _ sth11) as sth12.
          assert (sth13: (getNumCalls f (filterExecs id a l) > 0)%Z) by (Omega.omega).
          rewrite sth12 in *.
          assert (sth14: getNumCalls f (filterExecs id a l) = getNumCalls f l1) by Omega.omega.
          destruct (in_dec string_dec (fst f) (map fst (getAllMethods b))) as [ez|hard].
          -- specialize (H5 ez); dest.
             rewrite sth14 in *.
             split; [tauto|Omega.omega].
          -- destruct (in_dec string_dec (fst f) (getHidden b')) as [lhs | rhs]; [ | tauto].
             pose proof (WfConcats_Trace H WfConcat0 _ H13 f lhs).
             Omega.omega.
      + unfold MatchingExecCalls_Concat in *; intros.
        repeat match goal with
               | H : forall (x: MethT), _ |- _ => specialize (H f)
               end; try specialize (HDisjMeths (fst f));
          try specialize (HDisjMeths0 (fst f));
          try specialize (SameList_a (fst f));
          try specialize (SameList_b (fst f));
          try specialize (Subset_a (fst f));
          try specialize (Subset_b (fst f)).
        specialize (getNumExecs_nonneg f l0) as P1;
          rewrite Z.lt_eq_cases in P1; destruct P1;
            [specialize (Trace_meth_InExec' H0 _ _ H12 H21) as P2; clear - HDisjMeths0 P2 H20; tauto|].
        specialize (getNumCalls_nonneg f l0) as P1; rewrite Z.lt_eq_cases in P1; destruct P1;[|symmetry in H22; contradiction].
        rewrite <- H21 in H8; simpl in H8.
        specialize (getNumExecs_nonneg f (filterExecs id b l)) as P1.
        specialize (getNumCalls_nonneg f (filterExecs id b l)) as P2.
        assert (getNumCalls f (filterExecs id b l) <> 0%Z);[clear - P1 P2 H22 H8;Omega.omega|].
        specialize (H14 H23).
        assert (helper: (getNumExecs f (filterExecs id b l) < getNumCalls f (filterExecs id b l))%Z) by Omega.omega.
        pose proof (Trace_meth_InCall_InDef_InExec H3 f i) as sth10.
        pose proof (map_nth_error (filterExecs id b) _ _ H11) as sth11.
        specialize (sth10 _ sth11).
        pose proof (in_dec string_dec (fst f) (map fst (getAllMethods b))) as [th1 | th2].
        * clear - H11 H3 helper th1 sth10 sth11.
          specialize (sth10 th1).
          pose proof (Trace_meth_InCall_InDef_InExec H3 f i) as sth0.
          Omega.omega.
        * pose proof (NotInDef_ZeroExecs_Trace f H3 th2 _ sth11) as sth12.
          assert (sth13: (getNumCalls f (filterExecs id b l) > 0)%Z) by (Omega.omega).
          rewrite sth12 in *.
          assert (sth14: getNumCalls f (filterExecs id b l) = getNumCalls f l0) by Omega.omega.
          destruct (in_dec string_dec (fst f) (map fst (getAllMethods a))) as [ez|hard].
          -- specialize (H14 ez); dest.
             rewrite sth14 in *.
             split; [tauto|Omega.omega].
          -- destruct (in_dec string_dec (fst f) (getHidden a')) as [lhs | rhs]; [ | tauto].
             pose proof (WfConcats_Trace H0 WfConcat3 _ H12 f lhs).
             Omega.omega.
      + destruct x3, x4, p, p0, r1, r2; simpl; auto.
        pose proof (in_map (fun x => fst (snd x)) _ _ H19) as sth3.
        pose proof (in_map (fun x => fst (snd x)) _ _ H20) as sth4.
        simpl in *.
        assert (sth5: exists rle, In (Rle rle)
                                     (map (fun x => fst (snd x))
                                          (filterExecs id a l))) by
            (clear - H18 sth3; firstorder fail).
        assert (sth6: exists rle, In (Rle rle)
                                     (map (fun x => fst (snd x))
                                          (filterExecs id b l))) by
            (clear - H17 sth4; firstorder fail).
        dest.
        rewrite in_map_iff in *; dest.
        specialize (H15 _ _ H24 H23).
        rewrite H22, H21 in *.
        assumption.
    - rewrite map_length.
      rewrite length_combine_cond; congruence.
    - unfold nthProp, nthProp2 in *; intros.
      specialize (H10 i); specialize (H8 i); specialize (H5 i).
      rewrite nth_error_map in *.
      simpl in *.
      case_eq (nth_error ls1 i); intros; rewrite H11 in *; auto.
      setoid_rewrite (nth_error_combine (fun x3 => fst x3 ++ snd x3) _ i x2 x0); auto.
      case_eq (nth_error x2 i);
        case_eq (nth_error x0 i);
        intros; auto; rewrite H12, H13 in *; simpl in *; intros.
      split; intros.
      + dest.
        rewrite H16 at 1 2.
        repeat rewrite getNumExecs_app, getNumCalls_app.
        specialize (H8 f);specialize (H10 f).
        clear - H8 H10; Omega.omega.
      + dest.
        rewrite H17. rewrite map_app, in_app_iff in *; setoid_rewrite in_app_iff.
        clear - H19 H18 H14.
        firstorder fail.
  Qed.
End ModularSubstitution.

Section Fold.
  Variable k: Kind.

  Variable f: LetExprSyntax type k -> LetExprSyntax type k -> LetExprSyntax type k.
  Variable fEval: type k -> type k -> type k.
  Variable fEval_f: forall x y, evalLetExpr (f x y) = fEval (evalLetExpr x) (evalLetExpr y).

  Lemma evalFoldLeft_Let ls:
    forall seed,
      evalLetExpr (fold_left f ls seed) =
      fold_left fEval (map (@evalLetExpr _) ls) (evalLetExpr seed).
  Proof.
    induction ls; simpl; auto; intros.
    rewrite IHls; simpl.
    rewrite fEval_f.
    reflexivity.
  Qed.

  Lemma evalFoldRight_Let ls:
    forall seed,
      evalLetExpr (fold_right f seed ls) =
      fold_right fEval (evalLetExpr seed) (map (@evalLetExpr _) ls).
  Proof.
    induction ls; simpl; auto; intros.
    rewrite fEval_f.
    rewrite IHls; simpl.
    reflexivity.
  Qed.

  Local Ltac name_term n t H := 
    assert (H: exists n', n' = t);
    try (exists t; reflexivity);
    destruct H as [n H]. 


  Lemma evalFoldTree_Let ls:
    forall seed,
      evalLetExpr (fold_tree f seed ls) =
      fold_tree fEval (evalLetExpr seed) (map (@evalLetExpr _) ls).
  Proof.
    assert (exists l, length ls <= l) 
      as [l K] by (exists (length ls); auto). 
    revert ls K.
    induction l as [| l]; intros * K.
    - assert (A1: length ls = 0) by omega. 
      apply length_zero_iff_nil in A1.
      now subst ls.
    - destruct ls as [| x1 xs]. now simpl.
      destruct xs as [| x2 xs].
      intros.
      simpl.
      rewrite ?fold_tree_equation.
      auto.

      intros.
      rewrite fold_tree_equation.
      name_term tpl (unapp_half (x1::x2::xs)) Tpl;
        rewrite <- Tpl; destruct tpl as [m1 m2].
      simpl in K. 
      assert (K': S (length xs) <= l) by (rewrite le_S_n; auto); 
        clear K; rename K' into K.
      assert (length m1 <= length (x2::xs) 
              /\ length m2 <= length (x2::xs))
        as [A1 A2]. {
        symmetry in Tpl.
        apply unapp_half_nonnil_reduces in Tpl; auto.
        2: simpl; omega. 
        simpl in *.
        omega. 
      }
      simpl in A1, A2.
      assert (A3: length m1 <= l) by omega; clear A1.
      assert (A4: length m2 <= l) by omega; clear A2.
      remember (f (fold_tree f seed m1) (fold_tree f seed m2)) as sth.
      rewrite fold_tree_equation.
      simpl.
      apply unapp_half_map with (f := (@evalLetExpr _)) in Tpl.
      simpl in Tpl.
      rewrite <- Tpl.
      rewrite Heqsth; clear Heqsth.
      rewrite <- ?IHl; auto.
      destruct xs; simpl; auto.
  Qed.

  Variable fComm: forall a b, fEval a b = fEval b a.
  Variable fAssoc: forall a b c, fEval (fEval a b) c = fEval a (fEval b c).
  Variable unit: LetExprSyntax type k.
  Variable fUnit: forall x, fEval (evalLetExpr unit) x = x.
  
  Lemma evalFoldTree_evalFoldLeft ls:
    evalLetExpr (fold_tree f unit ls) =
    evalLetExpr (fold_left f ls unit).
  Proof.
    rewrite evalFoldLeft_Let.
    rewrite evalFoldTree_Let.
    rewrite fold_left_fold_tree; auto.
  Qed.

  
  Lemma evalFoldTree_evalFoldRight ls:
    evalLetExpr (fold_tree f unit ls) =
    evalLetExpr (fold_right f unit ls).
  Proof.
    rewrite evalFoldRight_Let.
    rewrite evalFoldTree_Let.
    rewrite fold_right_fold_tree; auto.
  Qed.
End Fold.

Section SimulationZeroAct.
  Variable imp spec: BaseModuleWf.
  Variable simRel: RegsT -> RegsT -> Prop.
  Variable simRelGood: forall oImp oSpec, simRel oImp oSpec -> getKindAttr oSpec = getKindAttr (getRegisters spec).
  Variable initRel: forall rimp, Forall2 regInit rimp (getRegisters imp) ->
                                 exists rspec, Forall2 regInit rspec (getRegisters spec) /\ simRel rimp rspec.

  Variable NoMeths: getMethods imp = [].
  Variable NoMethsSpec: getMethods spec = [].

  Variable simulation:
    forall oImp rImp uImp rleImp csImp oImp' aImp,
      In (rleImp, aImp) (getRules imp) ->
      SemAction oImp (aImp type) rImp uImp csImp WO ->
      UpdRegs [uImp] oImp oImp' ->
      forall oSpec,
        simRel oImp oSpec ->
        ((simRel oImp' oSpec /\ csImp = []) \/
         (exists rleSpec aSpec,
             In (rleSpec, aSpec) (getRules spec) /\
             exists rSpec uSpec,
               SemAction oSpec (aSpec type) rSpec uSpec csImp WO /\
               exists oSpec',
                 UpdRegs [uSpec] oSpec oSpec' /\
                 simRel oImp' oSpec')).

  Theorem simulationZeroAct:
    TraceInclusion (Base imp) (Base spec).
  Proof.
    pose proof (wfBaseModule imp) as wfImp.
    pose proof (wfBaseModule spec) as wfSpec.
    inv wfImp.
    inv wfSpec.
    dest.
    apply simulationZero with (simRel := simRel); auto; simpl; intros.
    inv H9; [|discriminate].
    inv HLabel.
    specialize (@simulation oImp reads u rn cs oImp' rb HInRules HAction H10 _ H11).
    pose proof (simRelGood H11).
    destruct simulation.
    - left; auto.
    - right.
      dest.
      exists x2, x, x3.
      split.
      + pose proof (WfActionT_ReadsWellDefined (H1 _ H12) H13) as sth1.
        pose proof (WfActionT_WritesWellDefined (H1 _ H12) H13) as sth2.
        repeat econstructor; eauto.
      + split; assumption.
  Qed.
End SimulationZeroAct.

Section LemmaNoSelfCall.
  Variable m: BaseModule.
  Lemma NoSelfCallAction ls k (a: ActionT type k):
    NoCallActionT ls a ->
    forall o reads u cs ret,
      SemAction o a reads u cs ret ->
      forall f, In (fst f) ls ->
                getNumFromCalls f cs = 0%Z.
  Proof.
    intro.
    induction H; simpl; auto; intros; simpl in *.
    - inv H2.
      EqDep_subst; simpl.
      specialize (H1 _ _ _ _ _ _ HSemAction _ H3).
      rewrite H1 in *.
      match goal with
      | |- (if ?P then _ else _) = _ => destruct P
      end; auto; subst; simpl in *.
      tauto.
    - inv H1; EqDep_subst; simpl in *.
      eapply H0; eauto.
    - inv H2; EqDep_subst; simpl in *.
      rewrite getNumFromCalls_app.
      specialize (H1 _ _ _ _ _ _ HSemActionCont _ H3).
      specialize (IHNoCallActionT _ _ _ _ _ HSemAction _ H3).
      rewrite H1, IHNoCallActionT.
      auto.
    - inv H1; EqDep_subst; simpl in *.
      eapply H0; eauto.
    - inv H1; EqDep_subst; simpl in *.
      eapply H0; eauto.
    - inv H0; EqDep_subst; simpl in *.
      eapply IHNoCallActionT; eauto.
    - inv H3; EqDep_subst; simpl in *; rewrite getNumFromCalls_app.
      + specialize (IHNoCallActionT1 _ _ _ _ _ HAction _ H4).
        specialize (H0 _ _ _ _ _ _ HSemAction _ H4).
        rewrite H0, IHNoCallActionT1.
        auto.
      + specialize (IHNoCallActionT2 _ _ _ _ _ HAction _ H4).
        specialize (H0 _ _ _ _ _ _ HSemAction _ H4).
        rewrite H0, IHNoCallActionT2.
        auto.
    - inv H0; EqDep_subst; simpl in *.
      eapply IHNoCallActionT; eauto.
    - inv H; EqDep_subst; simpl in *.
      auto.
  Qed.

  Lemma LetExprNoCallActionT k (e: LetExprSyntax type k): forall ls, NoCallActionT ls (convertLetExprSyntax_ActionT e).
  Proof.
    induction e; simpl; auto; intros; constructor; auto.
  Qed.
  
  Lemma NoSelfCallRule_Impl r:
    NoSelfCallBaseModule m ->
    In r (getRules m) ->
    forall o reads u cs ret,
      SemAction o (snd r type) reads u cs ret ->
      forall f, In (fst f) (map fst (getMethods m)) ->
                getNumFromCalls  f cs = 0%Z.
  Proof.
    intros.
    destruct H.
    unfold NoSelfCallRulesBaseModule, NoSelfCallMethsBaseModule in *.
    specialize (H _ H0); simpl in *.
    eapply NoSelfCallAction; eauto.
  Qed.

  Lemma NoSelfCallMeth_Impl f:
    NoSelfCallBaseModule m ->
    In f (getMethods m) ->
    forall o reads u cs arg ret,
      SemAction o (projT2 (snd f) type arg) reads u cs ret ->
      forall g, In (fst g) (map fst (getMethods m)) ->
                getNumFromCalls  g cs = 0%Z.
  Proof.
    intros.
    destruct H.
    unfold NoSelfCallRulesBaseModule, NoSelfCallMethsBaseModule in *.
    specialize (H3 _ H0 arg); simpl in *.
    eapply NoSelfCallAction; eauto.
  Qed.
End LemmaNoSelfCall.

Section SimulationGen.
  Variable imp spec: BaseModuleWf.
  Variable NoSelfCalls: NoSelfCallBaseModule spec.
  
  Variable simRel: RegsT -> RegsT -> Prop.
  Variable simRelGood: forall oImp oSpec, simRel oImp oSpec -> getKindAttr oSpec = getKindAttr (getRegisters spec).
  Variable initRel: forall rimp, Forall2 regInit rimp (getRegisters imp) ->
                                 exists rspec, Forall2 regInit rspec (getRegisters spec) /\ simRel rimp rspec.

  Variable simulationRule:
    forall oImp rImp uImp rleImp csImp oImp' aImp,
      In (rleImp, aImp) (getRules imp) ->
      SemAction oImp (aImp type) rImp uImp csImp WO ->
      UpdRegs [uImp] oImp oImp' ->
      forall oSpec,
        simRel oImp oSpec ->
        ((simRel oImp' oSpec /\ csImp = []) \/
         (exists rleSpec aSpec,
             In (rleSpec, aSpec) (getRules spec) /\
             exists rSpec uSpec,
               SemAction oSpec (aSpec type) rSpec uSpec csImp WO /\
               exists oSpec',
                 UpdRegs [uSpec] oSpec oSpec' /\
                 simRel oImp' oSpec')).

  Variable simulationMeth:
    forall oImp rImp uImp meth csImp oImp' sign aImp arg ret,
      In (meth, existT _ sign aImp) (getMethods imp) ->
      SemAction oImp (aImp type arg) rImp uImp csImp ret ->
      UpdRegs [uImp] oImp oImp' ->
      forall oSpec,
        simRel oImp oSpec ->
          exists aSpec rSpec uSpec,
            In (meth, existT _ sign aSpec) (getMethods spec) /\
            SemAction oSpec (aSpec type arg) rSpec uSpec csImp ret /\
              exists oSpec',
                UpdRegs [uSpec] oSpec oSpec' /\
                simRel oImp' oSpec'.

  Variable notMethMeth:
    forall oImp rImpl1 uImpl1 meth1 sign1 aImp1 arg1 ret1 csImp1
           rImpl2 uImpl2 meth2 sign2 aImp2 arg2 ret2 csImp2,
      In (meth1, existT _ sign1 aImp1) (getMethods imp) ->
      SemAction oImp (aImp1 type arg1) rImpl1 uImpl1 csImp1 ret1 ->
      In (meth2, existT _ sign2 aImp2) (getMethods imp) ->
      SemAction oImp (aImp2 type arg2) rImpl2 uImpl2 csImp2 ret2 ->
      exists k, In k (map fst uImpl1) /\ In k (map fst uImpl2).
          
  Variable notRuleMeth:
    forall oImp rImpl1 uImpl1 rleImpl1 aImp1 csImp1
           rImpl2 uImpl2 meth2 sign2 aImp2 arg2 ret2 csImp2,
      In (rleImpl1, aImp1) (getRules imp) ->
      SemAction oImp (aImp1 type) rImpl1 uImpl1 csImp1 WO ->
      In (meth2, existT _ sign2 aImp2) (getMethods imp) ->
      SemAction oImp (aImp2 type arg2) rImpl2 uImpl2 csImp2 ret2 ->
      exists k, In k (map fst uImpl1) /\ In k (map fst uImpl2).

  Lemma SubstepsSingle o l:
    Substeps imp o l ->
    length l <= 1.
  Proof.
    induction 1; simpl; auto; intros; subst.
    - destruct ls; simpl in *; auto; simpl in *.
      assert (sth1: length ls = 0) by (simpl in *; Omega.omega).
      rewrite length_zero_iff_nil in sth1; subst; simpl in *.
      specialize (HNoRle p (or_introl eq_refl)).
      specialize (HDisjRegs p (or_introl eq_refl)).
      repeat destruct p; simpl in *.
      destruct r0; simpl in *; [tauto|].
      inv H; [discriminate|].
      destruct fb; simpl in *.
      destruct (@notRuleMeth _ _ _ _ _ _ _ _ _ _ _ _ _ _ HInRules HAction HInMeths HAction0) as [k [in1 in2]].
      specialize (HDisjRegs k).
      inv HLabel.
      tauto.
    - destruct ls; simpl in *; auto; simpl in *.
      assert (sth1: length ls = 0) by (simpl in *; Omega.omega).
      rewrite length_zero_iff_nil in sth1; subst; simpl in *.
      specialize (HDisjRegs p (or_introl eq_refl)).
      repeat destruct p; simpl in *.
      inv H.
      + inv HLabel; simpl in *.
        inv HSubstep; try congruence.
        destruct fb.
        destruct (@notRuleMeth _ _ _ _ _ _ _ _ _ _ _ _ _ _ HInRules HAction0 HInMeths HAction) as [k [in1 in2]].
        specialize (HDisjRegs k).
        tauto.
      + destruct ls; [| discriminate].
        inv HLabel.
        destruct fb.
        destruct fb0.
        destruct (@notMethMeth _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HInMeths HAction HInMeths0 HAction0) as [k [in1 in2]].
        specialize (HDisjRegs k).
        tauto.
  Qed.
        
  Theorem simulationGen:
    TraceInclusion (Base imp) (Base spec).
  Proof.
    pose proof (wfBaseModule imp) as wfImp.
    pose proof (wfBaseModule spec) as wfSpec.
    inv wfImp.
    inv wfSpec.
    dest.
    apply StepSimulation with (simRel := simRel); auto; simpl; intros.
    inv H9.
    pose proof (SubstepsSingle HSubsteps) as sth.
    destruct lImp; [tauto| simpl in *].
    destruct lImp; simpl in *; [| Omega.omega].
    repeat destruct p; simpl in *.
    inv HSubsteps; inv HLabel; simpl in *.
    - destruct (@simulationRule _ _ _ _ _ _ _ HInRules HAction H11 _ H12); dest; subst.
      exists nil, oSpec.
      split.
      + constructor; auto; simpl in *.
        * constructor 1; auto.
          eapply simRelGood; eauto.
        * unfold MatchingExecCalls_Base, getNumCalls, getNumExecs; intros; simpl.
          Omega.omega.
      + simpl.
        split.
        * unfold UpdRegs; repeat split; auto; intros.
          right; split; try intro; simpl in *; auto.
          dest; auto.
        * split; auto.
          unfold WeakInclusion; simpl; intros.
          unfold getListFullLabel_diff; simpl.
          split; intros; dest; auto.
          tauto.
      + exists [(x2, (Rle x, cs))], x3; simpl.
        split.
        * constructor; auto.
          -- econstructor 2; eauto.
             ++ eapply WfActionT_ReadsWellDefined; eauto.
             ++ eapply WfActionT_WritesWellDefined; eauto.
             ++ simpl; intros; tauto.
             ++ constructor 1; auto.
                eapply simRelGood; eauto.
          -- unfold MatchingExecCalls_Base; unfold getNumCalls, getNumExecs; simpl; intros.
             rewrite app_nil_r.
             assert (th1: forall x, (x = 0)%Z -> (x <= 0)%Z) by (intros; Omega.omega).
             apply th1; clear th1.
             eapply NoSelfCallRule_Impl; eauto.
        * split; auto.
          split; auto.
          unfold WeakInclusion; simpl; intros.
          split; intros; auto.
          exists rn.
          left; auto.
    - destruct fb.
      destruct (@simulationMeth _ _ _ _ _ _ _ _ _ _ HInMeths HAction H11 _ H12); dest; subst.
      exists [(x2, (Meth (fn, existT _ x (argV, retV)), cs))], x3; simpl.
      split.
      * constructor; auto.
        -- econstructor 3; eauto.
           ++ eapply WfActionT_ReadsWellDefined; eauto.
           ++ eapply WfActionT_WritesWellDefined; eauto.
           ++ simpl; intros; tauto.
           ++ constructor 1; auto.
              eapply simRelGood; eauto.
        -- unfold MatchingExecCalls_Base; unfold getNumCalls, getNumExecs; simpl; intros.
           rewrite app_nil_r.
           assert (th1: forall x, (x = 0)%Z -> (x <= 0)%Z) by (intros; Omega.omega).
           match goal with
           | |- (_ <= if ?P then _ else _)%Z => destruct P; subst; simpl in *
           end.
           ++ assert (th2: forall x, (x = 0)%Z -> (x <= 1)%Z) by (intros; Omega.omega).
              apply th2; clear th2.
              eapply NoSelfCallMeth_Impl; eauto.
           ++ apply th1; clear th1.
              eapply NoSelfCallMeth_Impl; eauto.
      * split; auto.
        split; auto.
        unfold WeakInclusion; simpl; intros.
        split; intros; auto.
  Qed.
End SimulationGen.    

Lemma findRegs_Some u:
  NoDup (map fst u) ->
  forall s v,
    In (s, v) u <-> findReg s u = Some v.
Proof.
  induction u; simpl; split; auto; intros; auto; try (tauto || discriminate).
  - destruct H0; subst; simpl.
    + destruct (string_dec s s); simpl; tauto.
    + destruct a; simpl in *.
      inv H.
      specialize (IHu H4).
      destruct (string_dec s s0); subst; simpl; auto; subst.
      * apply (in_map fst) in H0; simpl in *; tauto.
      * rewrite <- IHu; auto.
  - destruct a; simpl in *.
    destruct (string_dec s s0); simpl in *.
    inv H0; auto.
    inv H.
    specialize (IHu H4).
    rewrite <- IHu in H0.
    auto.
Qed.

Lemma InvProp A (P Q: A -> Prop):
  (forall x, P x <-> Q x) ->
  (forall x, ~ Q x <-> ~ P x).
Proof.
  intros.
  firstorder.
Qed.

Lemma findRegs_None u:
  forall s,
    ~ In s (map fst u) <-> findReg s u = None.
Proof.
  induction u; simpl; split; auto; destruct a; simpl; intros.
  - destruct (string_dec s s0); subst.
    + firstorder fail.
    + rewrite <- IHu.
      firstorder fail.
  - destruct (string_dec s s0); subst.
    + discriminate.
    + rewrite <- IHu in H.
      intro.
      destruct H0; subst; firstorder fail.
Qed.

Lemma NoDup_app A (l1: list (string * A)):
  forall l2,
    DisjKeyWeak l1 l2 ->
    NoDup (map fst l1) ->
    NoDup (map fst l2) ->
    NoDup (map fst (l1 ++ l2)).
Proof.
  induction l1; unfold DisjKeyWeak; simpl; auto;
    rewrite ?app_nil_l, ?app_nil_r; intros; auto.
  inv H0.
  constructor.
  - intro.
    rewrite map_app in *.
    rewrite in_app_iff in H0.
    specialize (H (fst a) (or_introl eq_refl)).
    tauto.
  - eapply IHl1; auto.
    unfold DisjKeyWeak; firstorder fail.
Qed.

Lemma SemAction_NoDup_u k o (a: ActionT type k) readRegs u calls retl:
  SemAction o a readRegs u calls retl ->
  NoDup (map fst u).
Proof.
  induction 1; simpl; auto; rewrite ?DisjKeyWeak_same in * by (apply string_dec); subst.
  - apply NoDup_app; auto.
  - simpl.
    constructor; auto.
    unfold key_not_In in *.
    intro.
    rewrite in_map_iff in H0; dest.
    destruct x; simpl in *; subst.
    firstorder fail.
  - apply NoDup_app; auto.
  - apply NoDup_app; auto.
  - simpl; constructor.
Qed.

Lemma NoDup_UpdRegs o:
  NoDup (map fst o) ->
  forall u o',
    NoDup (map fst u) ->
    UpdRegs [u] o o' ->
    o' = doUpdRegs u o.
Proof.
  induction o; simpl; auto; intros.
  - inv H1; simpl in *.
    apply eq_sym in H2.
    apply map_eq_nil in H2.
    auto.
  - inv H1; simpl in *.
    destruct o'; simpl in *; [discriminate|].
    inv H2.
    f_equal.
    + specialize (H3 (fst p) (snd p)).
      destruct p; simpl in *.
      specialize (H3 (or_introl eq_refl)).
      rewrite H4 in *.
      destruct H3.
      * dest.
        destruct H1; [subst|tauto].
        rewrite findRegs_Some in H2; auto.
        rewrite H2; auto.
      * dest.
        assert (sth2: ~ In s (map fst u)) by firstorder.
        pose proof sth2 as sth3.
        rewrite findRegs_None in sth2.
        rewrite sth2.
        destruct H2; [congruence|].
        inv H.
        apply (in_map fst) in H2; simpl in *.
        exfalso; tauto.
    + inv H.
      eapply IHo; eauto.
      constructor; auto; intros; simpl.
      specialize (H3 s v (or_intror H)).
      destruct H3; [tauto|].
      dest.
      destruct H2; subst; simpl in *.
      * apply (in_map fst) in H; simpl in *.
        apply (f_equal (map fst)) in H6.
        rewrite ?map_map in *; simpl in *.
        assert (sth: forall A B, (fun (x: (A * B)) => fst x) = fst) by (intros; extensionality x; intros; reflexivity).
        rewrite ?sth in H6.
        rewrite <- H6 in H.
        tauto.
      * right; auto.
Qed.

Lemma doUpdRegs_enuf o u (noDup: NoDup (map fst u)):
  getKindAttr o = getKindAttr (doUpdRegs u o) ->
  UpdRegs [u] o (doUpdRegs u o).
Proof.
  induction o; simpl; auto; unfold UpdRegs; intros.
  - repeat split; simpl; auto.
  - inv H.
    specialize (IHo H3).
    simpl in *; intros.
    repeat split; auto; intros.
    + rewrite H1 at 1.
      rewrite H2 at 1.
      rewrite H3.
      auto.
    + unfold UpdRegs in *.
      dest.
      destruct H.
      * case_eq (findReg (fst a) u); intros; rewrite H5 in *; simpl in *.
        -- rewrite <- findRegs_Some in H5 by auto.
           inv H; simpl in *.
           left; eexists; eauto.
        -- rewrite <- findRegs_None in H5 by auto; subst; simpl in *.
           right.
           split; try intro; auto; dest.
           destruct H; subst; auto.
      * specialize (H4 _ _ H).
        clear - H4; firstorder fail.
Qed.

Lemma UpdRegs_nil_nil_upd: forall o, NoDup (map fst o) -> forall o', UpdRegs [[]] o o' -> o = o'.
Proof.
  unfold UpdRegs.
  intros.
  dest.
  simpl in *.
  assert (sth: forall s v, In (s, v) o' -> In (s, v) o).
  { intros.
    specialize (H1 s v H2).
    destruct H1; dest; try auto.
    destruct H1; subst; simpl in *; try tauto.
  }
  clear H1.
  generalize o' H H0 sth.
  clear o' H H0 sth.
  induction o; destruct o'; simpl; auto; intros.
  - discriminate.
  - discriminate.
  - inv H0.
    inv H.
    specialize (IHo _ H6 H4).
    destruct p, a; simpl in *; subst; auto; repeat f_equal; auto.
    + specialize (sth s s0 (or_introl eq_refl)).
      destruct sth.
      * inv H; subst; auto.
      * apply (in_map fst) in H; simpl in *; tauto.
    + eapply IHo; intros.
      specialize (sth _ _ (or_intror H)).
      destruct sth; [|auto].
      inv H0; subst.
      apply (f_equal (map fst)) in H4.
      rewrite ?map_map in *; simpl in *.
      setoid_rewrite (functional_extensionality (fun x => fst x) fst) in H4; try tauto.
      apply (in_map fst) in H; simpl in *; congruence.
Qed.

Lemma findRegs_Some' u:
  forall s v,
    findReg s u = Some v ->
    In (s, v) u.
Proof.
  induction u; simpl; auto; intros; auto; try (tauto || discriminate).
  destruct (string_dec s (fst a)); subst; simpl in *.
  - inv H; auto.
    destruct a; auto.
  - specialize (IHu _ _ H).
    right; auto.
Qed.
                           
Lemma getKindAttr_findReg_Some u:
  forall o: RegsT,
    (forall s v, In (s, v) u -> In (s, projT1 v) (getKindAttr o)) ->
    forall s v,
      findReg s u = Some v ->
      In (s, projT1 v) (getKindAttr o).
Proof.
  intros.
  apply findRegs_Some' in H0.
  specialize (H _ _ H0); simpl in *.
  auto.
Qed.

Lemma getKindAttr_doUpdRegs' o:
  forall u,
    getKindAttr (doUpdRegs u o) = map (fun x => match findReg (fst x) u with
                                                | Some y => (fst x, projT1 y)
                                                | None => (fst x, projT1 (snd x))
                                                end) o.
Proof.
  induction o; simpl; auto; intros.
  case_eq (findReg (fst a) u); simpl; intros; f_equal; auto.
Qed.

Lemma forall_map A B (f g: A -> B) ls:
  (map f ls = map g ls) <->
  forall x, In x ls -> f x = g x.
Proof.
  induction ls; simpl; split; auto; intros; try tauto.
  - destruct H0; subst.
    + inv H.
      auto.
    + inv H.
      rewrite IHls in H3.
      eapply H3; eauto.
  - assert (sth1: f a = g a) by firstorder fail.
    assert (sth2: forall x, In x ls -> f x = g x) by firstorder fail.
    f_equal; auto.
    firstorder.
Qed.


Lemma KeyMatching_gen A B : forall (l : list (A * B)) (a b : A * B),
    NoDup (map fst l) -> In a l -> In b l -> fst a = fst b -> a = b.
Proof.
  induction l; intros.
  - inversion H0.
  - destruct H0; destruct H1.
    + symmetry; rewrite <- H1; assumption.
    + rewrite (map_cons fst) in H.
      inversion H; subst.
      apply (in_map fst l b) in H1.
      apply False_ind. apply H5.
      destruct a0; destruct b; simpl in *.
      rewrite H2; assumption.
    + rewrite (map_cons fst) in H.
      inversion H; subst.
      apply (in_map fst l a0) in H0.
      apply False_ind; apply H5.
      destruct a0, b; simpl in *.
      rewrite <- H2; assumption.
    + inversion H; subst.
      apply IHl; auto.
Qed.


Lemma getKindAttr_doUpdRegs o:
  NoDup (map fst o) ->
  forall u,
    NoDup (map fst u) ->
    (forall s v, In (s, v) u -> In (s, projT1 v) (getKindAttr o)) ->
    getKindAttr o = getKindAttr (doUpdRegs u o).
Proof.
  intros.
  setoid_rewrite getKindAttr_doUpdRegs'.
  rewrite forall_map; intros.
  case_eq (findReg (fst x) u); intros; auto.
  rewrite <- findRegs_Some in H3; auto.
  specialize (H1 _ _ H3).
  f_equal.
  destruct x; simpl in *.
  apply (in_map (fun x => (fst x, projT1 (snd x)))) in H2; simpl in *.
  assert (sth: map fst o = map fst (getKindAttr o)). {
    rewrite map_map; simpl.
    assert (sth2: fst = fun x : RegT => fst x) by (extensionality x; intros; auto).
    rewrite sth2; auto.
  }
  rewrite sth in H.
  pose proof (@KeyMatching_gen _ _ (getKindAttr o) _ _ H H1 H2 eq_refl); simpl in *.
  inv H4; congruence.
Qed.

Lemma doUpdRegs_UpdRegs' o:
  NoDup (map fst o) ->
  forall u,
    NoDup (map fst u) ->
    (forall s v, In (s, v) u -> In (s, projT1 v) (getKindAttr o)) ->
    UpdRegs [u] o (doUpdRegs u o).
Proof.
  intros.
  eapply doUpdRegs_enuf; eauto.
  eapply getKindAttr_doUpdRegs; eauto.
Qed.

Lemma doUpdRegs_UpdRegs o:
  NoDup (map fst o) ->
  forall u,
    NoDup (map fst u) ->
    SubList (getKindAttr u) (getKindAttr o) ->
    UpdRegs [u] o (doUpdRegs u o).
Proof.
  intros.
  eapply doUpdRegs_enuf; eauto.
  eapply getKindAttr_doUpdRegs; eauto; intros.
  apply (in_map (fun x => (fst x, projT1 (snd x)))) in H2; simpl in *.
  eapply H1; eauto.
Qed.

Section SimulationGeneralEx.
  Variable imp spec: BaseModuleWf.
  Variable NoSelfCalls: NoSelfCallBaseModule spec.
  
  Variable simRel: RegsT -> RegsT -> Prop.
  Variable simRelGood: forall oImp oSpec, simRel oImp oSpec -> getKindAttr oSpec = getKindAttr (getRegisters spec).
  Variable simRelImpGood: forall oImp oSpec, simRel oImp oSpec -> getKindAttr oImp = getKindAttr (getRegisters imp).
  Variable initRel: forall rimp, Forall2 regInit rimp (getRegisters imp) ->
                                 exists rspec, Forall2 regInit rspec (getRegisters spec) /\ simRel rimp rspec.

  Variable simulationRule:
    forall oImp rImp uImp rleImp csImp aImp,
      In (rleImp, aImp) (getRules imp) ->
      SemAction oImp (aImp type) rImp uImp csImp WO ->
      forall oSpec,
        simRel oImp oSpec ->
        ((simRel (doUpdRegs uImp oImp) oSpec /\ csImp = []) \/
         (exists rleSpec aSpec,
             In (rleSpec, aSpec) (getRules spec) /\
             exists rSpec uSpec,
               SemAction oSpec (aSpec type) rSpec uSpec csImp WO /\
               exists oSpec',
                 UpdRegs [uSpec] oSpec oSpec' /\
                 simRel (doUpdRegs uImp oImp) oSpec')).

  Variable simulationMeth:
    forall oImp rImp uImp meth csImp sign aImp arg ret,
      In (meth, existT _ sign aImp) (getMethods imp) ->
      SemAction oImp (aImp type arg) rImp uImp csImp ret ->
      forall oSpec,
        simRel oImp oSpec ->
          exists aSpec rSpec uSpec,
            In (meth, existT _ sign aSpec) (getMethods spec) /\
            SemAction oSpec (aSpec type arg) rSpec uSpec csImp ret /\
              exists oSpec',
                UpdRegs [uSpec] oSpec oSpec' /\
                simRel (doUpdRegs uImp oImp) oSpec'.

  Variable notMethMeth:
    forall oImp rImpl1 uImpl1 meth1 sign1 aImp1 arg1 ret1 csImp1
           rImpl2 uImpl2 meth2 sign2 aImp2 arg2 ret2 csImp2,
      In (meth1, existT _ sign1 aImp1) (getMethods imp) ->
      SemAction oImp (aImp1 type arg1) rImpl1 uImpl1 csImp1 ret1 ->
      In (meth2, existT _ sign2 aImp2) (getMethods imp) ->
      SemAction oImp (aImp2 type arg2) rImpl2 uImpl2 csImp2 ret2 ->
      exists k, In k (map fst uImpl1) /\ In k (map fst uImpl2).
          
  Variable notRuleMeth:
    forall oImp rImpl1 uImpl1 rleImpl1 aImp1 csImp1
           rImpl2 uImpl2 meth2 sign2 aImp2 arg2 ret2 csImp2,
      In (rleImpl1, aImp1) (getRules imp) ->
      SemAction oImp (aImp1 type) rImpl1 uImpl1 csImp1 WO ->
      In (meth2, existT _ sign2 aImp2) (getMethods imp) ->
      SemAction oImp (aImp2 type arg2) rImpl2 uImpl2 csImp2 ret2 ->
      exists k, In k (map fst uImpl1) /\ In k (map fst uImpl2).

  Theorem simulationGeneralEx:
    TraceInclusion (Base imp) (Base spec).
  Proof.
    eapply simulationGen; eauto; intros.
    - pose proof (SemAction_NoDup_u H0) as sth.
      pose proof (simRelImpGood H2) as sth2.
      apply (f_equal (map fst)) in sth2.
      rewrite ?map_map in *; simpl in *.
      assert (sth3: forall A B, (fun x: (A * B) => fst x) = fst) by
          (intros; extensionality x; intros; auto).
      destruct (wfBaseModule imp); dest.
      rewrite <- sth3 in H6.
      rewrite <- sth2 in H6.
      rewrite sth3 in H6.
      apply NoDup_UpdRegs in H1; subst; auto.
      eapply simulationRule; eauto.
    - pose proof (SemAction_NoDup_u H0) as sth.
      pose proof (simRelImpGood H2) as sth2.
      apply (f_equal (map fst)) in sth2.
      rewrite ?map_map in *; simpl in *.
      assert (sth3: forall A B, (fun x: (A * B) => fst x) = fst) by
          (intros; extensionality x; intros; auto).
      destruct (wfBaseModule imp); dest.
      rewrite <- sth3 in H6.
      rewrite <- sth2 in H6.
      rewrite sth3 in H6.
      apply NoDup_UpdRegs in H1; subst; auto.
      eapply simulationMeth; eauto.
  Qed.
End SimulationGeneralEx.

Section SimulationZeroA.
  Variable imp spec: BaseModuleWf.
  Variable simRel: RegsT -> RegsT -> Prop.
  Variable simRelGood: forall oImp oSpec, simRel oImp oSpec ->
                                          getKindAttr oSpec = getKindAttr (getRegisters spec).
  Variable simRelImpGood: forall oImp oSpec, simRel oImp oSpec ->
                                             getKindAttr oImp = getKindAttr (getRegisters imp).
  Variable initRel: forall rimp, Forall2 regInit rimp (getRegisters imp) ->
                                 exists rspec, Forall2 regInit rspec (getRegisters spec) /\
                                               simRel rimp rspec.

  Variable NoMeths: getMethods imp = [].
  Variable NoMethsSpec: getMethods spec = [].

  Variable simulation:
    forall oImp rImp uImp rleImp csImp aImp,
      In (rleImp, aImp) (getRules imp) ->
      SemAction oImp (aImp type) rImp uImp csImp WO ->
      forall oSpec,
        simRel oImp oSpec ->
        ((simRel (doUpdRegs uImp oImp) oSpec /\ csImp = []) \/
         (exists rleSpec aSpec,
             In (rleSpec, aSpec) (getRules spec) /\
             exists rSpec uSpec,
               SemAction oSpec (aSpec type) rSpec uSpec csImp WO /\
               exists oSpec',
                 UpdRegs [uSpec] oSpec oSpec' /\
                 simRel (doUpdRegs uImp oImp) oSpec')).

  Theorem simulationZeroA:
    TraceInclusion (Base imp) (Base spec).
  Proof.
    eapply simulationZeroAct; eauto; intros.
    pose proof (SemAction_NoDup_u H0) as sth.
    pose proof (simRelImpGood H2) as sth2.
    apply (f_equal (map fst)) in sth2.
    rewrite ?map_map in *; simpl in *.
    assert (sth3: forall A B, (fun x: (A * B) => fst x) = fst) by
        (intros; extensionality x; intros; auto).
    destruct (wfBaseModule imp); dest.
    rewrite <- sth3 in H6.
    rewrite <- sth2 in H6.
    rewrite sth3 in H6.
    apply NoDup_UpdRegs in H1; subst; auto.
    eapply simulation; eauto.
  Qed.
End SimulationZeroA.

Section SimulationGeneral.
  Variable imp spec: BaseModuleWf.
  Variable NoSelfCalls: NoSelfCallBaseModule spec.
  
  Variable simRel: RegsT -> RegsT -> Prop.
  Variable simRelGood: forall oImp oSpec, simRel oImp oSpec -> getKindAttr oSpec = getKindAttr (getRegisters spec).
  Variable simRelImpGood: forall oImp oSpec, simRel oImp oSpec -> getKindAttr oImp = getKindAttr (getRegisters imp).
  Variable initRel: forall rimp, Forall2 regInit rimp (getRegisters imp) ->
                                 exists rspec, Forall2 regInit rspec (getRegisters spec) /\ simRel rimp rspec.

  Variable simulationRule:
    forall oImp rImp uImp rleImp csImp aImp,
      In (rleImp, aImp) (getRules imp) ->
      SemAction oImp (aImp type) rImp uImp csImp WO ->
      forall oSpec,
        simRel oImp oSpec ->
        ((simRel (doUpdRegs uImp oImp) oSpec /\ csImp = []) \/
         (exists rleSpec aSpec,
             In (rleSpec, aSpec) (getRules spec) /\
             exists rSpec uSpec,
               SemAction oSpec (aSpec type) rSpec uSpec csImp WO /\
                 simRel (doUpdRegs uImp oImp) (doUpdRegs uSpec oSpec))).

  Variable simulationMeth:
    forall oImp rImp uImp meth csImp sign aImp arg ret,
      In (meth, existT _ sign aImp) (getMethods imp) ->
      SemAction oImp (aImp type arg) rImp uImp csImp ret ->
      forall oSpec,
        simRel oImp oSpec ->
          exists aSpec rSpec uSpec,
            In (meth, existT _ sign aSpec) (getMethods spec) /\
            SemAction oSpec (aSpec type arg) rSpec uSpec csImp ret /\
                simRel (doUpdRegs uImp oImp) (doUpdRegs uSpec oSpec).

  Variable notMethMeth:
    forall oImp rImpl1 uImpl1 meth1 sign1 aImp1 arg1 ret1 csImp1
           rImpl2 uImpl2 meth2 sign2 aImp2 arg2 ret2 csImp2,
      In (meth1, existT _ sign1 aImp1) (getMethods imp) ->
      SemAction oImp (aImp1 type arg1) rImpl1 uImpl1 csImp1 ret1 ->
      In (meth2, existT _ sign2 aImp2) (getMethods imp) ->
      SemAction oImp (aImp2 type arg2) rImpl2 uImpl2 csImp2 ret2 ->
      exists k, In k (map fst uImpl1) /\ In k (map fst uImpl2).
          
  Variable notRuleMeth:
    forall oImp rImpl1 uImpl1 rleImpl1 aImp1 csImp1
           rImpl2 uImpl2 meth2 sign2 aImp2 arg2 ret2 csImp2,
      In (rleImpl1, aImp1) (getRules imp) ->
      SemAction oImp (aImp1 type) rImpl1 uImpl1 csImp1 WO ->
      In (meth2, existT _ sign2 aImp2) (getMethods imp) ->
      SemAction oImp (aImp2 type arg2) rImpl2 uImpl2 csImp2 ret2 ->
      exists k, In k (map fst uImpl1) /\ In k (map fst uImpl2).

  Theorem simulationGeneral:
    TraceInclusion (Base imp) (Base spec).
  Proof.
    eapply simulationGeneralEx; eauto; intros.
    - specialize (@simulationRule _ _ _ _ _ _ H H0 oSpec H1).
      destruct simulationRule; auto.
      dest.
      right.
      exists x, x0; repeat split; auto.
      exists x1, x2; repeat split; auto.
      exists (doUpdRegs x2 oSpec); split; auto.
      
      pose proof (SemAction_NoDup_u H3) as sth.
      destruct (wfBaseModule spec); dest.
      pose proof (simRelGood H1) as sth2.
      apply (f_equal (map fst)) in sth2.
      rewrite ?map_map in *; simpl in *.
      assert (sth3: forall A B, (fun x: (A * B) => fst x) = fst) by
          (intros; extensionality y; intros; auto).
      rewrite <- sth3 in H8.
      rewrite <- sth2 in H8.
      rewrite sth3 in H8.
      pose proof (SemActionUpdSub H3).
      eapply doUpdRegs_UpdRegs; eauto.
    - specialize (@simulationMeth _ _ _ _ _ _ _ _ _ H H0 oSpec H1).
      pose proof simulationMeth as sth; clear simulationMeth.
      dest.
      exists x, x0, x1; repeat split; auto.
      exists (doUpdRegs x1 oSpec); split; auto.
      pose proof (SemAction_NoDup_u H3) as sth.
      destruct (wfBaseModule spec); dest.
      pose proof (simRelGood H1) as sth2.
      apply (f_equal (map fst)) in sth2.
      rewrite ?map_map in *; simpl in *.
      assert (sth3: forall A B, (fun x: (A * B) => fst x) = fst) by
          (intros; extensionality y; intros; auto).
      rewrite <- sth3 in H8.
      rewrite <- sth2 in H8.
      rewrite sth3 in H8.
      pose proof (SemActionUpdSub H3).
      eapply doUpdRegs_UpdRegs; eauto.
  Qed.
End SimulationGeneral.

Section SimulationZeroAction.
  Variable imp spec: BaseModuleWf.
  Variable simRel: RegsT -> RegsT -> Prop.
  Variable simRelGood: forall oImp oSpec, simRel oImp oSpec ->
                                          getKindAttr oSpec = getKindAttr (getRegisters spec).
  Variable simRelImpGood: forall oImp oSpec, simRel oImp oSpec ->
                                             getKindAttr oImp = getKindAttr (getRegisters imp).
  Variable initRel: forall rimp, Forall2 regInit rimp (getRegisters imp) ->
                                 exists rspec, Forall2 regInit rspec (getRegisters spec) /\
                                               simRel rimp rspec.

  Variable NoMeths: getMethods imp = [].
  Variable NoMethsSpec: getMethods spec = [].

  Variable simulation:
    forall oImp rImp uImp rleImp csImp aImp,
      In (rleImp, aImp) (getRules imp) ->
      SemAction oImp (aImp type) rImp uImp csImp WO ->
      forall oSpec,
        simRel oImp oSpec ->
        ((simRel (doUpdRegs uImp oImp) oSpec /\ csImp = []) \/
         (exists rleSpec aSpec,
             In (rleSpec, aSpec) (getRules spec) /\
             exists rSpec uSpec,
               SemAction oSpec (aSpec type) rSpec uSpec csImp WO /\
                 simRel (doUpdRegs uImp oImp) (doUpdRegs uSpec oSpec))).

  Theorem simulationZeroAction:
    TraceInclusion (Base imp) (Base spec).
  Proof.
    eapply simulationZeroA; eauto; intros.
    specialize (@simulation _ _ _ _ _ _ H H0 _ H1).
    destruct simulation; auto.
    right.
    dest.
    exists x, x0; split; auto.
    exists x1, x2; split; auto.
    exists (doUpdRegs x2 oSpec); split; auto.
    pose proof (SemAction_NoDup_u H3) as sth.
    destruct (wfBaseModule spec); dest.
    pose proof (simRelGood H1) as sth2.
    apply (f_equal (map fst)) in sth2.
    rewrite ?map_map in *; simpl in *.
    assert (sth3: forall A B, (fun x: (A * B) => fst x) = fst) by
        (intros; extensionality y; intros; auto).
    rewrite <- sth3 in H8.
    rewrite <- sth2 in H8.
    rewrite sth3 in H8.
    pose proof (SemActionUpdSub H3).
    eapply doUpdRegs_UpdRegs; eauto.
  Qed.
End SimulationZeroAction.

Lemma SemAction_if k1 k (e: Bool @# type) (a1 a2: ActionT type k1) (a: type k1 -> ActionT type k) o reads u cs v:
  (if evalExpr e
   then SemAction o (LetAction a1 a) reads u cs v
   else SemAction o (LetAction a2 a) reads u cs v) ->
  SemAction o (IfElse e a1 a2 a) reads u cs v.
Proof.
  case_eq (evalExpr e); intros; inv H0; EqDep_subst.
  - econstructor 7; eauto.
  - econstructor 8; eauto.
Qed.

Lemma SemAction_if_split k1 k (e: Bool @# type) (a1 a2: ActionT type k1) (a: type k1 -> ActionT type k) o reads1 reads2 u1 u2 cs1 cs2 v1 v2 reads u cs v:
  (if evalExpr e
   then SemAction o (LetAction a1 a) reads1 u1 cs1 v1
   else SemAction o (LetAction a2 a) reads2 u2 cs2 v2) ->
  (reads = if evalExpr e then reads1 else reads2) ->
  (u = if evalExpr e then u1 else u2) ->
  (cs = if evalExpr e then cs1 else cs2) ->
  (v = if evalExpr e then v1 else v2) ->
  SemAction o (IfElse e a1 a2 a) reads u cs v.
Proof.
  intros.
  eapply SemAction_if.
  destruct (evalExpr e); subst; auto.
Qed.

Lemma convertLetExprSyntax_ActionT_same o k (e: LetExprSyntax type k):
  SemAction o (convertLetExprSyntax_ActionT e) nil nil nil (evalLetExpr e).
Proof.
  induction e; simpl; try constructor; auto.
  specialize (H (evalLetExpr e)).
  pose proof (SemLetAction (fun v => convertLetExprSyntax_ActionT (cont v)) (@DisjKey_nil_l string _ nil) IHe H) as sth.
  rewrite ?(app_nil_l nil) in sth.
  auto.
  eapply SemAction_if; eauto;
  case_eq (evalExpr pred); intros; subst; repeat econstructor; eauto; unfold not; simpl; intros; auto.
Qed.

Lemma convertLetExprSyntax_ActionT_full k (e: LetExprSyntax type k):
  forall o reads writes cs ret,
    SemAction o (convertLetExprSyntax_ActionT e) reads writes cs ret ->
    reads = nil /\ writes = nil /\ cs = nil /\ ret = (evalLetExpr e).
Proof.
  induction e; simpl; auto; intros; dest; subst.
  - inv H; dest.
    EqDep_subst.
    repeat split; auto.
  - inv H; dest.
    EqDep_subst.
    eapply IHe; eauto.
  - inv H0.
    EqDep_subst.
    apply H in HSemActionCont; dest; subst.
    apply IHe in HSemAction; dest; subst.
    repeat split; auto.
  - apply inversionSemAction in H0; dest.
    destruct (evalExpr pred); dest.
    + apply IHe1 in H1; dest; subst.
      apply H in H2; dest; subst.
      repeat split; auto.
    + apply IHe2 in H1; dest; subst.
      apply H in H2; dest; subst.
      repeat split; auto.
Qed.



Section Simulation.
  Variable imp spec: BaseModule.
  Variable impWf: WfBaseModule imp.
  Variable specWf: WfBaseModule spec.
  Variable NoSelfCalls: NoSelfCallBaseModule spec.
  
  Variable simRel: RegsT -> RegsT -> Prop.
  Variable simRelGood: forall oImp oSpec, simRel oImp oSpec -> getKindAttr oSpec = getKindAttr (getRegisters spec).
  Variable simRelImpGood: forall oImp oSpec, simRel oImp oSpec -> getKindAttr oImp = getKindAttr (getRegisters imp).
  Variable initRel: forall rimp, Forall2 regInit rimp (getRegisters imp) ->
                                 exists rspec, Forall2 regInit rspec (getRegisters spec) /\ simRel rimp rspec.

  Variable simulationRule:
    forall oImp rImp uImp rleImp csImp aImp,
      In (rleImp, aImp) (getRules imp) ->
      SemAction oImp (aImp type) rImp uImp csImp WO ->
      forall oSpec,
        simRel oImp oSpec ->
        ((simRel (doUpdRegs uImp oImp) oSpec /\ csImp = nil) \/
         (exists rleSpec aSpec,
             In (rleSpec, aSpec) (getRules spec) /\
             exists rSpec uSpec,
               SemAction oSpec (aSpec type) rSpec uSpec csImp WO /\
                 simRel (doUpdRegs uImp oImp) (doUpdRegs uSpec oSpec))).

  Variable simulationMeth:
    forall oImp rImp uImp meth csImp sign aImp arg ret,
      In (meth, existT _ sign aImp) (getMethods imp) ->
      SemAction oImp (aImp type arg) rImp uImp csImp ret ->
      forall oSpec,
        simRel oImp oSpec ->
          exists aSpec rSpec uSpec,
            In (meth, existT _ sign aSpec) (getMethods spec) /\
            SemAction oSpec (aSpec type arg) rSpec uSpec csImp ret /\
                simRel (doUpdRegs uImp oImp) (doUpdRegs uSpec oSpec).

  Variable notMethMeth:
    forall oImp rImpl1 uImpl1 meth1 sign1 aImp1 arg1 ret1 csImp1
           rImpl2 uImpl2 meth2 sign2 aImp2 arg2 ret2 csImp2,
      In (meth1, existT _ sign1 aImp1) (getMethods imp) ->
      SemAction oImp (aImp1 type arg1) rImpl1 uImpl1 csImp1 ret1 ->
      In (meth2, existT _ sign2 aImp2) (getMethods imp) ->
      SemAction oImp (aImp2 type arg2) rImpl2 uImpl2 csImp2 ret2 ->
      exists k, In k (map fst uImpl1) /\ In k (map fst uImpl2).
          
  Variable notRuleMeth:
    forall oImp rImpl1 uImpl1 rleImpl1 aImp1 csImp1
           rImpl2 uImpl2 meth2 sign2 aImp2 arg2 ret2 csImp2,
      In (rleImpl1, aImp1) (getRules imp) ->
      SemAction oImp (aImp1 type) rImpl1 uImpl1 csImp1 WO ->
      In (meth2, existT _ sign2 aImp2) (getMethods imp) ->
      SemAction oImp (aImp2 type arg2) rImpl2 uImpl2 csImp2 ret2 ->
      exists k, In k (map fst uImpl1) /\ In k (map fst uImpl2).

  Theorem simulation:
    TraceInclusion (Base imp) (Base spec).
  Proof.
    remember {| baseModule := imp ;
                wfBaseModule := impWf |} as impMod.
    remember {| baseModule := spec ;
                wfBaseModule := specWf |} as specMod.
    assert (Imp: imp = baseModule impMod) by (rewrite HeqimpMod; auto).
    assert (Spec: spec = baseModule specMod) by (rewrite HeqspecMod; auto).
    rewrite Imp, Spec in *.
    eapply simulationGeneral; eauto; intros.
  Qed.
End Simulation.
