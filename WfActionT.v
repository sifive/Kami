Require Export Bool Ascii String Fin List FunctionalExtensionality Psatz PeanoNat.
Require Export Kami.Syntax.

Inductive Failure :=
  | NativeReg : string -> Failure
  | NativeLetExpr : Failure
  | NativeReadNondet : Failure
  | RegNotFound : string -> Failure
  | HideMethodNotFound : string -> Failure
  | RegKindMismatch : string -> FullKind -> FullKind -> Failure
  | DuplicateMethod : string -> (* Signature -> Signature -> *) Failure
  | DuplicateRegister : string -> FullKind -> FullKind -> Failure
  | DuplicateRule : string -> Failure.

Fixpoint WfActionT_unit {k} (regs : list (string * {x : FullKind & RegInitValT x})) (a : ActionT (fun _ => unit) k) : list Failure :=
  match a with
  | MCall meth s e cont => WfActionT_unit regs (cont tt)
  | LetExpr (SyntaxKind k'') e cont => WfActionT_unit regs (cont tt)
  | LetExpr (NativeKind t c) e cont => NativeLetExpr :: WfActionT_unit regs (cont c)
  | LetAction k a cont => WfActionT_unit regs a ++ WfActionT_unit regs (cont tt)
  | ReadNondet (SyntaxKind k') cont => WfActionT_unit regs (cont tt)
  | ReadNondet (NativeKind t c) cont => NativeReadNondet :: WfActionT_unit regs (cont c)
  | ReadReg r (SyntaxKind k') cont => 
      match lookup String.eqb r regs with
      | Some (existT (SyntaxKind k'') _) => (if Kind_decb k' k'' then [] else [RegKindMismatch r (SyntaxKind k') (SyntaxKind k'')]) ++ WfActionT_unit regs (cont tt)
      | Some (existT (NativeKind t c) _) => [RegKindMismatch r (SyntaxKind k') (NativeKind c)]
      | None => [RegNotFound r]
      end
  | ReadReg r (NativeKind t c) cont => [NativeReg r]
  | WriteReg r (SyntaxKind k') e cont =>
      match lookup String.eqb r regs with
      | Some (existT (SyntaxKind k'') _) => if Kind_decb k' k'' then WfActionT_unit regs cont else RegKindMismatch r (SyntaxKind k') (SyntaxKind k'') :: WfActionT_unit regs cont
      | Some (existT (NativeKind t c) _) => [RegKindMismatch r (SyntaxKind k') (NativeKind c)]
      | None => [RegNotFound r]
      end
  | WriteReg r (NativeKind t c) e cont => NativeReg r :: WfActionT_unit regs cont
  | IfElse cond k' atrue afalse cont => WfActionT_unit regs atrue ++ WfActionT_unit regs afalse ++ WfActionT_unit regs (cont tt)
  | Sys l cont => WfActionT_unit regs cont
  | Return e => []
  end.

Definition WfBaseModule_rules_unit(m : BaseModule) :=
  List.fold_right (fun rule fs => WfActionT_unit (getRegisters m) rule ++ fs) [] (map (fun r => snd r _) (getRules m)).

Definition action_from_MethodT : (string * {x : Signature & MethodT x}) -> {k : _ & ActionT (fun _ => unit) k}.
Proof.
  intros.
  destruct X.
  destruct s0.
  unfold MethodT in m.
  pose (m (fun _ => unit)).
  exists (snd x).
  exact (a tt).
Defined.

Definition WfBaseModule_methods_unit(m : BaseModule) :=
  List.fold_right (fun meth fs => WfActionT_unit (getRegisters m) (projT2 (action_from_MethodT meth)) ++ fs) [] (getMethods m).

Fixpoint find_dups_aux{X}(acc ps : list (string * X)) : list (string * X * X) :=
  match ps with
  | [] => []
  | p::qs => match lookup String.eqb (fst p) acc with
             | Some x => (fst p, snd p, x) :: find_dups_aux acc qs
             | None => find_dups_aux (p::acc) qs
             end
  end.

Definition find_dups{X} : list (string * X) -> list (string * X * X) := find_dups_aux [].

Definition WfBaseModule_unit(m : BaseModule) :=
     map (fun '(s,x1,x2) => DuplicateMethod s (* (projT1 x1) (projT1 x2) *)) (find_dups (getMethods m))
  ++ map (fun '(s,x1,x2) => DuplicateRegister s (projT1 x1) (projT1 x2)) (find_dups (getRegisters m))
  ++ map (fun '(s,x1,x2) => DuplicateRule s) (find_dups (getRules m))
  ++ WfBaseModule_rules_unit m
  ++ WfBaseModule_methods_unit m.

Fixpoint find_overlaps{X}(ps qs : list (string * X)) : list (string * X * X) :=
  match ps with
  | [] => []
  | p::ps' => match lookup String.eqb (fst p) qs with
              | Some x => (fst p,snd p,x) :: find_overlaps ps' qs
              | None => find_overlaps ps' qs
              end
  end.

Fixpoint WfConcatActionT_unit{k}(a : ActionT (fun _ => unit) k)(m : Mod) : list Failure :=
  match a with
  | MCall meth s e cont => (if existsb (String.eqb meth) (getHidden m) then [HideMethodNotFound meth] else [])  ++ WfConcatActionT_unit (cont tt) m
  | LetExpr (SyntaxKind k') e cont => WfConcatActionT_unit (cont tt) m
  | LetExpr (NativeKind t c) e cont => NativeLetExpr :: WfConcatActionT_unit (cont c) m
  | LetAction k a cont => WfConcatActionT_unit a m ++ WfConcatActionT_unit (cont tt) m
  | ReadNondet (SyntaxKind k') cont => WfConcatActionT_unit (cont tt) m
  | ReadNondet (NativeKind t c) cont => NativeReadNondet :: WfConcatActionT_unit (cont c) m
  | ReadReg r (SyntaxKind k') cont => WfConcatActionT_unit (cont tt) m
  | ReadReg r (NativeKind t c) cont => NativeReg r :: WfConcatActionT_unit (cont c) m
  | WriteReg r k e a => WfConcatActionT_unit a m
  | IfElse e k a1 a2 cont => WfConcatActionT_unit a1 m ++ WfConcatActionT_unit a2 m ++ WfConcatActionT_unit (cont tt) m
  | Sys _ a => WfConcatActionT_unit a m
  | Return _ => []
  end.

Definition WfConcat_unit m1 m2 :=
     List.fold_right (fun rule fs => WfConcatActionT_unit rule m2 ++ fs) [] (map (fun r => snd r _) (getAllRules m1))
  ++ List.fold_right (fun meth fs => WfConcatActionT_unit (projT2 meth) m2 ++ fs) [] (map action_from_MethodT (getAllMethods m1)).

Fixpoint WfMod_unit(m : Mod) :=
  match m with
  | Base m => WfBaseModule_unit m
  | HideMeth m s => match lookup String.eqb s (getAllMethods m) with
                    | Some _ => WfMod_unit m
                    | None => HideMethodNotFound s :: WfMod_unit m
                    end
  | ConcatMod m1 m2 =>
         WfMod_unit m1
      ++ WfMod_unit m2
      ++ map (fun '(s,x1,x2) => DuplicateRegister s (projT1 x1) (projT1 x2)) (find_overlaps (getAllRegisters m1) (getAllRegisters m2))
      ++ map (fun '(s,x1,x2) => DuplicateRule s) (find_overlaps (getAllRules m1) (getAllRules m2))
      ++ map (fun '(s,x1,x2) => DuplicateMethod s (* (projT1 x1) (projT1 x2) *)) (find_overlaps (getAllMethods m1) (getAllMethods m2))
      ++ WfConcat_unit m1 m2
      ++ WfConcat_unit m2 m1
  end.

Section Proofs.

Lemma In_map_fst : forall {X Y}(x : X) ps, In x (map fst ps) -> exists y : Y, In (x,y) ps.
Proof.
  induction ps; intros.
  - destruct H.
  - destruct H.
    exists (snd a).
    left.
    destruct a.
    simpl in *; congruence.
    destruct (IHps H) as [y Hy].
    exists y.
    right; exact Hy.
Qed.

Lemma In_lookup : forall {X} str (ps : list (string * X)), In str (map fst ps) -> exists x, lookup String.eqb str ps = Some x.
Proof.
  induction ps; intros.
  - destruct H.
  - destruct H.
    + exists (snd a).
      unfold lookup.
      simpl.
      rewrite H.
      rewrite String.eqb_refl.
      reflexivity.
    + destruct a.
      rewrite lookup_cons.
      destruct String.eqb eqn:G.
      * exists x; auto.
      * auto.
Qed.

Lemma lookup_In : forall {X} str (ps : list (string * X)) x, lookup String.eqb str ps = Some x -> In str (map fst ps).
Proof.
  induction ps.
  - intros; discriminate.
  - intros.
    destruct a.
    rewrite lookup_cons in H.
    destruct String.eqb eqn:G.
    + left.
      rewrite String.eqb_eq in G; simpl; congruence.
    + right.
      apply (IHps x); auto.
Qed.

Lemma find_dups_aux_NoDup : forall {X}(ps acc : list (string * X)), find_dups_aux acc ps = [] -> NoDup (map fst ps) /\ forall str, In str (map fst ps) -> ~ In str (map fst acc).
Proof.
  induction ps; intros.
  - split.
    + constructor.
    + intros.
      destruct H0.
  - split.
    + simpl in H.
      destruct lookup eqn:G in H.
      * discriminate.
      * destruct (IHps _ H).
        constructor.
        ** intro.
           apply (H1 (fst a)).
           exact H2.
           left; auto.
        ** exact H0.
    + simpl in H.
      destruct lookup eqn:G in H.
      * discriminate.
      * intros.
        destruct (IHps _ H).
        intro.
        destruct H0.
        ** destruct (In_lookup str acc H3) as [x Hx].
           rewrite H0 in G.
           rewrite Hx in G.
           discriminate.
        ** apply (H2 str); auto.
           right; auto.
Qed.

Lemma find_dups_NoDups : forall {X}(ps : list (string * X)), find_dups ps = [] -> NoDup (map fst ps).
Proof.
  intros.
  eapply find_dups_aux_NoDup.
  exact H.
Qed.

Lemma WfActionT_unit_correct : forall lret m (a : ActionT _ lret), WfActionT_unit (getRegisters m) a = [] -> WfActionT_new (getRegisters m) a.
Proof.
  induction a; simpl; intros.
  - apply H; destruct x; auto.
  - apply H.
    destruct k.
    + destruct x; auto.
    + discriminate H0.
  - split.
    + apply IHa.
      destruct (app_eq_nil _ _ H0); auto.
    + intro; apply H.
      destruct (app_eq_nil _ _ H0); destruct x; auto.
  - apply H.
    destruct k.
    + destruct x; auto.
    + discriminate.
  - destruct k.
    + destruct lookup eqn:G.
      * destruct s.
        destruct x.
        ** destruct Kind_decb eqn:G0.
           *** split.
               **** rewrite Kind_decb_eq in G0; congruence.
               **** intros []; apply H; auto.
           *** discriminate.
        ** discriminate.
      * discriminate.
    + discriminate.
  - destruct k.
    + destruct lookup eqn:G.
      * destruct s.
        destruct x.
        ** destruct Kind_decb eqn:G0.
           *** split.
               **** rewrite Kind_decb_eq in G0; congruence.
               **** auto.
           *** discriminate.
        ** discriminate.
      * discriminate.
    + discriminate.
  - destruct (app_eq_nil _ _ H0); clear H0.
    destruct (app_eq_nil _ _ H2); clear H2.
    repeat split; auto.
    intros []; auto.
  - auto.
  - exact I.
Qed.

Lemma fold_right_empty_lemma : forall {X Y}(f : X -> list Y)(xs : list X),
  fold_right (fun x ys => f x ++ ys) [] xs = [] -> forall x, In x xs -> f x = [].
Proof.
  induction xs; intros.
  - destruct H0.
  - simpl in H.
    destruct (app_eq_nil _ _ H).
    destruct H0.
    + congruence.
    + auto.
Qed.

Lemma WfBaseModule_rules_unit_In : forall m, WfBaseModule_rules_unit m = [] -> forall rule, In rule (getRules m) -> WfActionT_unit (getRegisters m) (snd rule _) = [].
Proof.
  intros.
  apply (fold_right_empty_lemma _ _ H).
  apply (@in_map _ _ (fun r : string * (forall x : Kind -> Type, ActionT x Void) => snd r (fun _ => unit))); auto.
Qed.

Lemma WfBaseModule_rules_unit_correct : forall m, WfBaseModule_rules_unit m = [] -> forall rule, In rule (getRules m) ->
  WfActionT_new (getRegisters m) (snd rule (fun _ => unit)).
Proof.
  intros.
  apply WfActionT_unit_correct.
  apply WfBaseModule_rules_unit_In; auto.
Qed.

Lemma In_WfRules : forall ty regs rules, (forall rule, In rule rules -> WfActionT_new regs (snd rule ty)) -> WfRules ty regs rules.
Proof.
  induction rules; intros; simpl.
  - exact I.
  - split.
    + apply H.
      left; auto.
    + apply IHrules.
      intros.
      apply H.
      right; auto.
Qed.

Lemma WfBaseModule_methods_unit_In : forall m, WfBaseModule_methods_unit m = [] -> forall meth, In meth (getMethods m) -> WfActionT_unit (getRegisters m) (projT2 (snd meth) _ tt) = [].
Proof.
  intros.
  unfold WfBaseModule_methods_unit in H.
  pose @fold_right_empty_lemma.
  pose (@fold_right_empty_lemma _ _ _ _ H).
  unfold action_from_MethodT in e0.
  pose (e0 meth).
  destruct meth.
  destruct s0.
  simpl in e1.
  apply e1.
  exact H0.
Qed.

Lemma WfBaseModule_methods_unit_correct : forall m, WfBaseModule_methods_unit m = [] -> forall meth, In meth (getMethods m) ->
  WfActionT_new (getRegisters m) (projT2 (snd meth) (fun _ => unit) tt).
Proof.
  intros.
  apply WfActionT_unit_correct.
  apply WfBaseModule_methods_unit_In; auto.
Qed.


Lemma In_WfMethods : forall ty regs meths, (forall (meth : string * {x : Signature & MethodT x}) v, In meth meths -> @WfActionT_new ty regs _ (projT2 (snd meth) _ v)) -> WfMeths ty regs meths.
Proof.
  induction meths; intros; simpl.
  - exact I.
  - split.
    + intro; apply H.
      left; auto.
    + apply IHmeths.
      intros.
      apply H.
      right; auto.
Qed.

Lemma WfBaseModule_unit_correct : forall m, WfBaseModule_unit m = [] -> WfBaseModule_new (fun _ => unit) m.
Proof.
  unfold WfBaseModule_unit, WfBaseModule_new.
  intros.
  destruct (app_eq_nil _ _ H); clear H.
  destruct (app_eq_nil _ _ H1); clear H1.
  destruct (app_eq_nil _ _ H2); clear H2.
  destruct (app_eq_nil _ _ H3); clear H3.
  repeat split.
  - apply In_WfRules.
    intros.
    apply WfBaseModule_rules_unit_correct; auto.
  - apply In_WfMethods.
    intros meth [].
    apply WfBaseModule_methods_unit_correct; auto.
  - apply find_dups_NoDups.
    eapply map_eq_nil.
    exact H0.
  - apply find_dups_NoDups.
    eapply map_eq_nil.
    exact H.
  - apply find_dups_NoDups.
    eapply map_eq_nil.
    exact H1.
Qed.

Lemma find_overlaps_DisjKey : forall {X}(ps qs : list (string * X)), find_overlaps ps qs = [] -> DisjKey ps qs.
Proof.
  induction ps; intros qs Hoverlaps str.
  - left; simpl; auto.
  - simpl in Hoverlaps.
    destruct lookup eqn:G.
    + discriminate.
    + destruct (IHps qs Hoverlaps str).
      * destruct (fst a =? str) eqn:G0.
        ** right.
           intro.
           destruct (In_lookup _ _ H0).
           rewrite String.eqb_eq in G0.
            rewrite G0 in G.
            rewrite H1 in G.
            discriminate.
        ** left.
           intros [|].
           *** rewrite H0 in G0.
               rewrite String.eqb_refl in G0.
               discriminate.
           *** auto.
      * tauto.
Qed.

Lemma WfConcatActionT_unit_correct : forall {lret} m (a : ActionT (fun _ => unit) lret),
  WfConcatActionT_unit a m = [] -> WfConcatActionT_new a m.
Proof.
  induction a; simpl; intros.
  - split.
    + destruct existsb eqn:G.
      * discriminate.
      * Search existsb In.
        intro.
        assert (existsb (String.eqb meth) (getHidden m) = true).
        ** apply existsb_exists.
           exists meth; split.
           *** auto.
           *** apply String.eqb_refl.
        ** rewrite H2 in G; discriminate.
    + destruct x.
      apply H.
      destruct (app_eq_nil _ _ H0); auto.
  - destruct k.
    + destruct x; auto.
    + discriminate.
  - destruct (app_eq_nil _ _ H0); clear H0.
    split.
    + auto.
    + destruct x; auto.
  - destruct k.
    + destruct x; auto.
    + discriminate.
  - destruct k.
    + destruct x; auto.
    + discriminate.
  - auto.
  - destruct (app_eq_nil _ _ H0); clear H0.
    destruct (app_eq_nil _ _ H2); clear H2.
    repeat split.
    + auto.
    + auto.
    + destruct x; auto.
  - auto.
  - exact I.
Qed.

Lemma in_map2 : forall (A B : Type)(f : A -> B)(l : list A)(x : A)(y : B), y = f x -> In x l -> In y (map f l).
Proof.
  intros.
  rewrite H.
  apply in_map; auto.
Qed.

Theorem WfMod_unit_correct : forall m, WfMod_unit m = [] -> WfMod_new (fun _ => unit) m.
Proof.
  induction m; simpl; intro.
  - apply WfBaseModule_unit_correct; auto.
  - destruct lookup eqn:G in H.
    + split.
      * eapply lookup_In.
        exact G.
      * auto.
    + discriminate.
  - destruct (app_eq_nil _ _ H); clear H.
    destruct (app_eq_nil _ _ H1); clear H1.
    destruct (app_eq_nil _ _ H2); clear H2.
    destruct (app_eq_nil _ _ H3); clear H3.
    destruct (app_eq_nil _ _ H4); clear H4.
    destruct (app_eq_nil _ _ H5); clear H5.
    destruct (app_eq_nil _ _ H4); clear H4.
    destruct (app_eq_nil _ _ H6); clear H6.
    repeat split.
    + apply find_overlaps_DisjKey.
      eapply map_eq_nil.
      exact H1.
    + apply find_overlaps_DisjKey.
      eapply map_eq_nil.
      exact H2.
    + apply find_overlaps_DisjKey.
      eapply map_eq_nil.
      exact H3.
    + auto.
    + auto.
    + intros; apply WfConcatActionT_unit_correct.
      apply (@fold_right_empty_lemma _ _ _ _ H5).
      apply (@in_map _ _ (fun r : string * (forall x : Kind -> Type, ActionT x Void) => snd r (fun _ => unit))); auto.
    + intros; apply WfConcatActionT_unit_correct.
      unfold action_from_MethodT in H7.
      destruct v.
      pose (@fold_right_empty_lemma _ _ _ _ H7).
      pose (e (action_from_MethodT meth)).
      destruct meth.
      destruct s0.
      simpl.
      unfold action_from_MethodT in e0.
      simpl in e0.
      apply e0.
      apply (@in_map2 _ _ _ _ ((s, existT MethodT x m))).
      reflexivity.
      exact H6.
    + intros; apply WfConcatActionT_unit_correct.
      apply (@fold_right_empty_lemma _ _ _ _ H4).
      apply (@in_map _ _ (fun r : string * (forall x : Kind -> Type, ActionT x Void) => snd r (fun _ => unit))); auto.
    + intros; apply WfConcatActionT_unit_correct.
      unfold action_from_MethodT in H8.
      destruct v.
      pose (@fold_right_empty_lemma _ _ _ _ H8).
      pose (e (action_from_MethodT meth)).
      destruct meth.
      destruct s0.
      simpl.
      unfold action_from_MethodT in e0.
      simpl in e0.
      apply e0.
      apply (@in_map2 _ _ _ _ ((s, existT MethodT x m))).
      reflexivity.
      exact H6.
Qed.

End Proofs.

Section ParametricTheorems.

Lemma WfActionT_unit_new : forall {k}(regs : list RegInitT)(a : forall ty, ActionT ty k), WfActionT_unit regs (a _) = [] ->
  forall ty, WfActionT_new regs (a ty).
Proof.
Admitted.

Lemma WfBaseModule_unit_new : forall b : BaseModule, WfBaseModule_unit b = [] -> forall ty, WfBaseModule_new ty b.
Proof.
Admitted.

Lemma WfConcatActionT_unit_new : forall {k}(a : forall ty, ActionT ty k)(m : Mod),
  WfConcatActionT_unit (a _) m = [] -> forall ty, WfConcatActionT_new (a ty) m.
Proof.
Admitted.

Lemma WfConcat_unit_new : forall m1 m2, WfConcat_unit m1 m2 = [] -> forall ty, WfConcat_new ty m1 m2.
Proof.
Admitted.

Lemma WfMod_unit_new : forall m, WfMod_unit m = [] -> forall ty, WfMod_new ty m.
Proof.
Admitted.

End ParametricTheorems.