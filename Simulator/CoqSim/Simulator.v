Require Import Streams.


Require Import Kami.Simulator.CoqSim.Misc.
Require Import Kami.Simulator.CoqSim.TransparentProofs.
Require Import Kami.Simulator.CoqSim.HaskellTypes.
Require Import Kami.Simulator.CoqSim.RegisterFile.
Require Import Kami.Simulator.CoqSim.Eval.

Require Import Kami.AllNotations.
Require Import Kami.Lib.NatStr.
Import Kami.Simulator.CoqSim.HaskellTypes.Notations.

Section EvalAction.

Definition SimRegs := Map {x : _ & fullType eval_Kind x}.

Definition KamiState := (SimRegs * FileState)%type.

Section Regs.

Variable init_regs : list (string * {x : FullKind & RegInitValT x}).

Variable regs : SimRegs.

Definition kind_consistent := forall r k, 
    (exists v, lookup String.eqb r init_regs = Some (existT _ k v)) <-> (exists v', map_lookup r regs = Some (existT _ k v')).

Variable kc : kind_consistent.

(* helper lemmas *)
Lemma kc_init_sim : forall r k v, lookup String.eqb r init_regs = Some (existT _ k v) -> exists v',  map_lookup r regs = Some (existT _ k v').  
Proof.
  intros.
  apply kc.
  exists v; auto.
Qed.

Lemma kc_sim_init : forall r k v, map_lookup r regs = Some (existT _ k v) -> exists v', lookup String.eqb r init_regs = Some (existT _ k v').
Proof.
  intros.
  apply kc.
  exists v; auto.
Qed.

Record Update := {
  reg_name : string;
  kind : FullKind;
  new_val : fullType eval_Kind kind;
  lookup_match : exists v, lookup String.eqb reg_name init_regs = Some (existT _ kind v)
  }.

Definition Updates := list Update.
Definition FileUpdates := list FileUpd.

(*
Fixpoint mkProd(ts : list Type) : Type :=
  match ts with
  | [] => unit
  | T::ts' => (T * mkProd ts')%type
  end.
*)

Definition meth_sig(sig : Signature) : Type :=
  eval_Kind (fst sig) -> KamiState -> IO (eval_Kind (snd sig)).

Definition return_meth(meth_name : string)(sig : Signature)(meths : Map {sig : Signature & meth_sig sig}) : option (meth_sig sig). refine
  match map_lookup meth_name meths with
  | Some (existT sig' meth) => _
  | None => None
  end.
Proof.
  destruct (Signature_decb sig sig') eqn:G.
  - rewrite Signature_decb_eq in G.
    rewrite G; exact (Some meth).
  - exact None.
Defined.

Definition reg_not_found{X} : string -> IO X :=
  fun reg => error ("register " ++ reg ++ " not found.").

Lemma dep_pair_rewrite{X}{Y : X -> Type} : forall {x x'} (pf : x = x')(y : Y x),
  existT Y x y = existT Y x' (@eq_rect X x Y y x' pf).
Proof.
  intros.
  destruct pf.
  reflexivity.
Qed.

Fixpoint eval_ActionT{k}(state : FileState)(updates : Updates)(fupdates : FileUpdates)(a : ActionT eval_Kind k)(a_wf : WfActionT_new init_regs a)(ms : Map {sig : Signature & meth_sig sig}){struct a} : IO (Updates * FileUpdates * eval_Kind k).
  refine (match a return WfActionT_new init_regs a -> _ with
  | MCall meth s e cont => fun pf => do x <- rf_methcall state meth (existT _ (fst s) (eval_Expr e));
       match x with
      | Some (o, existT k v) => match Kind_dec k (snd s) with
                                | left _ => _
                                | right _ => error ("Type mismatch")
                                end
      | None => match return_meth meth s ms with
                | None => error ("Method " ++ meth ++ " not found")
                | Some f => (
                    do p <- f (eval_Expr e) (regs,state);
                    eval_ActionT _ state updates fupdates (cont p) _ ms
                    )
                end
      end
  | LetExpr k e cont => fun pf => eval_ActionT _ state updates fupdates (cont (eval_Expr e)) _ ms
  | LetAction k a cont => fun pf => (
      do p <- eval_ActionT _ state updates fupdates a _ ms;
      eval_ActionT _ state (fst (fst p)) (snd (fst p)) (cont (snd p)) _ ms
      )
  | ReadNondet k cont => fun pf => (
      do v <- rand_val_FK k;
      eval_ActionT _ state updates fupdates (cont v) _ ms
      )
  | ReadReg r k cont => fun pf => _
  | WriteReg r k e a => fun pf => (* match lookup String.eqb r regs with
                        | None => reg_not_found r
                        | Some p => _
                        end *) _
  | IfElse e k a1 a2 cont => fun pf => let a := if (eval_Expr e) then a1 else a2 in (
      do p <- eval_ActionT _ state updates fupdates a _ ms;
      eval_ActionT _ state (fst (fst p)) (snd (fst p)) (cont ((snd p))) _ ms
      )
  | Sys ss a => fun pf => (
      do _ <- eval_list_SysT ss;
      eval_ActionT _ state updates fupdates a _ ms
      )
  | Return e => fun pf => ret (updates, fupdates, eval_Expr e)
  end a_wf).
Proof.
  (* MCall *)
  - rewrite e0 in v.
    destruct o as [fupd|].
    + exact (eval_ActionT _ state updates (fupd::fupdates) (cont v) (pf _) ms).
    + exact (eval_ActionT _ state updates fupdates (cont v) (pf _) ms).
  - apply pf.
  - apply pf.
  - apply pf.
  - apply pf.
  - apply pf.
  (* ReadReg *)
  - destruct (map_lookup r regs) eqn:G.
    + pose (@eq_rect FullKind (projT1 s) (fullType eval_Kind) (projT2 s) k).
      assert (projT1 s = k).
      * simpl in pf.
        destruct s.
        simpl.
        destruct (@kc_sim_init _ _ _ G).
        rewrite H in pf.
        destruct pf.
        congruence.
      * refine (eval_ActionT _ state updates fupdates (cont (f H)) _ ms).
        simpl in pf.
        destruct lookup in pf.
        ** destruct s0.
           destruct pf.
           apply H1.
        ** destruct pf.
    + simpl in pf.
      destruct lookup eqn:G0 in pf.
      * absurd (map_lookup r regs = None).
        ** destruct s.
           destruct (@kc_init_sim _ _ _ G0).
           rewrite H; discriminate.
        ** exact G.
      * destruct pf.
  (* WriteReg *)
  - destruct (map_lookup r regs) eqn:G.
    + assert (projT1 s = k).
      * simpl in pf.
        destruct s.
        simpl.
        destruct (@kc_sim_init _ _ _ G).
        rewrite H in pf.
        destruct pf.
        congruence.
      * assert (exists v, lookup String.eqb r init_regs = Some (existT _ k v)).
        ** simpl in pf.
           destruct s; destruct (@kc_sim_init _ _  _ G).
           rewrite H0 in pf; destruct pf.
           rewrite (dep_pair_rewrite (eq_sym H1)) in H0.
           eexists; exact H0.
        ** pose (upd := {|
                   reg_name := r;
                   kind := k;
                   new_val := eval_Expr e;
                   lookup_match := H0
                        |}).
           refine (eval_ActionT _ state (upd::updates) fupdates a _ ms).
           simpl in pf.
           destruct lookup in pf.
           *** destruct s0.
               destruct pf.
               exact H2.
           *** destruct pf.
    + simpl in pf.
      destruct lookup eqn:G0 in pf.
      * absurd (map_lookup r regs = None).
        ** destruct s.
           destruct (@kc_init_sim _ _ _ G0).
           rewrite H; discriminate.
        ** exact G.
      * destruct pf.
  - simpl in pf; destruct (eval_Expr e); tauto.
  - apply pf.
  - exact pf.
Defined.

(*
Fixpoint curried(X : Type)(ts : list Type) : Type :=
  match ts with
  | [] => X
  | T::ts' => T -> curried X ts'
  end.

Fixpoint curry(X : Type)(ts : list Type) : (mkProd ts -> X) -> curried X ts :=
  match ts return (mkProd ts -> X) -> curried X ts with
  | [] => fun f => f tt
  | T::ts' => fun f t => curry ts' (fun xs => f (t,xs))
  end.
*)

Definition eval_RuleT(state : FileState)(r : RuleT)(r_wf : WfActionT_new init_regs (snd r eval_Kind))(ms : Map {sig : Signature & meth_sig sig}) : IO (Updates * FileUpdates * eval_Kind Void) :=
  eval_ActionT state [] [] ((snd r) eval_Kind) r_wf ms.

Definition do_single_update(upd : Update)(regs : SimRegs) : SimRegs :=
  insert (reg_name upd) (existT _ (kind upd) (new_val upd)) regs.

Definition do_updates(upds : Updates)(regs : SimRegs) : SimRegs :=
  fold_right do_single_update regs upds.

End Regs.

Section Regs2.

Lemma update_hit : forall init_regs regs k v (upd : Update init_regs), map_lookup (reg_name upd) regs = Some (existT _ k v) -> map_lookup (reg_name upd) (do_single_update upd regs) = Some (existT _ (kind upd) (new_val upd)).
Proof.
  intros.
  unfold do_single_update.
  rewrite insert_lookup_hit; auto.
Qed.

Lemma update_miss : forall r init_regs regs (upd : Update init_regs), r <> reg_name upd -> map_lookup r (do_single_update upd regs) = map_lookup r regs.
Proof.
  intros.
  unfold do_single_update.
  rewrite insert_lookup_miss; auto.
Qed.

(*
Lemma lookup_update : forall init_regs regs k x (upd : Update init_regs) r, map_lookup r (do_single_update upd regs) = Some (existT (fun x : FullKind => fullType eval_Kind x) k x) -> exists k' y, map_lookup r regs = Some (existT _ k' y).
Proof.
  intros.
  pose (lookup_match upd).
  - discriminate H.
  - simpl do_single_update in H.
    destruct a.
    destruct (reg_name upd =? s).
    + rewrite lookup_cons in H.
      rewrite lookup_cons.
      destruct (r =? s).
      * destruct s0; repeat eexists; reflexivity.
      * repeat eexists; exact H.
    + rewrite lookup_cons in H.
      rewrite lookup_cons.
      destruct (r =? s).
      * destruct s0; repeat eexists; reflexivity.
      * eapply IHregs.
        exact H.
Qed.



Lemma lookup_update : forall init_regs regs k x (upd : Update init_regs) r, map_lookup r (do_single_update upd regs) = Some (existT (fun x : FullKind => fullType eval_Kind x) k x) -> exists k' y, map_lookup r regs = Some (existT _ k' y).
Proof.
  intros.
  destruct upd.
*)

Lemma update_consistent : forall (curr_regs : SimRegs)(init_regs : list RegInitT)(upd : Update init_regs),
  kind_consistent init_regs curr_regs -> kind_consistent init_regs (do_single_update upd curr_regs).
Proof.
  intros curr_regs init_regs upd kc r k.
  split; intros [].
  - destruct (String.eqb r (reg_name upd)) eqn:G.
    + rewrite String.eqb_eq in G.
      rewrite G.
      destruct (kc_init_sim kc _ H).
      erewrite update_hit.
      * destruct (lookup_match upd) as [v lk].
        rewrite <- G in lk.
        rewrite H in lk.
        inversion lk.
        rewrite H2 in *.
        eexists; auto.
      * rewrite <- G.
        destruct (kc_init_sim kc _ H).
        exact H0.
    + rewrite String.eqb_neq in G.
      erewrite update_miss; auto.
      apply kc.
      eexists; exact H.
  - destruct (String.eqb r (reg_name upd)) eqn:G.
    + rewrite String.eqb_eq in G.
      rewrite G in H.
      destruct (lookup_match upd).
      destruct (@kc_init_sim _ _ kc _ _ _ H0).
      erewrite update_hit in H.
      * destruct (lookup_match upd) as [v lk].
        rewrite G.
        inversion H.
        eexists; exact lk.
      * exact H1.
    + rewrite String.eqb_neq in G.
      erewrite update_miss in H; auto.
      destruct (kc_sim_init kc H).
      eexists; exact H0.
Qed.

Lemma updates_consistent : forall (init_regs : list RegInitT)(curr_regs : SimRegs)(upds : list (Update init_regs)),
  kind_consistent init_regs curr_regs -> kind_consistent init_regs (do_updates upds curr_regs).
Proof.
  induction upds; intro.
  - exact H.
  - apply update_consistent; auto.
Qed.

Definition evaluated_Rule init_regs := forall (st : KamiState), kind_consistent init_regs (fst st) -> Map {sig : Signature & meth_sig sig} -> IO KamiState.

Definition eval_Rule : forall init_regs (r : RuleT), WfActionT_new init_regs (snd r eval_Kind) -> evaluated_Rule init_regs :=
    fun init_regs r wf st kc methods => (
      do p <- @eval_RuleT init_regs (fst st) kc (snd st) r wf methods;
      let regs := @do_updates _ (fst (fst p)) (fst st) in
      do state <- exec_file_updates (snd st) (snd (fst p));
      ret (regs, state)
      ).

Definition eval_RegInitValT : {k : FullKind & RegInitValT k} -> {k : FullKind & fullType eval_Kind k} :=
  fun '(existT k o) => match o with
                         | None => existT _ k (eval_ConstFullT (getDefaultConstFullKind k))
                         | Some c => existT _ k (eval_ConstFullT c)
                         end.

Definition initialize_SimRegs(regs : list RegInitT) : SimRegs := map_of_list (
  List.map (fun '(r,p) => (r, eval_RegInitValT p)) regs).

Lemma lookup_map : forall {V V'}(f : V -> V')(ps : list (string * V)) x v, lookup String.eqb x ps = Some v -> lookup String.eqb x (map (fun '(r,v') => (r, f v')) ps) = Some (f v).
Proof.
  induction ps; intros.
  - discriminate.
  - simpl.
    destruct a.
    rewrite lookup_cons in *.
    destruct (x =? s).
    + inversion H; auto.
    + apply IHps; auto.
Qed.

Lemma lookup_map_back : forall {V V'}(f : V -> V')(ps : list (string * V)) x v',
  lookup String.eqb x (map (fun '(r,v) => (r, f v)) ps) = Some v' ->
  exists v, f v = v' /\ lookup String.eqb x ps = Some v.
Proof.
  induction ps; intros.
  - discriminate.
  - destruct a.
    simpl in H.
    rewrite lookup_cons in *.
    destruct (x =? s).
    + exists v; inversion H; auto.
    + apply IHps; auto.
Qed.

Lemma cons_neq{X}(x : X)(xs : list X) : x::xs <> [].
Proof.
  discriminate.
Qed.

Definition get_wf_rules{ty} : forall init_regs rules, WfRules ty init_regs rules -> 
  list {r : RuleT & WfActionT_new init_regs (snd r ty)}.
Proof.
  intros.
  induction rules.
  - exact [].
  - simpl in H; destruct H.
    exact ((existT _ a H) :: (IHrules H0)).
Defined.

Lemma init_regs_kc : forall init_regs, kind_consistent init_regs (initialize_SimRegs init_regs).
Proof.
  intros; intros r k; split.
  - intros [v Hv].
    unfold initialize_SimRegs.
    rewrite map_of_list_lookup.
    rewrite (lookup_map eval_RegInitValT init_regs r Hv).
    unfold eval_RegInitValT.
    destruct v.
    simpl.
    + exists (eval_ConstFullT c); reflexivity.
    + exists (eval_ConstFullT (getDefaultConstFullKind k)); reflexivity.
  - intros [v Hv].
    unfold initialize_SimRegs in Hv.
    rewrite map_of_list_lookup in Hv.
    destruct (lookup_map_back eval_RegInitValT init_regs r Hv) as [[k' x] [Hx1 Hx2]].
    unfold eval_RegInitValT in Hx1.
    destruct x.
    + inversion Hx1.
      eexists.
      rewrite Hx2.
      reflexivity.
    + inversion Hx1.
      eexists.
      rewrite Hx2.
      rewrite <- H0.
      reflexivity.
Qed.

End Regs2.

End EvalAction.

Section SimAPI.

Definition init_state(m : Mod)(args : list (string * string)) : IO KamiState :=
  let init_regs := getAllRegisters m in
  let '(_,(rfs,_)) := separateModRemove m in
  let regs := initialize_SimRegs init_regs in
    do s <- initialize_files args rfs;
    ret (regs,s).

Print evaluated_Rule.

Definition sim_step{init_regs}(r : evaluated_Rule init_regs) : forall st : KamiState,
  kind_consistent init_regs (fst st) -> Map {sig : Signature & meth_sig sig} -> IO KamiState :=
  r.

End SimAPI.
