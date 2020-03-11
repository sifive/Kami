Require Import Streams.


Require Import Kami.Simulator.CoqSim.Misc.
Require Import Kami.Simulator.CoqSim.TransparentProofs.
Require Import Kami.Simulator.CoqSim.HaskellTypes.
Require Import Kami.Simulator.CoqSim.RegisterFile.
Require Import Kami.Simulator.CoqSim.Eval.

Require Import Kami.AllNotations.
Import Kami.Simulator.CoqSim.HaskellTypes.Notations.

Section EvalAction.

Definition SimReg := (string * {x : _ & fullType eval_Kind x})%type.
Definition SimRegs := list SimReg.

Section Regs.

Variable init_regs : list (string * {x : FullKind & RegInitValT x}).

Variable regs : SimRegs.

Definition kind_consistent := forall r k, 
    (exists v, lookup String.eqb r init_regs = Some (existT _ k v)) <-> (exists v', lookup String.eqb r regs = Some (existT _ k v')).

Variable kc : kind_consistent.

(* helper lemmas *)
Lemma kc_init_sim : forall r k v, lookup String.eqb r init_regs = Some (existT _ k v) -> exists v', lookup String.eqb r regs = Some (existT _ k v').
Proof.
  intros.
  apply kc.
  exists v; auto.
Qed.

Lemma kc_sim_init : forall r k v, lookup String.eqb r regs = Some (existT _ k v) -> exists v', lookup String.eqb r init_regs = Some (existT _ k v').
Proof.
  intros.
  apply kc.
  exists v; auto.
Qed.

Record Update := {
  reg_name : string;
  kind : FullKind;
  init_val : RegInitValT kind;
  new_val : fullType eval_Kind kind;
  lookup_match : lookup String.eqb reg_name init_regs = Some (existT _ kind init_val)
  }.

Definition Updates := list Update.
Definition FileUpdates := list FileUpd.

Fixpoint mkProd(ts : list Type) : Type :=
  match ts with
  | [] => unit
  | T::ts' => (T * mkProd ts')%type
  end.

Class Environment E := {
  envPre  : E -> FileState -> SimRegs -> string -> IO E;
  envPost : E -> FileState -> SimRegs -> string -> IO E
  }.

Definition meth_sig{E}`{Environment E}(sig : Signature) : Type :=
  eval_Kind (fst sig) -> FileState -> SimRegs -> E -> IO (E * (eval_Kind (snd sig))).

Definition dec_sig{E}`{Environment E}(dec : string * Signature) : Type :=
  meth_sig (snd dec).

Fixpoint return_meth{E}`{Environment E}(meth : string)(sig : Signature)(meths : list (string * Signature)) : mkProd (List.map dec_sig meths) -> option (meth_sig sig).
 refine match meths return mkProd (List.map dec_sig meths) -> option (meth_sig sig) with
  | [] => fun _ => None
  | dec::meths' => match string_sigb (meth,sig) dec with
                   | left pf => fun fs => Some _
                   | right _ => fun fs => return_meth _ _ meth sig meths' (snd fs)
                   end
  end.
Proof.
  assert (sig = snd dec).
  rewrite <- pf; auto.
  rewrite H0.
  exact (fst fs).
Defined.

Definition reg_not_found{X} : string -> IO X :=
  fun reg => error ("register " ++ reg ++ " not found.").

Fixpoint eval_ActionT{k}{E}`{Environment E}(env : E)(state : FileState)(meths : list (string * Signature))(updates : Updates)(fupdates : FileUpdates)(a : ActionT eval_Kind k)(a_wf : WfActionT_new init_regs a)(fs : mkProd (List.map dec_sig meths)){struct a} : IO (Updates * FileUpdates * eval_Kind k).
  refine (match a return WfActionT_new init_regs a -> _ with
  | MCall meth s e cont => fun pf => do x <- rf_methcall state meth (existT _ (fst s) (eval_Expr e));
       match x with
      | Some (o, existT k v) => match Kind_dec k (snd s) with
                                | left _ => _
                                | right _ => error ("Type mismatch")
                                end
      | None => match return_meth meth s meths fs with
                | None => error ("Method " ++ meth ++ " not found")
                | Some f => (
                    do p <- f (eval_Expr e) state regs env;
                    eval_ActionT _ _ _ (fst p) state meths updates fupdates (cont (snd p)) _ fs
                    )
                end
      end
  | LetExpr k e cont => fun pf => eval_ActionT _ _ _ env state meths updates fupdates (cont (eval_Expr e)) _ fs
  | LetAction k a cont => fun pf => (
      do p <- eval_ActionT _ _ _ env state meths updates fupdates a _ fs;
      eval_ActionT _ _ _ env state meths (fst (fst p)) (snd (fst p)) (cont (snd p)) _ fs
      )
  | ReadNondet k cont => fun pf => (
      do v <- rand_val_FK k;
      eval_ActionT _ _ _ env state meths updates fupdates (cont v) _ fs
      )
  | ReadReg r k cont => fun pf=> _
  | WriteReg r k e a => fun pf => (* match lookup String.eqb r regs with
                        | None => reg_not_found r
                        | Some p => _
                        end *) _
  | IfElse e k a1 a2 cont => fun pf => let a := if (eval_Expr e) then a1 else a2 in (
      do p <- eval_ActionT _ _ _ env state meths updates fupdates a _ fs;
      eval_ActionT _ _ _ env state meths (fst (fst p)) (snd (fst p)) (cont ((snd p))) _ fs
      )
  | Sys ss a => fun pf => (
      do _ <- eval_list_SysT ss;
      eval_ActionT _ _ _ env state meths updates fupdates a _ fs
      )
  | Return e => fun pf => ret (updates, fupdates, eval_Expr e)
  end a_wf).
Proof.
  (* MCall *)
  - rewrite e0 in v.
    destruct o as [fupd|].
    + exact (eval_ActionT _ _ _ env state meths updates (fupd::fupdates) (cont v) (pf _) fs).
    + exact (eval_ActionT _ _ _ env state meths updates fupdates (cont v) (pf _) fs).
  - apply pf.
  - apply pf.
  - apply pf.
  - apply pf.
  - apply pf.
  (* ReadReg *)
  - destruct (lookup String.eqb r regs) eqn:G.
    + simpl in pf.
      destruct lookup eqn:G' in pf.
      * destruct s0.
        destruct s.
        assert (x = x0).
        ** destruct (kc_init_sim _ G') as [v Hv].
           rewrite Hv in G.
           inversion G; auto.
        ** destruct pf.
           clear G.
           rewrite <- H0, <- H1 in f.
           exact (eval_ActionT _ _ _ env state meths updates fupdates (cont f) (H2 _) fs).
      * destruct pf.
   + exact (reg_not_found r).
  (* WriteReg *)
  - simpl in pf.
    destruct lookup eqn:lk in pf.
    + destruct s.
      destruct pf as [keq pf'].
      rewrite keq in e.
      destruct (lookup String.eqb r regs) eqn:G.
      * destruct s.
        assert (x = x0).
        ** destruct (kc_init_sim _ lk) as [v Hv].
           rewrite Hv in G.
           inversion G.
           reflexivity.
        ** pose (upd := {|
                    reg_name := r;
                    kind := x;
                    init_val := r0;
                    new_val := eval_Expr e;
                    lookup_match := lk
                    |}).
           exact (eval_ActionT _ _ _ env state meths (upd::updates) fupdates a pf' fs).
      * absurd (lookup String.eqb r regs = None).
        ** destruct (kc_init_sim _ lk) as [v Hv].
           rewrite Hv in G.
           discriminate G.
        ** auto.
    + destruct pf.
  - simpl in pf; destruct (eval_Expr e); tauto.
  - apply pf.
  - exact pf.
Defined.

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

Definition eval_RuleT{E}`{Environment E}(env : E)(state : FileState)(meths : list (string * Signature))(r : RuleT)(r_wf : WfActionT_new init_regs (snd r eval_Kind))(fs : mkProd (List.map dec_sig meths)) : IO (Updates * FileUpdates * eval_Kind Void) :=
  eval_ActionT env state meths [] [] ((snd r) eval_Kind) r_wf fs.

Fixpoint do_single_update(upd : Update)(regs : SimRegs) : SimRegs :=
  match regs with
  | [] => []
  | (reg',v')::regs' => if String.eqb (reg_name upd) reg' then (reg', existT _ (kind upd) (new_val upd))::regs' else (reg',v')::do_single_update upd regs'
  end.

Definition do_updates(upds : Updates)(regs : SimRegs) : SimRegs :=
  fold_right do_single_update regs upds.

End Regs.

Section Regs2.

Lemma update_hit : forall init_regs regs k v (upd : Update init_regs), lookup String.eqb (reg_name upd) regs = Some (existT _ k v) -> lookup String.eqb (reg_name upd) (do_single_update upd regs) = Some (existT _ (kind upd) (new_val upd)).
Proof.
  induction regs; intros.
  - discriminate H.
  - simpl do_single_update.
    destruct a.
    destruct String.eqb eqn:G.
    + rewrite lookup_cons.
      rewrite G.
      reflexivity.
    + rewrite lookup_cons.
      rewrite G.
      eapply IHregs.
      rewrite lookup_cons in H.
      rewrite G in H.
      exact H.
Qed.

Lemma update_miss : forall r init_regs regs (upd : Update init_regs), r <> reg_name upd -> lookup String.eqb r (do_single_update upd regs) = lookup String.eqb r regs.
Proof.
  induction regs; intros.
  - auto.
  - simpl do_single_update.
    destruct a.
    destruct String.eqb eqn:G.
    + repeat rewrite lookup_cons.
      rewrite String.eqb_eq in G.
      rewrite G in H.
      rewrite <- String.eqb_neq in H.
      rewrite H.
      auto.
    + repeat rewrite lookup_cons.
      destruct (r =? s).
      * auto.
      * apply IHregs; auto.
Qed.

Lemma lookup_update : forall init_regs regs k x (upd : Update init_regs) r, lookup String.eqb r (do_single_update upd regs) = Some (existT (fun x : FullKind => fullType eval_Kind x) k x) -> exists k' y, lookup String.eqb r regs = Some (existT _ k' y).
Proof.
  induction regs; intros.
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
      * pose (lookup_match upd) as lk.
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
      destruct (lookup_update _ _ _ H) as [k' [y Hy]].
      erewrite update_hit in H.
      * pose (lookup_match upd) as lk.
        rewrite G.
        inversion H.
        eexists; exact lk.
      * exact Hy.
    + rewrite String.eqb_neq in G.
      erewrite update_miss in H; auto.
      destruct (kc_sim_init kc _ H).
      eexists; exact H0.
Qed.

Lemma updates_consistent : forall (init_regs : list RegInitT)(curr_regs : SimRegs)(upds : list (Update init_regs)),
  kind_consistent init_regs curr_regs -> kind_consistent init_regs (do_updates upds curr_regs).
Proof.
  induction upds; intro.
  - exact H.
  - apply update_consistent; auto.
Qed.

Fixpoint eval_Rules{E}`{Environment E}(env : E)(state : FileState)(numRules : nat)(meths : list (string * Signature))(init_regs : list (string * {x : FullKind & RegInitValT x}))(curr_regs : SimRegs)(kc_curr : kind_consistent init_regs curr_regs)(rules : Stream {r : RuleT & WfActionT_new init_regs (snd r eval_Kind)}){struct numRules} : mkProd (List.map dec_sig meths) -> IO unit. refine
  match numRules with
  | 0 => fun fs => error "TIMEOUT"
  | S numRules' => fun fs => match rules with
                            | Cons r rules' => (
                                do env' <- envPre env state curr_regs (fst (projT1 r));
                                do p <- eval_RuleT _ env' state meths (projT1 r) (projT2 r)  fs;
                                do env'' <- envPost env' state curr_regs (fst (projT1 r));
                                do state' <- exec_file_updates state (snd (fst p));
                                eval_Rules _ _  env'' state' numRules' meths init_regs (do_updates (fst (fst p)) curr_regs) _ (rules') fs
                                )
                            end
  end.
Proof.
  - exact kc_curr.
  - apply updates_consistent; auto.
Defined.

Definition initialize_SimRegs(regs : list RegInitT) : SimRegs :=
  List.map (fun '(r,existT k v) => match v return SimReg with
                                   | None => (r,existT _ k (eval_ConstFullT (getDefaultConstFullKind k)))
                                   | Some c => (r,existT _ k (eval_ConstFullT c))
                                   end) regs.

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

Lemma kc_nil : kind_consistent [] [].
Proof.
  intros r k; split; intros []; discriminate.
Qed.

Lemma kc_cons : forall init_regs regs r k v v', kind_consistent init_regs regs -> kind_consistent ((r,(existT _ k v)) :: init_regs) ((r, (existT _ k v')) :: regs).
Proof.
  intros.
  intros r' k'; split; intro; rewrite lookup_cons in *; destruct (r' =? r) eqn:G; destruct H0.
  - inversion H0.
    eexists; auto.
  - apply (kc_init_sim H _ H0).
  - inversion H0.
    eexists; auto.
  - apply (kc_sim_init H _ H0).
Qed.

Lemma init_regs_kc : forall init_regs, kind_consistent init_regs (initialize_SimRegs init_regs).
Proof.
  induction init_regs.
  - exact kc_nil.
  - simpl initialize_SimRegs.
    destruct a.
    destruct s0.
    destruct r; apply kc_cons; auto.
Qed.

Definition eval_Basemodule_rr{E}`{Environment E}(env : E)(args : list (string * string))(rfbs : list RegFileBase)(timeout : nat)(meths : list (string * Signature))(basemod : BaseModule)(wf : WfBaseModule_new eval_Kind basemod) : mkProd (List.map dec_sig meths) -> IO unit. refine (
  match basemod return WfBaseModule_new eval_Kind basemod -> _ with
  | BaseRegFile rf => fun pf fs => _
  | BaseMod regs rules dms =>
      match rules with
      | [] => fun _ _ => error "empty rules"
      | r::rs => fun pf fs => _ (* eval_Rules timeout meths (initialize_SimRegs regs) (unwind_list (r::rs) (@cons_neq _ r rs)) *)
      end
  end wf).
Proof.
  - exact (error "BaseRegFile not simulatable").
  - unfold WfBaseModule_new in pf.
    destruct pf.
    refine (do state <- initialize_files args rfbs;
    eval_Rules env state (timeout * (List.length rules)) meths _ (unwind_list (get_wf_rules _ _ H0) _) fs).
    + apply init_regs_kc.
    + simpl.
      destruct H0; discriminate.
Defined.

Definition eval_BaseMod{E}`{Environment E}(env : E)(args : list (string * string))(rfbs : list RegFileBase)(timeout : nat)(meths : list (string * Signature))(basemod : BaseModule)(wf : WfBaseModule_new eval_Kind basemod) :=
  curry _ (eval_Basemodule_rr env args rfbs timeout meths wf).

End Regs2.

End EvalAction.

Section Eval_Wf.

Definition eval_BaseMod_Wf{E}`{Environment E}(env : E)(args : list (string * string))(rfbs : list RegFileBase)(timeout : nat)(meths : list (string * Signature))(basemod : BaseModule)(wf : WfBaseModule (eval_Kind) basemod) :=
  curry _ (eval_Basemodule_rr env args rfbs timeout meths (WfBaseModule_WfBaseModule_new wf)).

End Eval_Wf.
