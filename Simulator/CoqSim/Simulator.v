Require Import Streams.


Require Import Kami.Simulator.CoqSim.Misc.
Require Import Kami.Simulator.CoqSim.TransparentProofs.
Require Import Kami.Simulator.CoqSim.HaskellTypes.
Require Import Kami.Simulator.CoqSim.RegisterFile.
Require Import Kami.Simulator.CoqSim.Eval.

Require Import Kami.AllNotations.
Import Kami.Simulator.CoqSim.HaskellTypes.Notations.

Section EvalAction.

Definition SimRegs := Map {x : _ & fullType eval_Kind x}.

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

Lemma dep_pair_rewrite{X}{Y : X -> Type} : forall {x x'} (pf : x = x')(y : Y x),
  existT Y x y = existT Y x' (@eq_rect X x Y y x' pf).
Proof.
  intros.
  destruct pf.
  reflexivity.
Qed.

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
  | ReadReg r k cont => fun pf => _
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
  - destruct (map_lookup r regs) eqn:G.
    + pose (@eq_rect FullKind (projT1 s) (fullType eval_Kind) (projT2 s) k).
      assert (projT1 s = k).
      * simpl in pf.
        destruct s.
        simpl.
        destruct (@kc_sim_init _ _ _ G).
        rewrite H0 in pf.
        destruct pf.
        congruence.
      * refine (eval_ActionT _ _ _ env state meths updates fupdates (cont (f H0)) _ fs).
        simpl in pf.
        destruct lookup in pf.
        ** destruct s0.
           destruct pf.
           apply H2.
        ** destruct pf.
    + simpl in pf.
      destruct lookup eqn:G0 in pf.
      * absurd (map_lookup r regs = None).
        ** destruct s.
           destruct (@kc_init_sim _ _ _ G0).
           rewrite H0; discriminate.
        ** exact G.
      * destruct pf.
  (* WriteReg *)
  - destruct (map_lookup r regs) eqn:G.
    + assert (projT1 s = k).
      * simpl in pf.
        destruct s.
        simpl.
        destruct (@kc_sim_init _ _ _ G).
        rewrite H0 in pf.
        destruct pf.
        congruence.
      * assert (exists v, lookup String.eqb r init_regs = Some (existT _ k v)).
        ** simpl in pf.
           destruct s; destruct (@kc_sim_init _ _  _ G).
           rewrite H1 in pf; destruct pf.
           rewrite (dep_pair_rewrite (eq_sym H2)) in H1.
           eexists; exact H1.
        ** pose (upd := {|
                   reg_name := r;
                   kind := k;
                   new_val := eval_Expr e;
                   lookup_match := H1
                        |}).
           refine (eval_ActionT _ _ _ env state meths (upd::updates) fupdates a _ fs).
           simpl in pf.
           destruct lookup in pf.
           *** destruct s0.
               destruct pf.
               exact H3.
           *** destruct pf.
    + simpl in pf.
      destruct lookup eqn:G0 in pf.
      * absurd (map_lookup r regs = None).
        ** destruct s.
           destruct (@kc_init_sim _ _ _ G0).
           rewrite H0; discriminate.
        ** exact G.
      * destruct pf.
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

Definition execute_Rule{E}`{Environment E}(env : E)(init_regs : list RegInitT)(meths : list (string * Signature))(fs : mkProd (List.map dec_sig meths))(rule : RuleT)(wf_rule : WfActionT_new init_regs (snd rule eval_Kind))(state : FileState)(curr_regs : SimRegs)(kc_curr : kind_consistent init_regs curr_regs) : IO (FileState * SimRegs) :=
  do env' <- envPre env state curr_regs (fst rule);
  do p <- @eval_RuleT _ curr_regs kc_curr _ _ env' state meths rule wf_rule fs;
  do env'' <- envPost env' state curr_regs (fst rule);
  do state' <- exec_file_updates state (snd (fst p));
  ret (state', (do_updates (fst (fst p)) curr_regs)).

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