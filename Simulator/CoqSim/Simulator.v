Require Import Streams.

Require Import Kami.AllNotations.

Require Import Kami.Simulator.CoqSim.Misc.
Require Import Kami.Simulator.CoqSim.TransparentProofs.
Require Import Kami.Simulator.CoqSim.SimTypes.
Require Import Kami.Simulator.CoqSim.HaskellTypes.
Require Import Kami.Simulator.CoqSim.RegisterFile.
Require Import Kami.Simulator.CoqSim.Eval.

Section EvalAction.

Variable Word : nat -> Type.
Variable Vec : nat -> Type -> Type.
Variable Map : Type -> Type.
Variable M : Type -> Type.

Context `{IsWord Word}.
Context `{IsVector Vec}.
Context `{StringMap Map}.
Context `{IOMonad Word Vec M}.

Notation "'do' x <- y ; cont" := (bind y (fun x => cont)) (at level 20).

(* Variable KindInfo : Map string FullKind 
Hypothesis ActionGood: forall Write r k in a, KindInfo r = k /\ forall Read r k in a, KindInfo r = k
Lemma: SimRegGood: (r, k) in SimReg -> KindInfo r = k
Theorem: ActionSimRegGood: forall Write r k in a, (r, k') in SimReg -> k = k' *)

Definition eval_K := eval_Kind Word Vec.

Definition eval_E := @eval_Expr Word Vec _ _.

Definition SimReg := (string * {x : _ & fullType eval_K x})%type.
Definition SimRegs := list SimReg.

Section Regs.

Variable regs : SimRegs.

Record Update := {
  reg_name : string;
  kind : FullKind;
  old_val : fullType eval_K kind;
  new_val : fullType eval_K kind;
  lookup_match : lookup String.eqb reg_name regs = Some (existT _ kind old_val)
  }.

Definition Updates := list Update.
Definition FileUpdates := list (@FileUpd Vec Word).

Fixpoint mkProd(ts : list Type) : Type :=
  match ts with
  | [] => unit
  | T::ts' => (T * mkProd ts')%type
  end.

Class Environment E := {
  envPre  : E -> FileState (V := Vec) (W := Word) (M := Map) -> SimRegs -> string -> M E;
  envPost : E -> FileState (V := Vec) (W := Word) (M := Map) -> SimRegs -> string -> M E
  }.

Definition meth_sig{E}`{Environment E}(sig : Signature) : Type :=
  eval_K (fst sig) -> FileState (V := Vec) (W := Word) (M := Map) -> SimRegs -> E -> M (E * (eval_K (snd sig))).

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
  rewrite H6.
  exact (fst fs).
Defined.

Definition reg_not_found{X} : string -> M X :=
  fun reg => error ("register " ++ reg ++ " not found.").

Fixpoint wf_action{k}(a : ActionT eval_K k) : Prop :=
  match a with
  | MCall meth s e cont => forall x, wf_action (cont x)
  | LetExpr k e cont => forall x, wf_action (cont x)
  | LetAction k a cont => (wf_action a /\ forall x, wf_action (cont x))
  | ReadNondet k cont => forall x, wf_action (cont x)
  | ReadReg r k' cont => match lookup String.eqb r regs with
                         | None => False
                         | Some (existT k'' _) => k' = k'' /\ forall x, wf_action (cont x)
                         end
  | WriteReg r k' e a => match lookup String.eqb r regs with
                         | None => False
                         | Some (existT k'' _) => k' = k'' /\ wf_action a
                         end
  | IfElse e k1 a1 a2 cont => (wf_action a1 /\ wf_action a2 /\ forall x, wf_action (cont x))
  | Sys _ a => wf_action a
  | Return _ => True
  end.

Fixpoint eval_ActionT{k}{E}`{Environment E}(env : E)(state : @FileState Vec Word Map)(meths : list (string * Signature))(updates : Updates)(fupdates : FileUpdates)(a : ActionT eval_K k)(a_wf : wf_action a)(fs : mkProd (List.map dec_sig meths)){struct a} : M (Updates * FileUpdates * eval_K k).
  refine (match a return wf_action a -> _ with
  | MCall meth s e cont => fun pf => 
       match rf_methcall state meth (existT _ (fst s) (eval_E e)) with
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
  | ReadReg r k cont => fun pf=> match lookup String.eqb r regs with
                        | None => reg_not_found r
                        | Some p => _
                        end
  | WriteReg r k e a => fun pf => match lookup String.eqb r regs with
                        | None => reg_not_found r
                        | Some p => _
                        end
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
  - destruct p.
    simpl in pf.
    destruct lookup in pf.
    * destruct s; destruct pf as [keq pf'].
      rewrite <- keq in f0.
      exact (eval_ActionT _ _ _ env state meths updates fupdates (cont f0) (pf' _) fs).
    * destruct pf.
  (* WriteReg *)
  - simpl in pf.
    destruct lookup eqn:lk in pf.
    * destruct s.
      destruct pf as [keq pf'].
      rewrite keq in e.
      pose (upd := {|
        reg_name := r;
        kind := x;
        old_val := f;
        new_val := eval_Expr e;
        lookup_match := lk
        |}).
      exact (eval_ActionT _ _ _ env state meths (upd::updates) fupdates a pf' fs).
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

Definition eval_RuleT{E}`{Environment E}(env : E)(state : FileState)(meths : list (string * Signature))(r : RuleT)(r_wf : wf_action (snd r eval_K))(fs : mkProd (List.map dec_sig meths)) : M (Updates * FileUpdates * eval_K Void) :=
  eval_ActionT env state meths [] [] ((snd r) eval_K) r_wf fs.

Fixpoint do_single_update(upd : Update)(regs : SimRegs) : SimRegs :=
  match regs with
  | [] => []
  | (reg',v')::regs' => if String.eqb (reg_name upd) reg' then (reg', existT _ (kind upd) (new_val upd))::regs' else (reg',v')::do_single_update upd regs'
  end.

Definition do_updates(upds : Updates)(regs : SimRegs) : SimRegs :=
  fold_right do_single_update regs upds.

End Regs.

Section Regs2.

Definition consistent(regs1 regs2 : SimRegs) := forall r k v,
  lookup String.eqb r regs1 = Some (existT _ k v) -> exists v', lookup String.eqb r regs2 = Some (existT _ k v').

Lemma consistent_refl : forall regs, consistent regs regs.
Proof.
  intros regs r k v lk.
  exists v; auto.
Qed.

Lemma consistent_trans : forall regs1 regs2 regs3, consistent regs1 regs2 -> consistent regs2 regs3 -> consistent regs1 regs3.
Proof.
  intros regs1 regs2 regs3 cons12 cons23 r k v Hv.
  destruct (cons12 r k v) as [v' Hv']; auto.
  destruct (cons23 r k v') as [v'' Hv'']; auto.
  exists v''; auto.
Qed.

Lemma lookup_cons : forall K V (eqb : K -> K -> bool) k k' v (ps : list (K*V)), lookup eqb k ((k',v)::ps) =
  if eqb k k' then Some v else lookup eqb k ps.
Proof.
  intros.
  unfold lookup.
  unfold find.
  simpl.
  destruct (eqb k k'); auto.
Qed.

Lemma consistent_cons_cong : forall (regs1 regs2 : SimRegs)(r : SimReg), consistent regs1 regs2 -> consistent (r::regs1) (r::regs2).
Proof.
  intros regs1 regs2 r cons12 s k v Hv.
  destruct r.
  rewrite lookup_cons in Hv.
  rewrite lookup_cons.
  destruct (String.eqb s s0).
  - exists v; auto.
  - destruct (cons12 s k v); auto.
    exists x; auto.
Qed.

(*
Lemma consistent_do_update_cong : forall (regs1 regs2 : SimRegs)(upd : Update regs1),
  consistent regs1 regs2 -> consistent (do_single_update upd regs1) (do_single_update upd regs2).
Proof.
Admitted.

Lemma update_consistent : forall (regs : SimRegs)(upd : Update regs), consistent regs (do_single_update upd regs).
Proof.
  intros regs upd r k v Hv.
  pose (lookup_match upd).
  Print Update.
*)

Lemma wf_consistent_stable : forall {k} (a : ActionT eval_K k) regs1 regs2, consistent regs1 regs2 -> wf_action regs1 a -> wf_action regs2 a.
Proof.
  intros.
  induction a; simpl.
Admitted.

Lemma updates_consistent : forall (regs : SimRegs)(upds : Updates regs), consistent regs (do_updates upds regs).
Proof.
  intros; induction upds; simpl.
  - apply consistent_refl.
  - apply (@consistent_trans _ (do_single_update a regs) _).
Admitted.

Lemma wf_updates_stable{k} : forall (regs : SimRegs)(upds : Updates regs)(a : ActionT eval_K k),
  wf_action regs a -> wf_action (do_updates upds regs) a.
Proof.
  intros.
  apply (@wf_consistent_stable _ _ regs).
  - apply updates_consistent.
  - auto.
Qed.

Definition maintain_wf{k} regs (upds : Updates regs) (a : ActionT eval_K k) : {r : RuleT & wf_action regs a} -> {r : RuleT & wf_action (do_updates upds regs) a}.
Admitted.

(* TODO: FIGURE OUT IF THE ENV NEEDS TO BE UPDATED AT SOME POINT *)
Check envPre.
Print RuleT.

Fixpoint eval_Rules{E}`{Environment E}(env : E)(state : FileState (V := Vec) (W := Word) (M := Map))(timeout : nat)(meths : list (string * Signature))(init_regs : SimRegs)(rules : Stream {r : RuleT & wf_action init_regs (snd r eval_K)}){struct timeout} : mkProd (List.map dec_sig meths) -> M unit. refine
  match timeout with
  | 0 => fun fs => error "TIMEOUT"
  | S timeout' => fun fs => match rules with
                            | Cons r rules' => (
                                do env' <- envPre env state init_regs (fst (projT1 r));
                                do p <- eval_RuleT init_regs env' state meths (projT1 r) (projT2 r)  fs;
                                do env'' <- envPost env' state init_regs (fst (projT1 r));
                                eval_Rules _ _  env'' (exec_file_updates state (snd (fst p))) timeout' meths (do_updates (fst (fst p)) init_regs) (Streams.map _ rules') fs
                                )
                            end
  end.
Proof.
  intros [rule wf].
  exists rule.
  apply wf_updates_stable; auto.
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

Fixpoint wf_rules(regs : SimRegs)(rules : list RuleT) :=
  match rules with
  | [] => True
  | r::rs => wf_action regs (snd r eval_K) /\ wf_rules regs rs
  end.

Definition wf_bm(basemod : BaseModule) : Prop :=
  match basemod with
  | BaseRegFile rf => False
  | BaseMod regs rules dms => wf_rules (initialize_SimRegs regs) rules
  end.

Definition get_wf_rules : forall regs rules, wf_rules (initialize_SimRegs regs) rules -> 
  list {r : RuleT & wf_action (initialize_SimRegs regs) (snd r eval_K)}.
Proof.
  intros.
  induction rules.
  - exact [].
  - simpl in H5; destruct H5.
    exact ((existT _ a H5)::IHrules H6).
Defined.

Definition eval_Basemodule_rr{E}`{Environment E}(env : E)(args : list (string * string))(rfbs : list RegFileBase)(timeout : nat)(meths : list (string * Signature))(basemod : BaseModule)(wf : wf_bm basemod) : mkProd (List.map dec_sig meths) -> M unit. refine (
  match basemod return wf_bm basemod -> _ with
  | BaseRegFile rf => fun pf fs => _
  | BaseMod regs rules dms =>
      match rules with
      | [] => fun _ _ => error "empty rules"
      | r::rs => fun pf fs => _ (* eval_Rules timeout meths (initialize_SimRegs regs) (unwind_list (r::rs) (@cons_neq _ r rs)) *)
      end
  end wf).
Proof.
  - destruct pf.
  - unfold wf_bm in pf.
    refine (do state <- initialize_files args rfbs;
    eval_Rules env state timeout meths (initialize_SimRegs regs) (unwind_list (get_wf_rules _ _ pf) _) fs).
    simpl.
    destruct pf; discriminate.
Defined.

Definition eval_BaseMod{E}`{Environment E}(env : E)(args : list (string * string))(rfbs : list RegFileBase)(timeout : nat)(meths : list (string * Signature))(basemod : BaseModule)(wf : wf_bm basemod) :=
  curry _ (eval_Basemodule_rr env args rfbs timeout meths basemod wf).

End Regs2.

End EvalAction.

Definition eval_BaseMod_Haskell := @eval_BaseMod HWord HVec HMap IO _ _ _ _ _ _.