Require Import Coq.Lists.List. Import ListNotations.
  
Axiom one : forall {T}, (T -> Prop) -> list T -> Prop.
Axiom kleene : forall {T}, (list T -> Prop) -> list T -> Prop.
Axiom plus : forall {T}, (list T -> Prop) -> list T -> Prop.
Axiom app : forall {T}, (list T -> Prop) -> (list T -> Prop) -> list T -> Prop.
Axiom either : forall {T}, (list T -> Prop) -> (list T -> Prop) -> list T -> Prop.
Axiom maybe : forall {T}, (list T -> Prop) -> list T -> Prop.
Local Notation "x ^*" := (kleene x) (at level 50).
Local Notation "x ^+" := (plus x) (at level 50).
Local Infix "+++" := app (at level 60).

Module List. Section __.
  Context {T : Type}.
    (* Module interleave.
    Inductive interleave : list T -> list T -> list T -> Prop :=
    | nil                                      : interleave     nil    nil    nil
    | left  x xs ys zs (_:interleave xs ys zs) : interleave (cons x xs) ys (cons x zs)
    | right y xs ys zs (_:interleave xs ys zs) : interleave (cons y xs) ys (cons y zs).
    End interleave.
  Notation interleave := interleave.interleave. *)

  (*
  Definition interleave_body interleave (zs xs ys : list T) : Prop :=
    match xs,ys with
    | [],_ => ys = zs
    | _,[] => xs = zs
    | x::xs,y::ys =>
        match zs with
        | [] => False
        | cons z zs => (z = x /\ interleave zs xs ys) \/ (z = y /\ interleave zs xs ys)
        end
    end. 
  *)

  Definition interleave_body interleave (zs xs ys : list T) : Prop :=
    match zs with
    | nil => xs = nil /\ zs = nil
    | cons z zs' =>
        (exists xs', xs = cons z xs' /\ interleave zs' xs' ys ) \/
        (exists ys', ys = cons z ys' /\ interleave zs' xs  ys')
    end.
  Definition interleave (xs ys zs : list T) : Prop :=
    (fix interleave zs := interleave_body interleave zs) zs xs ys.

  Lemma interleave_rcons z zs xs ys y (H : z = y) (HH : interleave xs ys zs) : interleave xs (y::ys) (z::zs).
  Proof. subst; cbn; eauto. Qed.
  Lemma interleave_lcons z zs xs ys x (H : z = x) (HH : interleave xs ys zs) : interleave (x::xs) ys (z::zs).
  Proof. subst; cbn; eauto. Qed.

  Lemma interleave_rapp z zs xs ys y (H : z = y) (HH : interleave xs ys zs) : interleave xs (y++ys) (z++zs).
  Proof. subst; induction y; cbn; eauto. Qed.
  Lemma interleave_lapp z zs xs ys x (H : z = x) (HH : interleave xs ys zs) : interleave (x++xs) ys (z++zs).
  Proof. subst; induction x; cbn; eauto. Qed.

  Lemma interleave_nil_r zs : interleave zs nil zs.
  Proof. induction zs; cbn; eauto. Qed.
  Lemma interleave_nil_l zs : interleave zs nil zs.
  Proof. induction zs; cbn; eauto. Qed.
End __. End List.


Module TracePredicate.
  Definition flat_map {A B} (P:A->list B->Prop) xs :=
    List.fold_right app (eq nil) (List.map P xs).

  (* [interleave] trace of *arbitrarily small slices of* [P] and [Q].
     This sometimes makes sense for completely independent streams of
     events, but consider [(P \/ Q)^*] instead first. *)
  Definition interleave {T} (P Q : list T -> Prop) :=
    fun zs => exists xs ys, List.interleave xs ys zs /\ P xs /\ Q ys.

  Lemma interleave_rapp {T} {P Q : list T -> Prop} z zs
    (H : Q^* z) (HH : interleave P (Q^* ) zs) : interleave P (Q^* ) (z++zs).
  Proof.
    destruct HH as (?&?&?&?&?).
    eexists _, _; split.
    eapply List.interleave_rapp; eauto.
    split; eauto.
  Admitted.
  
  Lemma interleave_lapp {T} {P Q : list T -> Prop} z zs
    (H : P^* z) (HH : interleave (P^* ) Q zs) : interleave (P^* ) Q (z++zs).
  Proof.
    destruct HH as (?&?&?&?&?).
    eexists _, _; split.
    eapply List.interleave_lapp; eauto.
    split; eauto.
  Admitted.

  Definition interleave_rcons {T} {P Q} (z:T) zs H HH : interleave _ _ (cons _ _) :=
    @interleave_rapp T P Q [z] zs H HH.
  Definition interleave_lcons {T} {P Q} (z:T) zs H HH : interleave _ _ (cons _ _):=
    @interleave_lapp T P Q [z] zs H HH.
  
  Definition at_next_edge {T} clk data : list T -> Prop :=
    (fun x => clk false x)^+ +++ (fun x => clk true x /\ data x).
End TracePredicate.

Require Import Kami.All.

Definition bits {w} : word w -> list bool. Admitted.
Definition x : nat. exact O. Qed.

Section Named.
  Context (name : string).
  Local Open Scope kami_action.
  Local Open Scope kami_expr.
  Local Notation "@^ x" := (name ++ "_" ++ x)%string (at level 0).

  Definition SPI := MODULE {
         Register @^"hack_for_sequential_semantics" : Bit 0 <- Default
    with Register @^"tx_fifo"     : Bit 8 <- Default
    with Register @^"tx_fifo_len" : Bit 4 <- Default
    with Register @^"rx_fifo"     : Bit 8 <- Default
    with Register @^"rx_fifo_len" : Bit 4 <- @natToWord 4 15
    with Register @^"sck"         : Bool  <- Default
    
    with Rule @^"cycle" := (
      Write @^"hack_for_sequential_semantics" : Bit 0 <- $$(WO);

      Read sck <- @^"sck";
      Read tx_fifo : Bit 8 <- @^"tx_fifo";
      Read tx_fifo_len : Bit 4 <- @^"tx_fifo_len";
      Read rx_fifo : Bit 8 <- @^"rx_fifo";
      Read rx_fifo_len : Bit 4 <- @^"rx_fifo_len";

      Call miso : Bit 1 <- "GetMISO"();
      Call "PutSCK"(#sck : Bool);
      Call "PutMOSI"((UniBit (TruncMsb 7 1) #tx_fifo) : Bit 1);

      If ((*!*)#tx_fifo_len == $$@natToWord 4 0) then Retv else (If (#sck) then (
        Write @^"tx_fifo" : Bit 8 <- UniBit (TruncLsb 8 1) (BinBit (Concat 8 1) #tx_fifo $$(@ConstBit 1 $x));
        Write @^"tx_fifo_len" <- #tx_fifo_len + $1;
        Write @^"sck" : Bool <- !#sck;
      Retv ); Retv);

      If (#rx_fifo_len < $$@natToWord 4 8) then (If ((*!*)#sck) then Retv else (
        Write @^"rx_fifo" : Bit 8 <- UniBit (TruncLsb 8 1) (BinBit (Concat 8 1) #rx_fifo #miso);
        Write @^"rx_fifo_len" <- #rx_fifo_len - $1;
        Write @^"sck" : Bool <- !#sck;
      Retv ); Retv);

      Retv
    )
    
    with Method "write" (data : Bit 8) : Bool := (
      Write @^"hack_for_sequential_semantics" : Bit 0 <- $$(WO);
      Read tx_fifo_len <- @^"tx_fifo_len";
      If (#tx_fifo_len == $$@natToWord 4 0) then (
        Write @^"tx_fifo" : Bit 8 <- #data;
        Write @^"tx_fifo_len" <- $$@natToWord 4 8;
        Write @^"rx_fifo_len" <- $$@natToWord 4 0;
        Ret $$false
      ) else (
        Ret $$true
      ) as b;
      Ret #b
    )
    
    with Method "read" () : Bool := ( (* TODO return pair *)
      Write @^"hack_for_sequential_semantics" : Bit 0 <- $$(WO);
      Read rx_fifo_len : Bit 4 <- @^"rx_fifo_len";
      Read rx_fifo <- @^"rx_fifo";
      If (#rx_fifo_len == $$@natToWord 4 8) then (
        LET data : Bit 8 <- #rx_fifo;
        LET err : Bool <- $$false;
        Write @^"rx_fifo_len" <- $$@natToWord 4 15;
        Ret #err (* TODO: return (data, err) *)
      ) else (
        Ret $$true
      ) as r;
      Ret #r
    )
  }.

  Definition cmd_write arg err t := exists r : RegsT, t =
    [[(r, (Meth ("write", existT SignT (Bit 8, Bool) (arg, err)), @nil MethT))]].
  Definition cmd_read (ret : word 8) err t := exists r : RegsT, t =
    [[(r, (Meth ("read", existT SignT (Void, Bool) (wzero 0, err)), @nil MethT))]].
  Definition iocycle miso sck mosi t := exists r : RegsT, t = [[(r, (Rle (name ++ "_cycle"),
      [("GetMISO", existT SignT (Void, Bit 1) (wzero 0, WS miso WO));
      ("PutSCK",   existT SignT (Bool, Void)  (sck, wzero 0));
      ("PutMOSI",  existT SignT (Bit 1, Void) (WS mosi WO, wzero 0))]))]].
  
  Definition nop x := (exists arg, cmd_write arg true x) \/ (exists ret, cmd_read ret true x).

  Definition sck clk t := exists miso mosi, iocycle miso clk mosi t.
  Definition mosi mosi t := exists sck miso, iocycle miso sck mosi t.
  Definition miso miso t := exists sck mosi, iocycle miso sck mosi t.
  
  (* these are probably not useful because interleaving.. *)
  Definition mosis := TracePredicate.flat_map (fun x => TracePredicate.at_next_edge sck (mosi x)).
  Definition misos := TracePredicate.flat_map (fun x => TracePredicate.at_next_edge sck (miso x)).

  Definition exchange tx rx :=
    cmd_write tx false +++
    (fun t => mosis (bits tx) t /\ mosis (bits rx) t) +++
    maybe (cmd_read rx false).

  Definition transaction t := exists tx rx, exchange tx rx t.
  Definition spec := TracePredicate.interleave nop (kleene (fun t => sck false t \/ transaction t)).

  Definition enforce_regs (regs:RegsT) tx_fifo tx_fifo_len rx_fifo rx_fifo_len sck := regs =
    [(@^"hack_for_sequential_semantics", existT _ (SyntaxKind (Bit 0)) WO);
                (@^"tx_fifo", existT _ (SyntaxKind (Bit 8)) tx_fifo);
                (@^"tx_fifo_len", existT _ (SyntaxKind (Bit 4)) tx_fifo_len);
                (@^"rx_fifo", existT _ (SyntaxKind (Bit 8)) rx_fifo);
                (@^"rx_fifo_len", existT _ (SyntaxKind (Bit 4)) rx_fifo_len);
                (@^"sck", existT _ (SyntaxKind Bool) sck) ].

  (* Local Coercion SyntaxKind : Kind >-> FullKind. *)
  Record idle (regs : RegsT) (t : list (list FullLabel)) : Prop := {
    tx_fifo : _ ;
    rx_fifo : _ ;
    _ : spec t;
    _ : enforce_regs regs tx_fifo (natToWord 4 0) rx_fifo (natToWord 4 15) false;
  }.

  Record active (regs : RegsT) (t : list (list FullLabel)) : Prop := {
    tx : _;
    tx_fifo : _ ;
    tx_fifo_len : _ ;
    rx_fifo : _ ;
    rx_fifo_len : _ ;
    _ : (app spec (cmd_write tx false)) t; (* WIP *)
    _ : tx = tx_fifo; (* only during first tick *)
    _ : enforce_regs regs tx_fifo tx_fifo_len rx_fifo rx_fifo_len false;
  }.

  Definition invariant s t := idle s t \/ active s t.

  Goal forall s t, Trace SPI s t -> invariant s t.
  Proof.
    induction 1.
    { admit. }
    subst.

    destruct IHTrace as [IHTrace|IHTrace]; [|admit].
    destruct IHTrace.
    cbv [enforce_regs] in *.

    unshelve (idtac;
    let pf := open_constr:(InvertStep (@Build_BaseModuleWf SPI _) _ _ _ HStep) in
    destruct pf);
    [abstract discharge_wf|..];
    repeat match goal with
      | H: Trace _ _ |- _ => clear H
      | _ => progress intros
      | _ => progress clean_hyp_step
      | _ => progress cbn [SPI getMethods baseModule makeModule makeModule' type evalExpr isEq evalConstT Kind_rect List.app map fst snd projT1 projT2] in *
      | H: UpdRegs _ _ _ |- _ => apply NoDup_UpdRegs in H; symmetry in H; destruct H
    end.

    10: {
      match goal with
      | H: UpdRegs _ _ _ |- _ => apply NoDup_UpdRegs in H; [symmetry in H; destruct H|..]
      end.
      constructor. econstructor.

      2: cbv [enforce_regs] in *;
      repeat match goal with
      | _ => progress discharge_string_dec
      | _ => progress cbn [fst snd]
      | |- context G [match ?x with _ => _ end] =>
         let X := eval hnf in x in
         progress change x with X
      | _ => progress (f_equal; [])
      | |- ?l = ?r =>
          let l := eval hnf in l in
          let r := eval hnf in r in
          progress change (l = r)
      | _ => exact eq_refl
      end.
      2:cbn [evalBinBit evalUniBool].

      {
        cbv [spec].
        simple refine (TracePredicate.interleave_rcons _ _ _ _).
        2:eassumption.
        match goal with |- ?f ?x => enough (sck false x) by admit end.
        cbv [sck iocycle].
        eexists _, _, _.
        repeat f_equal; eauto.
        1,2: admit. (* bbv... *)
      }

      idtac.
      all : cbn [map fst].
      1,2: admit. (* NoDup *)
    }


    10: {
      match goal with
      | H: UpdRegs _ _ _ |- _ => apply NoDup_UpdRegs in H; [symmetry in H; destruct H|..]
      end.
      constructor. econstructor.

      2: cbv [enforce_regs] in *;
      repeat match goal with
      | _ => progress discharge_string_dec
      | _ => progress cbn [fst snd]
      | |- context G [match ?x with _ => _ end] =>
         let X := eval hnf in x in
         progress change x with X
      | _ => progress (f_equal; [])
      | |- ?l = ?r =>
          let l := eval hnf in l in
          let r := eval hnf in r in
          progress change (l = r)
      | _ => exact eq_refl
      end.





End Named.

  (* Notation "( x , y , .. , z )" := (existT _ .. (existT _ x y) .. z) : core_scope. *)
