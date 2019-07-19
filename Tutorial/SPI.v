Require Import Coq.Lists.List. Import ListNotations.
Module spec.
  
  Axiom one : forall {T}, (T -> Prop) -> list T -> Prop.
  Axiom plus : forall {T}, (list T -> Prop) -> list T -> Prop.
  Axiom app : forall {T}, (list T -> Prop) -> (list T -> Prop) -> list T -> Prop.
  Local Notation "x ^+" := (plus x) (at level 50).
  Local Infix "+++" := app (at level 60).
  
  Definition flat_map {A B} (P:A->list B->Prop) xs :=
    List.fold_right app (eq nil) (List.map P xs).
  
  Definition at_next_edge {T} clk data : list T -> Prop :=
    (fun x => not (clk x))^+ +++ (fun x => clk x /\ data x).
  
  Definition clk : list (bool * bool * bool) -> Prop :=
    one (fun '(clk, _, _) => clk = true).
  Definition mosi : bool -> list (bool * bool * bool) -> Prop :=
    fun b => one (fun '(_, mosi, _) => mosi = b).
  Definition miso : bool -> list (bool * bool * bool) -> Prop :=
    fun b => one (fun '(_, _, miso) => miso = b).
  
  (* TODO: allow and ignore nop-s in external io *)
  Definition mosis := @flat_map bool (bool*bool*bool) (fun x => at_next_edge clk (mosi x)).
  Definition misos := @flat_map bool (bool*bool*bool) (fun x => at_next_edge clk (miso x)).
End spec.

Require Import Kami.All.
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
    with Register @^"rx_fifo_len" : Bit 4 <- Default
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

      If (#tx_fifo_len == $$@natToWord 4 0) then (
        If (#sck) then (
          Write @^"tx_fifo" : Bit 8 <- UniBit (TruncLsb 8 1) (BinBit (Concat 8 1) #tx_fifo $$(@ConstBit 1 $x));
          Write @^"tx_fifo_len" <- #tx_fifo_len - $1;
          Retv
        ) else (
          Write @^"rx_fifo" : Bit 8 <- UniBit (TruncLsb 8 1) (BinBit (Concat 8 1) #rx_fifo #miso);
          Write @^"rx_fifo_len" : Bit 4 <- #rx_fifo_len + $1;
          Retv
        );
        Retv
      );
      Write @^"sck" : Bool <- !#sck;

      Retv
    )
    
    with Method "write" (data : Bit 8) : Bool := (
      Write @^"hack_for_sequential_semantics" : Bit 0 <- $$(WO);
      Read tx_fifo_len <- @^"tx_fifo_len";
      If (#tx_fifo_len == $$@natToWord 4 0) then (
        Write @^"tx_fifo" : Bit 8 <- #data;
        Write @^"tx_fifo_len" <- $$@natToWord 4 8;
        Ret $$false
      ) else (
        Ret $$true
      ) as b;
      Ret #b
    )
    
    with Method "read" () : Bool := ( (* TODO return pair *)
      Write @^"hack_for_sequential_semantics" : Bit 0 <- $$(WO);
      Read rx_fifo <- @^"rx_fifo";
      Read rx_fifo_len <- @^"rx_fifo_len";
      If (#rx_fifo_len == $$@natToWord 4 8) then (
        LET data : Bit 8 <- #rx_fifo;
        LET err : Bool <- $$false;
        Ret #err (* TODO: return (data, err) *)
      ) else (
        Ret $$true
      ) as r;
      Ret #r
    )
  }.

  Definition iocycle miso sck mosi := eq (Rle (name ++ "_cycle"),
      [("GetMISO", existT SignT (Void, Bit 1) (wzero 0, miso));
      ("PutSCK",   existT SignT (Bool, Void)  (sck, wzero 0));
      ("PutMOSI",  existT SignT (Bit 1, Void) (mosi, wzero 0))]).
  Definition cmd_write arg err := eq
    (Meth ("write", existT SignT (Bit 8, Bool) (arg, err)), @nil MethT).
  Definition cmd_read (ret : word 8) err := eq (* TODO: use "ret" *)
    (Meth ("read", existT SignT (Void, Bool) (wzero 0, err)), @nil MethT).
  Definition nop x := (exists arg, cmd_write arg true x) \/ (exists ret, cmd_read ret true x).

  Definition parsable := Forall (fun l => exists (r:RegsT) x, l = [(r, x)] /\
    ((exists miso sck mosi, iocycle miso sck mosi x) \/
     (exists arg err, cmd_write arg err x) \/
     (exists ret err, cmd_read ret err x))).

  Goal forall (I:_->Prop) r l, I r -> Trace SPI r l -> parsable l.
  Proof.
    intros I r l HI HTrace.
    induction HTrace.
    { subst ls'. cbn. admit. }

    unshelve (idtac;
    let pf := open_constr:(InvertStep (@Build_BaseModuleWf SPI _) _ _ _ HStep) in
    destruct pf);
    [abstract discharge_wf|..];
    repeat match goal with
      | _ => progress intros
      | _ => progress clean_hyp_step
      | _ => progress cbn [SPI getMethods baseModule makeModule makeModule' type evalExpr isEq evalConstT Kind_rect app map fst snd projT1 projT2] in *
    end.
    15: {
      erewrite (word0 arg).
      constructor.
      2: eapply IHHTrace; admit.
      eexists ?[r], (?[n], ?[vs]).
      split; repeat f_equal.
      right; right.
      eexists _, _.
      exact eq_refl. }


  Abort.

    (*
    inversion HStep; subst.
    inversion HSubsteps; subst.
    3: {
      cbn -[SPI] in *.
      destruct fb as [[argT retT] method].
      cbn -[SPI] in *.
      simpl in HInMeths.

      clean_hyp_step.
      clean_hyp_step.
      assert (sth: Bit 8 = argT). {
        clear - H1.
        inversion_sigma.
        inv H0.
        auto.
    }
      assert (sth2: Bool = retT). {
        clear - H1.
        inversion_sigma.
        inv H0.
        auto.
    }
      destruct sth, sth2.
      inversion_sigma.
      Import Eqdep.
      Set Printing All.
      replace (H0) with (eq_refl (Bit 8, Bool)) in H2.
      2: { symmetry; eapply UIP_refl. }
      cbn in H2.
      clear H0.
      repeat clean_hyp_step.

      Notation "( x , y , .. , z )" := (existT _ .. (existT _ x y) .. z) : core_scope.

      all:
      try subst method;
      cbn [type] in *;
      repeat clean_hyp_step;
      cbn [evalExpr isEq evalConstT Kind_rect app map fst snd] in *.

      2: {
        *)

End Named.
