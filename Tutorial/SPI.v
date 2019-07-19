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
    with Register @^"sck"         : Bool <- Default
    
    with Rule @^"cycle" := (
      Write @^"hack_for_sequential_semantics" : Bit 0 <- $$(WO);
      Call miso : Bit 1 <- "GetMISO"();

      Read sck <- @^"sck";
      Read tx_fifo : Bit 8 <- @^"tx_fifo";
      Read tx_fifo_len : Bit 4 <- @^"tx_fifo_len";
      Read rx_fifo : Bit 8 <- @^"rx_fifo";
      Read rx_fifo_len : Bit 4 <- @^"rx_fifo_len";
      If (#tx_fifo_len == $$@natToWord 4 0) then (
        If (#sck) then (
          Write @^"tx_fifo" : Bit 8 <- UniBit (TruncLsb 8 1) (BinBit (Concat 8 1) #tx_fifo $$(@ConstBit 1 $x));
          Write @^"tx_fifo_len" <- #tx_fifo_len - $1;
          Call "PutSCK"(#sck : Bool);
          Call "PutMOSI"((UniBit (TruncMsb 7 1) #tx_fifo) : Bit 1);
          Retv
        ) else (
          Write @^"rx_fifo" : Bit 8 <- UniBit (TruncLsb 8 1) (BinBit (Concat 8 1) #rx_fifo #miso);
          Write @^"rx_fifo_len" : Bit 4 <- #rx_fifo_len + $1;
          Call "PutSCK"(#sck : Bool);
          Call "PutMOSI"((UniBit (TruncMsb 7 1) #tx_fifo) : Bit 1);
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
      Write @^"hack_for_sequential_semantich" : Bit 0 <- $$(WO);
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

  (* Eval cbv -[type fullType fst snd] in FullLabel. *)
  (* = (list RegT * (RuleOrMeth * list (string * {k : Kind * Kind & type (fst k) * type (snd k)})))%type *)

  Goal forall (P:_->Prop) r l, Trace SPI r l -> P (map (map snd) l).
  Proof.
    intros.
    induction H; subst; [admit|].
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
      rewrite @UIP_refl in H2.
      unfold eq_rect in *.
      
      inv H0.
      match goal with
      | H:existT ?a ?b1 ?c1 = existT ?a ?b2 ?c2
      |- _ => idtac H; apply inversionExistT in H; destruct H as [? ?]; subst
      end.

      clean_hyp_step.
      clean_hyp_step.
      clean_hyp_step.
      clean_hyp_step.
      clean_hyp_step.
      clean_hyp_step.
      
      admit. (* stuck on eq_refl match *)
      admit. (* stuck on eq_refl match *)
    }
    2: {
      repeat clean_hyp_step;
      cbn [evalExpr isEq evalConstT Kind_rect map fst snd] in *.
      admit.


End Named.
