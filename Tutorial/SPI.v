Require Import Coq.Lists.List. Import ListNotations.

Section TracePredicate.  
  Context {T : Type}.
  Axiom kleene : (list T -> Prop) -> list T -> Prop.
  Axiom plus : (list T -> Prop) -> list T -> Prop.
  Axiom app : (list T -> Prop) -> (list T -> Prop) -> list T -> Prop.
  Lemma app_empty_r (P Q : list T -> Prop) t : P t -> Q nil -> app P Q t. Admitted.
  Axiom either : (list T -> Prop) -> (list T -> Prop) -> list T -> Prop.
  Axiom maybe : (list T -> Prop) -> list T -> Prop.

  Definition exist {V} (P : V -> list T -> Prop) (l : list T) : Prop :=
    exists v : V, P v l.
End TracePredicate.
Local Notation "x ^*" := (kleene x) (at level 50).
Local Notation "x ^+" := (plus x) (at level 50).
Local Infix "+++" := app (at level 60).

Module List. Section __.
  Context {T : Type}.
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
  Lemma interleave_nil_l zs : interleave nil zs zs.
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

  Local Infix "||" := TracePredicate.interleave.
  Lemma interleave_rapp {T} {P QQ Q : list T -> Prop} z zs
    (H : Q z) (HH : interleave P QQ zs) : interleave P (QQ +++ Q) (z++zs).
  Proof.
    destruct HH as (?&?&?&?&?).
    eexists _, _; split.
    eapply List.interleave_rapp; eauto.
    split; eauto.
  Admitted.
  
  Lemma interleave_lapp {T} {PP P Q : list T -> Prop} z zs
    (H : P z) (HH : interleave PP Q zs) : interleave (PP +++ P) Q (z++zs).
  Proof.
    destruct HH as (?&?&?&?&?).
    eexists _, _; split.
    eapply List.interleave_lapp; eauto.
    split; eauto.
  Admitted.

  Definition interleave_rcons {T} {P QQ Q} (z:T) zs H HH : interleave _ _ (cons _ _) :=
    @interleave_rapp T P QQ Q [z] zs H HH.
  Definition interleave_lcons {T} {PP P Q} (z:T) zs H HH : interleave _ _ (cons _ _):=
    @interleave_lapp T PP P Q [z] zs H HH.

  Lemma interleave_rkleene {T} {P Q : list T -> Prop} z zs
    (H : Q^* z) (HH : interleave P (Q^* ) zs) : interleave P (Q^* ) (z++zs).
  Proof.
    destruct HH as (?&?&?&?&?).
    eexists _, _; split.
    eapply List.interleave_rapp; eauto.
    split; eauto.
  Admitted.
  
  Lemma interleave_lkleene {T} {P Q : list T -> Prop} z zs
    (H : P^* z) (HH : interleave (P^* ) Q zs) : interleave (P^* ) Q (z++zs).
  Proof.
    destruct HH as (?&?&?&?&?).
    eexists _, _; split.
    eapply List.interleave_lapp; eauto.
    split; eauto.
  Admitted.

  Definition interleave_rkleene_cons {T} {P Q} (z:T) zs H HH : interleave _ _ (cons _ _) :=
    @interleave_rkleene T P Q [z] zs H HH.
  Definition interleave_lkleene_cons {T} {P Q} (z:T) zs H HH : interleave _ _ (cons _ _):=
    @interleave_lkleene T P Q [z] zs H HH.

  Lemma interleave_kleene_l_app_r {T} (A B C : list T -> Prop) (bs cs : list T)
    (HB : TracePredicate.interleave (kleene A) B bs)
    (HC : TracePredicate.interleave (kleene A) C cs)
    : TracePredicate.interleave (kleene A) (B +++ C) (cs ++ bs).
  Admitted.
  (* TODO: how do I actually prove this in a loop *)

  Lemma interleave_exist_r {T V} P Q (t : list T) : (exist (fun v:V => P || Q v)) t -> (P || exist Q) t.
  Proof.
    cbv [exist].
    intros (?&?&?&?&?&?).
    eexists _, _; eauto.
  Qed.

  Lemma interleave_exist_l {T V} P Q (t : list T) : (exist (fun v:V => P v || Q)) t -> (exist P || Q) t.
  Proof.
    cbv [exist].
    intros (?&?&?&?&?&?).
    eexists _, _; eauto.
  Qed.

End TracePredicate.
Local Infix "||" := TracePredicate.interleave.

Require Import Kami.All.

Definition bits {w} : word w -> list bool. Admitted.
Lemma length_bits w x : List.length (@bits w x) = w. Admitted.
Lemma bits_nil x : @bits 0 x = nil.
Proof.
  pose proof length_bits x as H.
  destruct (bits x); [trivial | inversion H].
Qed.
Definition x : nat. exact O. Qed.

Section Named.
  Context (name : string).
  Local Open Scope kami_action.
  Local Open Scope kami_expr.
  Local Notation "@^ x" := (name ++ "_" ++ x)%string (at level 0).

  Definition SPI := MODULE {
         Register @^"hack_for_sequential_semantics" : Bit 0 <- Default
    with Register @^"i"           : Bit 4 <- Default
    with Register @^"sck"         : Bool  <- Default
    with Register @^"tx"     : Bit 8 <- Default
    with Register @^"rx"     : Bit 8 <- Default
    with Register @^"rx_valid"    : Bool  <- Default
    
    with Rule @^"cycle" := (
      Write @^"hack_for_sequential_semantics" : Bit 0 <- $$(WO);
      Read sck <- @^"sck";
      Read i : Bit 4 <- @^"i";
      Read tx : Bit 8 <- @^"tx";
      If (*!*) #i == $$@natToWord 4 0 then Retv else (
        If (#sck) then (
          Write @^"sck" : Bool <- $$false;
          Call "PutSCK"($$false : Bool);
          Call "PutMOSI"((UniBit (TruncMsb 7 1) #tx) : Bit 1);
          Retv
        ) else (
          Read rx : Bit 8 <- @^"rx";
          Call miso : Bit 1 <- "GetMISO"();
          Write @^"rx" : Bit 8 <- BinBit (Concat 7 1) (UniBit (TruncMsb 1 7) #rx) #miso;
          Write @^"sck" : Bool <- $$true;
          Call "PutSCK"($$true : Bool);
          Call "PutMOSI"((UniBit (TruncMsb 7 1) #tx) : Bit 1);
          Write @^"tx" : Bit 8 <- BinBit (Concat 7 1) (UniBit (TruncMsb 1 7) #tx) $$(@ConstBit 1 $x);
          Write @^"rx_valid" <- #i == $$@natToWord 4 1;
          Retv
        );
      Retv);

    Retv)
    
    with Method "write" (data : Bit 8) : Bool := (
      Write @^"hack_for_sequential_semantics" : Bit 0 <- $$(WO);
      Read i <- @^"i";
      If #i == $$@natToWord 4 0 then (
        Write @^"tx" : Bit 8 <- #data;
        Write @^"i" <- $$@natToWord 4 8;
        Write @^"rx_valid" <- $$false;
        Ret $$false
      ) else (
        Ret $$true
      ) as b;
      Ret #b
    )
    
    with Method "read" () : Bool := ( (* TODO return pair *)
      Write @^"hack_for_sequential_semantics" : Bit 0 <- $$(WO);
      Read rx_valid <- @^"rx_valid";
      If #rx_valid then (
        Read data : Bit 8 <- @^"rx";
        Write @^"rx_valid" <- $$false;
        Ret $$false (* TODO: return (data, false) *)
      ) else (
        Ret $$true
      ) as r;
      Ret #r
    )
  }.

  Definition cmd_write arg err := exist (fun r : RegsT =>
    eq [[(r, (Meth ("write", existT SignT (Bit 8, Bool) (arg, err)), @nil MethT))]]).
  Definition cmd_read (ret : word 8) err := exist (fun r : RegsT =>
    eq [[(r, (Meth ("read", existT SignT (Void, Bool) (wzero 0, err)), @nil MethT))]]).
  Definition iocycle miso sck mosi := exist (fun r : RegsT => eq [[(r, (Rle (name ++ "_cycle"),
      [("GetMISO", existT SignT (Void, Bit 1) (wzero 0, WS miso WO));
      ("PutSCK",   existT SignT (Bool, Void)  (sck, wzero 0));
      ("PutMOSI",  existT SignT (Bit 1, Void) (WS mosi WO, wzero 0))]))]]).

  Definition nop x := (exists arg, cmd_write arg true x) \/ (exists ret, cmd_read ret true x).
  
  Inductive p :=
  | getmiso (_ : forall miso : bool, p)
  | putsck (_ : bool) (_ : p)
  | putmosi (_ : word 1) (_ : p)

  | yield (_ : p)
  | ret (_ : word 8).

  Fixpoint xchg_prog (n : nat) : forall (tx : word 8) (rx : word 8), p :=
    match n with
    | O => fun _ rx => ret rx
    | S n => fun tx rx =>
      let mosi := split2 7 1 tx in
      let tx := WS false (split1 7 1 tx) in
      putsck false (
      putmosi mosi (
      yield (
      getmiso (fun miso =>
      let rx := WS miso (split1 7 1 rx) in
      putsck true (
      putmosi mosi (
      yield (
      @xchg_prog n tx rx
      )))))))
    end.

  Fixpoint interp (e : p) : list MethT -> word 8 -> list (list FullLabel) -> Prop :=
    match e with
    | getmiso k => fun l w => exist (fun miso => interp (k miso) (l++[("GetMISO", existT SignT (Void, Bit 1) (wzero 0, WS miso WO))]) w)
    | putsck sck k => fun l w => interp k (l++[("PutSCK", existT SignT (Bool, Void) (sck, wzero 0))]) w
    | putmosi mosi k => fun l w => interp k (l++[("PutMOSI", existT SignT (Bit 1, Void) (mosi, wzero 0))]) w
    | yield k => fun l w => exist (fun r => (eq [[(r, (Rle (name ++ "_cycle"), l))]] +++ interp k nil w))
    | ret w => fun l' w' t => w' = w /\ t = nil
    end.

  Definition silent := exist (fun miso => exist (fun mosi => iocycle miso false mosi)).

  Definition spec := TracePredicate.interleave (kleene nop) (kleene (fun t =>
    silent t \/
    exists tx rx, (cmd_write tx false +++
                   interp (xchg_prog 8 tx (wzero 8)) nil rx +++
                   maybe (cmd_read rx false)) t)).

  Definition enforce_regs (regs:RegsT) i sck tx rx rx_valid := regs =
    [
    (@^"hack_for_sequential_semantics", existT _ (SyntaxKind (Bit 0)) WO);
     (@^"i", existT _ (SyntaxKind (Bit 4)) i);
     (@^"sck", existT _ (SyntaxKind Bool) sck);
     (@^"tx", existT _ (SyntaxKind (Bit 8)) tx);
     (@^"rx", existT _ (SyntaxKind (Bit 8)) rx);
     (@^"rx_valid", existT _ (SyntaxKind Bool) rx_valid)
     ].

  Definition xchg_prog_sckfalse (n : nat) (tx : word 8) (rx : word 8) (mosi : word 1) : p :=
    getmiso (fun miso =>
    let tx := WS false (split1 7 1 tx) in
    let rx := WS miso (split1 7 1 rx) in
    putsck true (
    putmosi mosi (
    yield (
    @xchg_prog n tx rx)))).

  Definition xchg_prog_as_sckfalse (n : nat) (tx : word 8) (rx : word 8) :
    xchg_prog (S n) tx rx =
    let mosi := split2 7 1 tx in
    putsck false (
    putmosi mosi (
    yield (
    xchg_prog_sckfalse n tx rx mosi)))
    := eq_refl.

  Ltac solve_enforce_regs :=
    solve[cbv [doUpdRegs enforce_regs] in *; subst; clear;
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
    end].

  (* draining case only *)
  Goal forall s past,
    Trace SPI s past ->
    exists i sck tx rx (*rx_valid*)false,
    enforce_regs s i sck tx rx false /\
    wordToNat i <> 0 /\
    let i := wordToNat i in
    forall frx future,
    (if sck
    then TracePredicate.interleave (kleene nop) (interp (xchg_prog i tx rx) nil frx) future
    else TracePredicate.interleave (kleene nop) (interp (xchg_prog_sckfalse (pred i)  tx rx (split2 7 1 tx)) nil frx) future)
    -> TracePredicate.interleave (kleene nop) (interp (xchg_prog 8 tx rx) nil frx) (future ++ past).
  Proof.
    intros s past.
    pose proof eq_refl s as MARKER.
    induction 1 as [A B C D | regsBefore t regUpds regsAfter E _ IHTrace HStep K I].
    { subst. admit. }

    rename t into past.
    specialize (IHTrace eq_refl); destruct IHTrace as (i&sck&tx&rx&rx_valid&Hregs&Hi&IHTrace).

    unshelve epose proof InvertStep (@Build_BaseModuleWf SPI _) _ _ _ HStep as HHS;
      clear HStep; [abstract discharge_wf|..|rename HHS into HStep].
    1,2,3: admit.

    repeat match goal with
      | _ => progress intros
      | _ => progress subst
      | _ => progress clean_hyp_step
      | _ => progress discharge_string_dec
      | _ => progress cbn [fst snd] in *
      | _ => progress cbv [enforce_regs] in *
      | K: UpdRegs _ _ ?z |- _ =>
          let H := fresh K in
          unshelve epose proof (NoDup_UpdRegs _ _ K); clear K; [> ..| progress subst z]
      | |- NoDup _ => admit
      | |- exists _ _ _ _ _, doUpdRegs _ _ = _ /\ _ =>
          eexists _, _, _, _, _; eapply conj; [> solve_enforce_regs| ]
      | |- context G [@cons ?T ?a ?b] =>
          assert_fails (idtac; match b with nil => idtac end);
          let goal := context G [@List.app T (@cons T a nil) b] in
          change goal
      | _ => progress rewrite ?app_assoc, ?app_nil_r
      | H : ?T -> _ |- _ => assert_succeeds (idtac; match type of T with Prop => idtac end); specialize (H ltac:(auto))
    end.

    all:
    repeat match goal with
      | |- _ /\ _ => split; try solve [auto 2]; (let n := numgoals in guard n <= 1)
    end.

    { (* i = 0 *)
      unshelve epose proof ((_ : forall x y, getBool (weq x y) = true -> x = y) _ _ H3); [>admit|].
      subst rv0.
      case (Hi eq_refl). }
    {
      (* trace construction *)
      rename Hi into Hi'; destruct (wordToNat rv0) as [|?i] eqn:Hi; [>congruence|]; clear Hi'.
      cbn [Init.Nat.pred evalExpr evalConstT getBool isEq] in *; subst.

      intros frx future Hfuture.
      rewrite app_assoc.
      revert Hfuture; revert future; revert frx.
      intros; refine (IHTrace _ _ _); clear IHTrace; revert Hfuture; revert future; revert frx.
      rewrite xchg_prog_as_sckfalse; cbn zeta beta.

      intros.
      cbn [interp].
      eapply TracePredicate.interleave_exist_r; eexists.
      eapply TracePredicate.interleave_kleene_l_app_r; [|eassumption].
      eexists nil, _; split; [|split].
      { eapply List.interleave_nil_l. }
      { (* kleene_nil *) admit. }
      cbv [List.app]. f_equal. f_equal. f_equal. f_equal.
      repeat f_equal.
      eapply f_equal.
      2:eapply f_equal.       
      1,2: rewrite word0, (word0 (wzero 0)); reflexivity. }


Abort.

End Named.

  (* Notation "( x , y , .. , z )" := (existT _ .. (existT _ x y) .. z) : core_scope. *)
