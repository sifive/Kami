Require Import Kami.AllNotations.

Section Named.
  Variable sz: nat.
  Variable name: string.
  Local Notation "@^ x" := (name ++ "_" ++ x)%string (at level 0).

  (* The implementation which keeps incrementing a counter in one step and sends the value of the counter in the other *)
  Definition IncrementerImpl :=
    MODULE {
      Register @^"counter" : Bit sz <- Default
      with Register @^"counter1" : Bit sz <- Default
      with Register @^"isSending" : Bool <- true
      
      with Rule @^"send_and_inc" :=
      ( Read isSending: Bool <- @^"isSending" ;
        If #isSending
        then (  
          Read counter: Bit sz <- @^"counter" ;
          Call "counterVal"(#counter: _);
          Write @^"isSending" <- !#isSending ;
          Retv)
        else (
          Read counter: Bit sz <- @^"counter" ;
          Write @^"counter" <- #counter + $1;
          Write @^"isSending" <- !#isSending ;
          Retv );
        Retv) }.
      

  (* The specification which combines the two actions in one rule *)
  Definition IncrementerSpec :=
    MODULE {
      Register @^"counter" : Bit sz <- Default
      with Register @^"counter1" : Bit sz <- Default
      
      with Rule @^"send_and_inc" :=
      ( Read counter: Bit sz <- @^"counter" ;
        Call "counterVal"(#counter: _);
        Write @^"counter" <- #counter + $1;
        Retv )
      }.
  
  (* The invariant connecting the state of the implementation with the
    state of the spec, including specifying the list of register register names, their types and values *)
  Record Incrementer_invariant (impl spec: RegsT) : Prop :=
    { counterImpl: word sz ;
      isSending: bool ;
      implEq : impl = (@^"counter", existT _ (SyntaxKind (Bit sz)) counterImpl)
                        :: (@^"counter1", existT _ (SyntaxKind (Bit sz)) $0)
                        :: (@^"isSending", existT _ (SyntaxKind Bool) isSending) :: nil ;
      specEq : spec = (@^"counter", existT _ (SyntaxKind (Bit sz))
                                           (if isSending then counterImpl else counterImpl ^+ $1))
                        :: (@^"counter1", existT  _ (SyntaxKind (Bit sz)) $0)
                        :: nil
    }.

  (* Proving the trace inclusion of the implementation with respect to the spec *)
  Theorem Incrementer_TraceInclusion:
    TraceInclusion (Base IncrementerImpl) (Base IncrementerSpec).
  Proof.
    (* discharge_simulation with the name of the record holding the invariant will discharge most of the trivial goals and
      requires the user to specify, for each implementation rule or method, either a specification rule or method that 
      produces the same method calls while maintaining the state invariant or a nil step in the specification.
      The former is simplified using simplify_simulatingRule, with the rule name.
      The latter is simplified using simplify_nilStep.
      discharge_CommonRegisterAuto discharges the goals that require that two methods or a method and rule of
      the implementation are not combinable by automatically searching for at least one register with the two actions write to *)
    discharge_simulation Incrementer_invariant; discharge_CommonRegisterAuto.
    - simplify_simulatingRule @^"send_and_inc"; subst.
      + auto.
      + simpl. discharge_string_dec.
        repeat (econstructor; eauto; simpl; subst).
        rewrite wzero_wplus; auto.
    - simplify_nilStep.
      econstructor; simpl; eauto; subst.
      rewrite ?negb_true_iff in *; subst.
      rewrite wzero_wplus; simpl; auto.

      (* Note that while this example does not create spurious existentials, usually, there is a plethora of existentials created that can be instantiated with arbitrary values as they do not affect the proof. These goals are discharged with the following two commands*)
      Unshelve.
      all: repeat constructor.
Qed.
End Named.
