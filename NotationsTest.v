Require Import Kami.Syntax Kami.Notations Kami.Tactics.
Section mod_test.
  Variable a: string.
  Local Notation "^ x" := (a ++ "." ++ x)%string (at level 0).
  Local Example test := MOD_WF{
                              Register (^"x") : Bool <- true
                                with Register (^"y") : Bool <- false
                                with Rule (^"r1") := ( Read y: Bool <- ^"y";
                                                         Write (^"x"): Bool <- #y;
                                                         Retv )
                          }.

  Local Example test1 := MODULE_WF{
                             Register (^"x") : Bool <- true
                               with Register (^"y") : Bool <- false
                               with Rule (^"r1") := ( Read y: Bool <- ^"y";
                                                        Write (^"x"): Bool <- #y;
                                                        Retv )
                           }.
End mod_test.





Local Example test_normaldisj:
  DisjKey (map (fun x => (x, 1)) ("a" :: "b" :: "c" :: nil))%string
          (map (fun x => (x, 2)) ("d" :: "e" :: nil))%string.
Proof.
  simpl.
  discharge_DisjKey.
Qed.

Local Example test_prefix_disj a:
  DisjKey (map (fun x => ((a ++ x)%string, 1)) ("ab" :: "be" :: "cs" :: nil))%string
          (map (fun x => ((a ++ x)%string, 2)) ("de" :: "et" :: nil))%string.
Proof.
  simpl.
  discharge_DisjKey.
Qed.

Local Example test_suffix_disj a:
  DisjKey (map (fun x => ((x ++ a)%string, 1)) ("ab" :: "be" :: "cs" :: nil))%string
          (map (fun x => ((x ++ a)%string, 2)) ("de" :: "et" :: nil))%string.
Proof.
  simpl.
  discharge_DisjKey.
Qed.




(* Testing the Notations *)

Local Example testSwitch ty (val: Bit 5 @# ty) (a b: Bool @# ty) : Bool @# ty :=
  (Switch val Retn Bool With {
            $$ (ZToWord 5 5) ::= $$ true ;
            $$ (ZToWord 5 6) ::= $$ false
          })%kami_expr.

Local Example testSwitch2 ty (val: Bit 5 @# ty) (a b: Bool @# ty) : Bool @# ty :=
  (Switch val Of Bit 5 Retn Bool With {
            $$ (ZToWord 5 5) ::= $$ true ;
            $$ (ZToWord 5 6) ::= $$ false
          })%kami_expr.


Local Example test2 a b := (ConcatMod (test a) (test b))%kami.

Section unittests.

  Open Scope kami_expr.

  Local Notation "X ==> Y" := (evalExpr X = Y) (at level 75).

  Let test_struct
    :=  STRUCT {
            "field0" ::= Const type false;
            "field1" ::= Const type (ZToWord 4 2);
            "field2" ::= Const type (ZToWord 5 3)}%kami_expr%struct_init.

  Section struct_get_field_default_unittests.
    Let test0
    :  test_struct @% "field0" ==> false
      := eq_refl false.

    Let test1
      : test_struct @% "field1" ==> ZToWord 4 2
      := eq_refl (ZToWord 4 2).
    
    Let test2
      : test_struct @% "field2" ==> ZToWord 5 3
      := eq_refl (ZToWord 5 3).

  End struct_get_field_default_unittests.

  Section struct_set_field_unittests.

    Let test_0
    :  (test_struct @%["field0" <- (Const type true)]) @% "field0"
                                                       ==> true
      := eq_refl true.

    Let test_1
      :  (test_struct @%["field1" <- (Const type (ZToWord 4 5))]) @% "field1"
                                                                    ==> ZToWord 4 5
      := eq_refl (ZToWord 4 5).

    Let test_2
      :  (test_struct @%["field2" <- (Const type (ZToWord 5 5))]) @% "field2"
                                                                    ==> ZToWord 5 5
      := eq_refl (ZToWord 5 5).
  End struct_set_field_unittests.

  Close Scope kami_expr.

End unittests.


Local Definition testConcat ty (w1: Bit 10 @# ty) (w2: Bit 2 @# ty) (w3: Bit 5 @# ty) :=
  {< w1, w2, w3 >}%kami_expr.

Local Definition testArrayAccess ty (v: Array 4 (Bit 10) @# ty) (idx : Bit 2 @# ty) := (v @[ idx <- v @[ idx ]])%kami_expr.

Local Definition testConstNat ty (w1 w2: Bit 10 @# ty): Bit 10 @# ty := (w1 + w2 + $4 + $6)%kami_expr.

Local Definition testExtract ty n n1 n2 (pf1: n > n1) (pf2: n1 > n2) (a: Bit n @# ty) := (a $#[n1 : n2])%kami_expr.





Local Definition testStruct :=
  (STRUCT_TYPE {
       "hello" :: Bit 10 ;
       "a" :: Bit 3 ;
       "b" :: Bit 5 ;
       "test" :: Bool }).

Local Definition testStructVal {ty}: testStruct @# ty :=
  (STRUCT {
       "hello" ::= $ 4 ;
       "a" ::= $ 23 ;
       "b" ::= $ 5 ;
       "test" ::= $$ true })%kami_expr.



Local Open Scope kami_action.
Local Open Scope kami_expr.
Local Definition testFieldAccess (ty: Kind -> Type): ActionT ty (Bit 10) :=
  (LET val: testStruct <- testStructVal;
     Ret (#val @% "hello"))%kami_action.
Local Close Scope kami_expr.
Local Close Scope kami_action.

Local Definition testFieldUpd (ty: Kind -> Type) := 
  ((testStructVal (ty := ty)) @%[ "hello" <- Const ty (ZToWord 10 23) ])%kami_expr.
