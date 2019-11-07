Require Import Kami.AllNotations.
Require Import Kami.Extraction.
Require Import BinNat.
Import FinFun.Fin2Restrict.

Class toString (X : Type) := {
  to_string : X -> string
  }.

Instance toString_prod{X Y}`{toString X, toString Y} : toString (X * Y) := {|
  to_string := fun '(x,y) => (to_string x ++ "_" ++ to_string y)%string
  |}.

Instance toString_sigma{X}{Y : X -> Type}`{toString X}`{forall x, toString (Y x)} : toString {x : X & Y x} := {|
  to_string := fun '(existT x y) => (to_string x ++ "_" ++ to_string y)%string
  |}.

Definition cart_prod{X Y}(xs : list X)(ys : list Y) : list (X * Y) :=
  concat (map (fun x => map (pair x) ys) xs).

Definition dep_cart_prod{X}{Y : X -> Type}(xs : list X)(ys : forall x, list (Y x)) : list ({x : X & Y x}) :=
  concat (map (fun x => map (fun y => existT Y x y) (ys x)) xs).

Section Params.

Definition num := 5.
Definition idxNum := 20.
Definition Xlen := 32.
Definition Data := Bit Xlen.
Definition Counter := Bit 1.
Definition init_val : word Xlen := Xlen 'h"e".

(* mask = {true; false; false; false; true} *)
Definition mask_func1 : Fin.t num -> bool := fun (i : Fin.t num) =>
  match i with
  | F1 _ => true
  | FS _ (F1 _) => false
  | FS _ (FS _ (F1 _)) => false
  | FS _ (FS _ (FS _ (F1 _))) => false
  | _ => true
  end.

Definition mask_func2 : Fin.t num -> bool := fun i => negb (mask_func1 i).

Definition mask1 : ConstT (Array num Bool) := ConstArray mask_func1.
Definition mask2 : ConstT (Array num Bool) := ConstArray mask_func2.

Definition write_index := 4.
Definition read_under_index := 2.
Definition read_over_index := 6.
Definition read_disjoint_index := 12.

Definition write_val_1 : word Xlen := Xlen 'h"1e".
Definition write_val_2 : word Xlen := Xlen 'h"3e".

(* reality check lemmas *)

(* good read/write indices*)

Lemma read_under_bounds : read_under_index < write_index < read_under_index + num.
Proof.
  cbv delta; lia.
Qed.

Lemma read_over_bounds : read_over_index < write_index + num < read_over_index + num.
Proof.
  cbv delta; lia.
Qed.

Lemma read_disjoint_bounds : write_index + num < read_disjoint_index /\ read_disjoint_index + num < idxNum.
Proof.
  cbv delta; lia.
Qed.

(*good masks*)

Lemma mask1_under_true : exists (i : Fin.t num), mask_func1 i = true /\ f2n i < num - (write_index - read_under_index).
Proof.
  exists F1; simpl; auto.
Qed.

Lemma mask1_under_false : exists (i : Fin.t num), mask_func1 i = false /\ f2n i < num - (write_index - read_under_index).
Proof.
  exists (FS F1); simpl; auto.
Qed.

Lemma mask1_over_true : exists (i : Fin.t num), mask_func1 i = true /\ f2n i > (read_over_index - write_index).
Proof.
  exists (FS (FS (FS (FS F1)))); unfold f2n; simpl; auto.
Qed.

Lemma mask1_over_false : exists (i : Fin.t num), mask_func1 i = false /\ f2n i > (read_over_index - write_index).
Proof.
  exists (FS (FS (FS F1))); unfold f2n; simpl; auto.
Qed.

Lemma mask2_under_true : exists (i : Fin.t num), mask_func2 i = true /\ f2n i < num - (write_index - read_under_index).
Proof.
  exists (FS F1); simpl; auto.
Qed.

Lemma mask2_under_false : exists (i : Fin.t num), mask_func2 i = false /\ f2n i < num - (write_index - read_under_index).
Proof.
  exists F1; simpl; auto.
Qed.

Lemma mask2_over_true : exists (i : Fin.t num), mask_func2 i = true /\ f2n i > (read_over_index - write_index).
Proof.
  exists (FS (FS (FS F1))); unfold f2n; simpl; auto.
Qed.

Lemma mask2_over_false : exists (i : Fin.t num), mask_func2 i = false /\ f2n i > (read_over_index - write_index).
Proof.
  exists (FS (FS (FS (FS F1)))); unfold f2n; simpl; auto.
Qed.

(* good values *)

Lemma init_write1_neq : weqb init_val write_val_1 = false.
Proof.
  auto.
Qed.

Lemma init_write2_neq : weqb init_val write_val_2 = false.
Proof.
  auto.
Qed.

Lemma write1_write2_neq : weqb write_val_1 write_val_2 = false.
Proof.
  auto.
Qed.

End Params.

Section Files.

Inductive FileType :=
  | AsyncF
  | SyncIsAddr
  | SyncNotIsAddr.

Inductive OverlapType :=
  | Over (* write  -----
            read     -----
          *)

  | Under (* write    -----
             read  -----
           *)


  | Disjoint (* write -----
                read        -----
              *)
  .

Inductive MaskType :=
  | IsWrMask
  | NotIsWrMask.

Inductive Schedule :=
  | WriteFirst
  | WriteSecond
  | WriteThird.

Instance toString_FileType : toString FileType := {|
  to_string := fun x => match x with
                        | AsyncF => "async"
                        | SyncIsAddr => "syncIsAddr"
                        | SyncNotIsAddr => "syncNotIsAddr"
                        end
  |}.

Instance toString_OverlapType : toString OverlapType := {|
  to_string := fun x => match x with
                        | Over => "over"
                        | Under => "under"
                        | Disjoint => "disjoint"
                        end
  |}.

Instance toString_MaskType : toString MaskType := {|
  to_string := fun x => match x with
                        | IsWrMask => "isWrMask"
                        | NotIsWrMask => "notIsWrMask"
                        end
  |}.

Instance toString_Schedule : toString Schedule := {|
  to_string := fun x => match x with
                        | WriteFirst => "writeFirst"
                        | WriteSecond => "writeSecond"
                        | WriteThird => "writeThird"
                        end
  |}.

Definition FileTuple := (FileType * Schedule * OverlapType * MaskType)%type.

Definition dataArray_name : FileTuple -> string :=
  fun tup => ("dataArray_" ++ to_string tup)%string.

Definition read_name : FileTuple -> string :=
  fun tup => ("read_" ++ to_string tup)%string.

Definition readReq_name : FileTuple -> string :=
  fun tup => ("readReq_" ++ to_string tup)%string.

Definition readRes_name : FileTuple -> string :=
  fun tup => ("readRes_" ++ to_string tup)%string.

Definition readReg_name : FileTuple -> string :=
  fun tup => ("readReg_" ++ to_string tup)%string.

Definition write_name : FileTuple -> string :=
  fun tup => ("write_" ++ to_string tup)%string.


Definition async_schedules : list (FileType * Schedule) :=
  cart_prod [AsyncF] [WriteFirst; WriteSecond].

Definition syncIsAddr_schedules : list (FileType * Schedule) :=
  cart_prod [SyncIsAddr] [WriteFirst; WriteSecond; WriteThird].

Definition syncNotIsAddr_schedules : list (FileType * Schedule) :=
  cart_prod [SyncNotIsAddr] [WriteFirst; WriteSecond; WriteThird].

(*
Definition file_varieties : list FileTuple :=
  cart_prod (cart_prod file_schedules [Over; Under; Disjoint]) [IsWrMask; NotIsWrMask].
*)

Definition async_file_varieties : list FileTuple :=
  cart_prod (cart_prod async_schedules [Over; Under; Disjoint]) [IsWrMask; NotIsWrMask].

Definition syncIsAddr_file_varieties : list FileTuple :=
  cart_prod (cart_prod syncIsAddr_schedules [Over; Under; Disjoint]) [IsWrMask; NotIsWrMask].

Definition syncNotIsAddr_file_varieties : list FileTuple :=
  cart_prod (cart_prod syncNotIsAddr_schedules [Over; Under; Disjoint]) [IsWrMask; NotIsWrMask].

Definition make_RFB(tup : FileTuple) : RegFileBase :=
  let '(ft,sch,ot,mt) := tup in
    {|
      rfIsWrMask := match mt with
                    | IsWrMask => true
                    | NotIsWrMask => false
                    end;
      rfNum := num;
      rfDataArray := dataArray_name tup;
      rfRead :=  match ft with
                 | AsyncF => Async [read_name tup]
                 | SyncIsAddr => Sync true
                     [
                       {| readReqName := readReq_name tup;
                          readResName := readRes_name tup;
                          readRegName := readReg_name tup
                       |}
                     ]
                 | SyncNotIsAddr => Sync false
                     [
                       {| readReqName := readReq_name tup;
                          readResName := readRes_name tup;
                          readRegName := readReg_name tup
                       |}
                     ]
                 end;
      rfWrite := write_name tup;
      rfIdxNum := idxNum;
      rfData := Data;
      rfInit := RFNonFile idxNum (Some (ConstBit init_val))
    |}.

End Files.

Section Rules.

Local Open Scope kami_expr.
Local Open Scope kami_action. 

Variable tup : FileTuple.

Definition all_init : ConstT (Array num Data) :=
  ConstArray (fun _ => init_val).

Definition expected_read_under(val : word Xlen) : ConstT (Array num Data) :=
    ConstArray (fun i => if f2n i <? write_index - read_under_index then init_val else val).

Definition expected_read_over(val : word Xlen) : ConstT (Array num Data) :=
    ConstArray (fun i => if f2n i <? num - (read_over_index - write_index) then val else init_val).

(*translations*)
Definition read_under_Fin_to_write_Fin(i : Fin.t num) : Fin.t num.
Proof.
  refine (@of_nat_lt (f2n i - (write_index - read_under_index)) num _).
  unfold f2n.
  destruct to_nat.
  simpl; lia.
Defined.

Definition read_over_Fin_to_write_Fin(i : Fin.t num)(pf : (f2n i < num - (read_over_index - write_index))%nat) : Fin.t num.
Proof.
  refine (@of_nat_lt (f2n i + (read_over_index - write_index)) num _).
  unfold f2n.
  unfold f2n in pf.
  destruct to_nat.
  simpl proj1_sig.
  simpl in pf.
  simpl.
  unfold num.
  lia.
Defined.

Definition expected_read_under_masked(mask_val non_mask_val : word Xlen)(mf nmf : Fin.t num -> bool) : ConstT (Array num Data) :=
  ConstArray (fun i => if f2n i <? write_index - read_under_index then init_val else
    if mf (read_under_Fin_to_write_Fin i) then mask_val else 
    if nmf (read_under_Fin_to_write_Fin i) then non_mask_val else init_val).

Definition expected_read_over_masked(mask_val non_mask_val : word Xlen)(mf nmf : Fin.t num -> bool) : ConstT (Array num Data) :=
  ConstArray (fun i => match Compare_dec.le_lt_dec (num - (read_over_index - write_index)) (f2n i) with
                       | left _ => init_val
                       | right pf => if mf (read_over_Fin_to_write_Fin i pf) then mask_val else
                                     if nmf (read_over_Fin_to_write_Fin i pf) then non_mask_val else init_val
                       end).

Definition expected_read_ot_mt(write_val old_val : word Xlen)(wmf omf : Fin.t num -> bool)(ot : OverlapType)(mt : MaskType) :=
  match ot,mt with
  | Over,IsWrMask => expected_read_over_masked write_val old_val wmf omf
  | Over,NotIsWrMask => expected_read_over write_val
  | Under,IsWrMask => expected_read_under_masked write_val old_val wmf omf
  | Under,NotIsWrMask => expected_read_under write_val
  | Disjoint,_ => all_init
  end.

Definition expected_read_val_first_cycle : ConstT (Array num Data) :=
  let '(p,ot,mt) := tup in
    match p with
    | (AsyncF,WriteFirst) => expected_read_ot_mt write_val_1 init_val mask_func1 mask_func2 ot mt
    | (AsyncF,_) => all_init
    | _ => getDefaultConst (Array num Data)
    end.

Definition expected_read_val_second_cycle : ConstT (Array num Data) :=
  let '(p,ot,mt) := tup in
    match p with
    | (AsyncF, WriteFirst) => expected_read_ot_mt write_val_2 write_val_1 mask_func2 mask_func1 ot mt
    | (AsyncF, _) => expected_read_ot_mt write_val_1 init_val mask_func1 (fun _ => true) ot mt
    | (SyncIsAddr, WriteFirst) => expected_read_ot_mt write_val_2 write_val_1 mask_func2 mask_func1 ot mt
    | (SyncIsAddr, WriteSecond) => expected_read_ot_mt write_val_1 init_val mask_func1 (fun _ => true) ot mt
    | (SyncIsAddr, WriteThird) => expected_read_ot_mt write_val_1 init_val mask_func1 (fun _ => true) ot mt
    | (SyncNotIsAddr, WriteFirst) => expected_read_ot_mt write_val_1 init_val mask_func1 (fun _ => true) ot mt
    | (SyncNotIsAddr, WriteSecond) => expected_read_ot_mt write_val_1 init_val mask_func1 (fun _ => true) ot mt
    | (SyncNotIsAddr, WriteThird) => all_init
    end.

Definition make_write : RuleT :=
  let '(ft,sch,ot,mt) := tup in
  match mt with
  | IsWrMask => (("rule_" ++ write_name tup)%string,
      fun ty : (Kind -> Type) =>
        Read c : Counter <- "counter";
        LET write_val <- ITE (#c == $1) $$write_val_2 $$write_val_1;
        LET mask <- ITE (#c == $1) $$mask2 $$mask1;
        Call (write_name tup)(@createWriteRqMask ty idxNum num Data ($write_index) (BuildArray (fun _ => #write_val)) #mask : _);
        Call (("rule_" ++ write_name tup)%string) (@createWriteRqMask ty idxNum num Data ($write_index) (BuildArray (fun _ => #write_val)) #mask : _);
        Retv
      )
  | NotIsWrMask => (("rule_" ++ write_name tup)%string,
      fun ty : (Kind -> Type) =>
        Read c : Counter <- "counter";
        LET write_val <- ITE (#c == $1) $$write_val_2 $$write_val_1;
        Call (write_name tup)(@createWriteRq ty idxNum num Data ($write_index) (BuildArray (fun _ => #write_val)) : _);
        Call (("rule_" ++ write_name tup)%string)(@createWriteRq ty idxNum num Data ($write_index) (BuildArray (fun _ => #write_val)) : _);
        Retv
      )
  end.

Definition print_comparison{ty k}(val exp_val : Expr ty (SyntaxKind k)) : list (SysT ty) :=
  [DispString _ "Read Value:     ";
   DispHex val;
   DispString _ "\n";
   DispString _ "Expected Value: ";
   DispHex exp_val;
   DispString _ "\n";
   DispString _ "Match: ";
   DispHex (Eq val exp_val);
   DispString _ "\n\n"
  ].

Definition print_read{ty}(read_idx : Expr ty (SyntaxKind (Bit (Nat.log2_up idxNum)))) : list (SysT ty) :=
  [DispString _ "Read Index: ";
   DispHex read_idx;
   DispString _ "\n\n"
  ].

Definition make_read : RuleT :=
  let '(ft,sch,ot,mt) := tup in
  let read_index := match ot with
                    | Over => read_over_index
                    | Under => read_under_index
                    | Disjoint => read_disjoint_index
                    end in
  (("rule_" ++ read_name tup)%string,
  fun (ty : Kind -> Type) => 
    Call val : Array num Data <- (read_name tup)($read_index : Bit (Nat.log2_up idxNum));
    Call (("rule_" ++ read_name tup)%string)($read_index : Bit (Nat.log2_up idxNum));
    Read c : Counter <- "counter";
    LET exp_val : Array num Data <- ITE (#c == $1) $$expected_read_val_second_cycle $$expected_read_val_first_cycle;
    System ([DispString _  ("rule_" ++ read_name tup ++ ":\n")%string] ++ print_read ($read_index) ++ print_comparison #val #exp_val);
    Retv
  ).

Definition make_readReq : RuleT :=
  let '(ft,sch,ot,mt) := tup in
  let read_index := match ot with
                    | Over => read_over_index
                    | Under => read_under_index
                    | Disjoint => read_disjoint_index
                    end in
  (("rule_" ++ readReq_name tup)%string,
  fun ty => 
      Call (readReq_name tup)($read_index : Bit (Nat.log2_up idxNum));
      Call (("rule_" ++ readReq_name tup)%string)($read_index : Bit (Nat.log2_up idxNum));
      System ([DispString _  ("rule_" ++ readReq_name tup ++ ":\n")%string] ++ print_read ($read_index));
      Retv
  ).

Definition make_readResp : RuleT :=
  (("rule_" ++ readRes_name tup)%string,
  fun (ty : Kind -> Type) =>
    Call val : Array num Data <- (readRes_name tup)();
    Call (("rule_" ++ readRes_name tup)%string)(#val: _);
    Read c : Counter <- "counter";
    LET exp_val : Array num Data <- ITE (#c == $1) $$expected_read_val_second_cycle $$expected_read_val_first_cycle;
    System [DispString _  ("rule_" ++ readRes_name tup ++ ":\n")%string];
    If (#c == $1) then (System (print_comparison #val #exp_val); Retv);
    Retv
  ).

Definition make_rules : list RuleT :=
  let '(p,ot,mt) := tup in
  match p with
  | (AsyncF, WriteFirst) => [make_write; make_read]
  | (AsyncF, _) => [make_read; make_write]
  | (SyncIsAddr, WriteFirst) => [make_write; make_readResp; make_readReq]
  | (SyncIsAddr, WriteSecond) => [make_readResp; make_write; make_readReq]
  | (SyncIsAddr, WriteThird) => [make_readResp; make_readReq; make_write]
  | (SyncNotIsAddr, WriteFirst) => [make_write; make_readResp; make_readReq]
  | (SyncNotIsAddr, WriteSecond) => [make_readResp; make_write; make_readReq]
  | (SyncNotIsAddr, WriteThird) => [make_readResp; make_readReq; make_write]
  end.

End Rules.

Section TestMod.

Local Open Scope kami_expr.
Local Open Scope kami_action.

Definition all_async_rules : list RuleT :=
  concat (map make_rules async_file_varieties).

Definition all_syncIsAddr_rules : list RuleT :=
  concat (map make_rules syncIsAddr_file_varieties).

Definition all_syncNotIsAddr_rules : list RuleT :=
  concat (map make_rules syncNotIsAddr_file_varieties).

(* registers *)
(* write then read *)

Definition write_reg_WR : RuleT :=
  ("write_reg_WR", fun ty : (Kind -> Type) =>
      Read c : Counter <- "counter";
      LET new_val : Data <- ITE (#c == $1) $$write_val_2 $$write_val_1;
      System ([DispString _  ("write_reg_WR: ")%string; DispHex #new_val; DispString _ "\n\n"]);
      Write "reg_WR" <- #new_val;
      Retv
      ).

Definition read_reg_WR : RuleT :=
  ("read_reg_WR", fun ty : (Kind -> Type) =>
      Read c : Counter <- "counter";
      Read val : Data <- "reg_WR";
      LET exp_val : Data <- ITE (#c == $1) $$write_val_2 $$write_val_1;
      System ([DispString _ "read_reg_WR:\n"] ++ print_comparison #val #exp_val);
      Retv
      ).

(* read then write *)

Definition read_reg_RW : RuleT :=
  ("read_reg_RW", fun ty : (Kind -> Type) =>
      Read c : Counter <- "counter";
      Read val : Data <- "reg_RW";
      LET exp_val : Data <- ITE (#c == $1) $$write_val_1 $$init_val;
      System ([DispString _ "read_reg_RW:\n"] ++ print_comparison #val #exp_val);
      Retv
      ).

Definition write_reg_RW : RuleT :=
  ("write_reg_RW", fun ty : (Kind -> Type) =>
      Read c : Counter <- "counter";
      LET new_val : Data <- ITE (#c == $1) $$write_val_2 $$write_val_1;
      System ([DispString _  "write_reg_RW: "; DispHex #new_val; DispString _ "\n\n"]);
      Write "reg_RW" <- #new_val;
      Retv
      ).

Definition reg_3_rule_1 : RuleT :=
  ("reg_3_write_1", fun ty : (Kind -> Type) =>
      Write "reg_3" <- $$write_val_1;
      Read val : Data <- "reg_3";
      System ([DispString _ "reg_3_write_1:\n"] ++ print_comparison #val $$init_val);
      Retv
      ).

Definition reg_3_rule_2 : RuleT :=
  ("reg_3_write_2", fun ty : (Kind -> Type) =>
      Write "reg_3" <- $$write_val_2;
      Read val : Data <- "reg_3";
      System ([DispString _ "reg_3_write_2:\n"] ++ print_comparison #val $$write_val_1);
      Retv
      ).

Definition reg_3_rule_3 : RuleT :=
  ("reg_3_init", fun ty : (Kind -> Type) =>
      Write "reg_3" <- $$init_val;
      Read val : Data <- "reg_3";
      System ([DispString _ "reg_3_init:\n"] ++ print_comparison #val $$write_val_2);
      Retv
      ).

(* counter rule*)

Definition counter : RuleT :=
  ("counter", fun ty : (Kind -> Type) =>
      Read c : Counter <- "counter";
      System [DispString _ "End of cycle "; DispHex #c; DispString _ "\n"];
      Call "finished"(#c: Counter);
      If(#c == $1) then
        System [DispString _ "Finished.\n"; Finish _]; Retv
      else
        Write "counter" <- #c + $1;
        Retv;
        Retv).

Definition all_reg_rules := [write_reg_WR; read_reg_WR; read_reg_RW; write_reg_RW; reg_3_rule_1; reg_3_rule_2; reg_3_rule_3].

Definition testRegBaseMod := BaseMod [
  ("reg_WR", (existT _ (SyntaxKind _) (Some (SyntaxConst init_val))));
  ("reg_RW", (existT _ (SyntaxKind _) (Some (SyntaxConst init_val))));
  ("reg_3", (existT _ (SyntaxKind _) (Some (SyntaxConst init_val))));
  ("counter", (existT _ (SyntaxKind (Counter)) (Some (SyntaxConst (getDefaultConst _)))))
  ]
 (all_reg_rules ++ [counter]) [].

Definition testAsyncBaseMod := BaseMod [
  ("counter", (existT _ (SyntaxKind (Counter)) (Some (SyntaxConst (getDefaultConst _)))))
  ]
  (all_async_rules ++ [counter]) [].

Definition testSyncIsAddrBaseMod := BaseMod [
  ("counter", (existT _ (SyntaxKind (Counter)) (Some (SyntaxConst (getDefaultConst _)))))
  ]
  (all_syncIsAddr_rules ++ [counter]) [].

Definition testSyncNotIsAddrBaseMod := BaseMod [
  ("counter", (existT _ (SyntaxKind (Counter)) (Some (SyntaxConst (getDefaultConst _)))))
  ]
  (all_syncNotIsAddr_rules ++ [counter]) [].

Definition testAsyncRFs := map make_RFB async_file_varieties.

Definition testSyncIsAddrRFs := map make_RFB syncIsAddr_file_varieties.

Definition testSyncNotIsAddrRFs := map make_RFB syncNotIsAddr_file_varieties.

Definition mkTestMod(bm : BaseModule)(rfs : list RegFileBase) :=
  let md := (fold_right ConcatMod bm (map (fun m => Base (BaseRegFile m)) rfs)) in
  createHideMod md (map fst (getAllMethods md)).

Definition testRegMod := mkTestMod testRegBaseMod [].

Definition testAsyncMod := mkTestMod testAsyncBaseMod testAsyncRFs.

Definition testSyncIsAddrMod := mkTestMod testSyncIsAddrBaseMod testSyncIsAddrRFs.

Definition testSyncNotIsAddrMod := mkTestMod testSyncNotIsAddrBaseMod testSyncNotIsAddrRFs.

End TestMod.