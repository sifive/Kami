Require Import Kami.AllNotations.
Require Import Kami.Extraction.

Section TestMod.

  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Definition rf_a : RegFileBase := {|
    rfIsWrMask := false;
    rfNum := 10;
    rfDataArray := "dataArray_a";
    rfRead := Async ["read_a_1"; "read_a_2"];
    rfWrite := "write_a";
    rfIdxNum := 100;
    rfData := Bit 3;
    rfInit := RFNonFile _ (Some (getDefaultConst _))
    |}.

  Definition rf_b : RegFileBase := {|
    rfIsWrMask := true;
    rfNum := 5;
    rfDataArray := "dataArray_b";
    rfRead := Sync false [
      {| readReqName := "readRq_b_1";
         readResName := "readRs_b_1";
         readRegName := "readRg_b_1"
      |};
      {| readReqName := "readRq_b_2";
         readResName := "readRs_b_2";
         readRegName := "readRg_b_2"
      |}
      ];
    rfWrite := "write_b";
    rfIdxNum := 20;
    rfData := Bool;
    rfInit := RFNonFile _ (Some (ConstBool false))
    |}.

  Definition rf_c : RegFileBase := {|
    rfIsWrMask := false;
    rfNum := 7;
    rfDataArray := "dataArray_c";
    rfRead := Sync true [
      {| readReqName := "readRq_c_1";
         readResName := "readRs_c_1";
         readRegName := "readRg_c_1"
      |};
      {| readReqName := "readRq_c_2";
         readResName := "readRs_c_2";
         readRegName := "readRg_c_2"
      |}
      ];
    rfWrite := "write_c";
    rfIdxNum := 128;
    rfData := Array 10 (Bit 5);
    rfInit := RFNonFile _ (Some (getDefaultConst _))
    |}.

  Definition TestBaseMod :=
    MODULE {
      Register "reg" : Bool <- false
      with Rule "rule1" := (
        Read x <- "reg";
        Write "reg" <- (!#x);
        Retv
        )
      with Rule "rule2" := (
        Call x : Array 10 (Bit 3) <- "read_a_1"($13 : Bit (Nat.log2_up 100));
        System ([DispHex #x]);
        Retv
        )
      with Rule "rule3" := (
        Call "write_a"(@createWriteRq _ 100 10 (Bit 3) ($33) (Const _ (getDefaultConst _)) : _);
        System ([DispString _ "executed rule3"]);
        Retv
        )
      with Rule "rule4" := (
        Call "readRq_b_2"($5 : Bit (Nat.log2_up 20));
        Retv
        )
      with Rule "rule5" := (
        Call x : Array 5 Bool <- "readRs_b_2"();
        Retv
        )
      with Rule "rule6" := (
        Call "write_b" (@createWriteRq _ 20 5 Bool ($4) (Const _ (getDefaultConst _)) : _);
        Retv
        )
      with Rule "rule7" := (
        Call "readRq_c_1"($3 : Bit (Nat.log2_up 128));
        Retv
        )
      with Rule "rule8" := (
        Call x : Array 7 (Array 10 (Bit 5)) <- "readRs_c_1"();
        Retv
        )
      with Rule "rule9" := (
        Call "write_c"(@createWriteRq _ 128 7 (Array 10 (Bit 5)) ($11) (Const _ (getDefaultConst _)) : _);
        Retv
        )
       }.

  Definition TestMod : Mod := let md := (fold_right ConcatMod TestBaseMod (map (fun m => Base (BaseRegFile m))
   [rf_a;rf_b;rf_c])) in createHideMod md (map fst (getAllMethods md)).

End TestMod.