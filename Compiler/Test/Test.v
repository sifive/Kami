Require Import Kami.AllNotations.
Require Import Kami.Extraction.

Section TestMod.

  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Definition rf_async : RegFileBase := {|
    rfIsWrMask := false;
    rfNum := 10;
    rfDataArray := "dataArray_async";
    rfRead := Async ["read_async_1"; "read_async_2_nc"];
    rfWrite := "write_async";
    rfIdxNum := 100;
    rfData := Bit 3;
    rfInit := RFNonFile _ (Some (getDefaultConst _))
    |}.

  Definition rf_notIsAddr : RegFileBase := {|
    rfIsWrMask := true;
    rfNum := 5;
    rfDataArray := "dataArray_notIsAddr";
    rfRead := Sync false [
      {| readReqName := "readRq_notIsAddr_1_nc";
         readResName := "readRs_notIsAddr_1_nc";
         readRegName := "readRg_notIsAddr_1_nc"
      |};
      {| readReqName := "readRq_notIsAddr_2";
         readResName := "readRs_notIsAddr_2";
         readRegName := "readRg_notIsAddr_2"
      |}
      ];
    rfWrite := "write_notIsAddr";
    rfIdxNum := 20;
    rfData := Bool;
    rfInit := RFNonFile _ (Some (ConstBool false))
    |}.

  Definition rf_isAddr : RegFileBase := {|
    rfIsWrMask := false;
    rfNum := 7;
    rfDataArray := "dataArray_isAddr";
    rfRead := Sync true [
      {| readReqName := "readRq_isAddr_1";
         readResName := "readRs_isAddr_1";
         readRegName := "readRg_isAddr_1"
      |};
      {| readReqName := "readRq_isAddr_2_nc";
         readResName := "readRs_isAddr_2_nc";
         readRegName := "readRg_isAddr_2_nc"
      |}
      ];
    rfWrite := "write_isAddr";
    rfIdxNum := 128;
    rfData := Array 10 (Bit 5);
    rfInit := RFNonFile _ (Some (getDefaultConst _))
    |}.

  Definition TestBaseMod :=
    MODULE {
      Register "my_reg" : Bool <- false

      with Rule "rule0" := (
        Read x: Bool <- "my_reg";
        System ([DispString _ "read "; DispHex #x]);
        Retv
        )    

      with Rule "rule1" := (
        Read x: Bool <- "my_reg";          
        Write "my_reg" <- (!#x);
        System ([DispString _ "read "; DispHex #x; DispString _ "\nrule0 write "; DispHex (!#x)]);
        Retv
        )

      with Rule "rule2" := (
        Call x : Array 10 (Bit 3) <- "read_async_1"($13 : Bit (Nat.log2_up 100));
        Retv
        )

      with Rule "rule3" := (
        Call "write_async"(@createWriteRq _ 100 10 (Bit 3) ($33) (Const _ (getDefaultConst _)) : _);
        System ([DispString _ "executed rule3"]);
        Retv
        )

      with Rule "rule4" := (
        Call "readRq_notIsAddr_2"($5 : Bit (Nat.log2_up 20));
        Retv
        )

      with Rule "rule5" := (
        Call x : Array 5 Bool <- "readRs_notIsAddr_2"();
        Retv
        )

      with Rule "rule6" := (
        Call "write_notIsAddr" (@createWriteRqMask _ 20 5 Bool ($4) (Const _ (getDefaultConst _)) (Const _ (ConstArray (fun _ => true))) : _);
        Retv
        )

      with Rule "rule7" := (
        Call "readRq_isAddr_1"($3 : Bit (Nat.log2_up 128));
        Retv
        )

      with Rule "rule8" := (
        Call x : Array 7 (Array 10 (Bit 5)) <- "readRs_isAddr_1"();
        Retv
        )

      with Rule "rule9" := (
        Call "write_isAddr"(@createWriteRq _ 128 7 (Array 10 (Bit 5)) ($11) (Const _ (getDefaultConst _)) : _);
        Retv
        )
       }.

  Definition testMod : Mod := let md := (fold_right ConcatMod TestBaseMod (map (fun m => Base (BaseRegFile m))
   [rf_async;rf_notIsAddr;rf_isAddr])) in createHideMod md (map fst (getAllMethods md)).

End TestMod.
