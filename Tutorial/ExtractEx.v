Require Import Kami.All.
Require Import Kami.Tutorial.TacticsEx.

(* Example of how to extract a module to be used by the Haskell simulator *)

Definition IncrMod : BaseModule := IncrementerImpl 5 "test".
(*
Separate Extraction

  getFins
  Fin.to_nat
  fullFormatHex
  fullFormatBinary
  fullFormatDecimal
  readReqName
  readResName
  readRegName
  rfIsWrMask
  rfNum
  rfDataArray
  rfRead
  rfWrite
  rfIdxNum
  rfData
  rfInit
  pack
  unpack

  IncrMod.
*)
