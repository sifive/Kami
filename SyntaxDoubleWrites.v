Require Export Bool Ascii String List FunctionalExtensionality Psatz PeanoNat.
Require Export bbv.Word Kami.Lib.VectorFacts Kami.Lib.EclecticLib Kami.AllNotations.

Export Word.Notations.

Require Import Permutation RecordUpdate.RecordSet.
Require Import ZArith.
Import ListNotations.

Global Set Implicit Arguments.
Global Set Asymmetric Patterns.

Global Open Scope word_scope.
Global Open Scope nat_scope.
Global Open Scope string_scope.
Global Open Scope vector_scope.
Global Open Scope list_scope.
Section DoubleWrites.
Variable o: RegsT.

 Inductive SemActionDoubleWrites:
    forall k, ActionT type k -> RegsT -> RegsT -> MethsT -> type k -> Prop :=
  | SemMCallDoubleWrites
      meth s (marg: Expr type (SyntaxKind (fst s)))
      (mret: type (snd s))
      retK (fret: type retK)
      (cont: type (snd s) -> ActionT type retK)
      readRegs newRegs (calls: MethsT) acalls
      (HAcalls: acalls = (meth, (existT _ _ (evalExpr marg, mret))) :: calls)
      (HSemAction: SemActionDoubleWrites (cont mret) readRegs newRegs calls fret):
      SemActionDoubleWrites (MCall meth s marg cont) readRegs newRegs acalls fret
  | SemLetExprDoubleWrites
      k (e: Expr type k) retK (fret: type retK)
      (cont: fullType type k -> ActionT type retK) readRegs newRegs calls
      (HSemAction: SemActionDoubleWrites (cont (evalExpr e)) readRegs newRegs calls fret):
       SemActionDoubleWrites (LetExpr e cont) readRegs newRegs calls fret
  | SemLetActionDoubleWrites
      k (a: ActionT type k) (v: type k) retK (fret: type retK)
      (cont: type k -> ActionT type retK)
      readRegs newRegs readRegsCont newRegsCont calls callsCont
      (HSemAction: SemActionDoubleWrites a readRegs newRegs calls v)
      (HSemActionCont: SemActionDoubleWrites (cont v) readRegsCont newRegsCont callsCont fret)
      uReadRegs uNewRegs uCalls
      (HReadRegs: uReadRegs = readRegs ++ readRegsCont)
      (HNewRegs: uNewRegs = newRegs ++ newRegsCont)
      (HCalls: uCalls = calls ++ callsCont):
      SemActionDoubleWrites (LetAction a cont) uReadRegs uNewRegs uCalls fret
  | SemReadNondetDoubleWrites
      valueT (valueV: fullType type valueT)
      retK (fret: type retK) (cont: fullType type valueT -> ActionT type retK)
      readRegs newRegs calls
      (HSemAction:  SemActionDoubleWrites (cont valueV) readRegs newRegs calls fret):
       SemActionDoubleWrites (ReadNondet _ cont) readRegs newRegs calls fret
  | SemReadRegDoubleWrites
      (r: string) regT (regV: fullType type regT)
      retK (fret: type retK) (cont: fullType type regT -> ActionT type retK)
      readRegs newRegs calls areadRegs
      (HRegVal: In (r, existT _ regT regV) o)
      (HSemAction:  SemActionDoubleWrites (cont regV) readRegs newRegs calls fret)
      (HNewReads: areadRegs = (r, existT _ regT regV) :: readRegs):
       SemActionDoubleWrites (ReadReg r _ cont) areadRegs newRegs calls fret
  | SemWriteRegDoubleWrites
      (r: string) k
      (e: Expr type k)
      retK (fret: type retK)
      (cont: ActionT type retK) readRegs newRegs calls anewRegs
      (HRegVal: In (r, k) (getKindAttr o))
      (HANewRegs: anewRegs = (r, (existT _ _ (evalExpr e))) :: newRegs)
      (HSemAction:  SemActionDoubleWrites cont readRegs newRegs calls fret):
       SemActionDoubleWrites (WriteReg r e cont) readRegs anewRegs calls fret
  | SemIfElseTrueDoubleWrites
      (p: Expr type (SyntaxKind Bool)) k1
      (a: ActionT type k1)
      (a': ActionT type k1)
      (r1: type k1)
      k2 (cont: type k1 -> ActionT type k2)
      readRegs1 readRegs2  newRegs1 newRegs2 calls1 calls2 (r2: type k2)
      (HTrue: evalExpr p = true)
      (HAction:  SemActionDoubleWrites a readRegs1 newRegs1 calls1 r1)
      (HSemAction:  SemActionDoubleWrites (cont r1) readRegs2 newRegs2 calls2 r2)
      ureadRegs unewRegs ucalls
      (HUReadRegs: ureadRegs = readRegs1 ++ readRegs2)
      (HUNewRegs: unewRegs = newRegs1 ++ newRegs2)
      (HUCalls: ucalls = calls1 ++ calls2) :
      SemActionDoubleWrites (IfElse p a a' cont) ureadRegs unewRegs ucalls r2
  | SemIfElseFalseDoubleWrites
      (p: Expr type (SyntaxKind Bool)) k1
      (a: ActionT type k1)
      (a': ActionT type k1)
      (r1: type k1)
      k2 (cont: type k1 -> ActionT type k2)
      readRegs1 readRegs2 newRegs1 newRegs2 calls1 calls2 (r2: type k2)
      (HFalse: evalExpr p = false)
      (HAction:  SemActionDoubleWrites a' readRegs1 newRegs1 calls1 r1)
      (HSemAction:  SemActionDoubleWrites (cont r1) readRegs2 newRegs2 calls2 r2)
      ureadRegs unewRegs ucalls
      (HUReadRegs: ureadRegs = readRegs1 ++ readRegs2)
      (HUNewRegs: unewRegs = newRegs1 ++ newRegs2)
      (HUCalls: ucalls = calls1 ++ calls2):
       SemActionDoubleWrites (IfElse p a a' cont) ureadRegs unewRegs ucalls r2
  | SemSysDoubleWrites
      (ls: list (SysT type)) k (cont: ActionT type k)
      r readRegs newRegs calls
      (HSemAction:  SemActionDoubleWrites cont readRegs newRegs calls r):
       SemActionDoubleWrites (Sys ls cont) readRegs newRegs calls r
  | SemReturnDoubleWrites
      k (e: Expr type (SyntaxKind k)) evale
      (HEvalE: evale = evalExpr e)
      readRegs newRegs calls
      (HReadRegs: readRegs = nil)
      (HNewRegs: newRegs = nil)
      (HCalls: calls = nil) :
       SemActionDoubleWrites (Return e) readRegs newRegs calls evale.
End DoubleWrites.
