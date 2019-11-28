Require Import Kami.Notations.
Require Import Kami.Syntax.
Require Import List.
(*
 * kami_rewrites_reflection.v
 *
 * Code to perform all the rewrites in kami_rewrites_db by reflection
 *)
Inductive KRTyp : Type :=
  | KRTypModuleElt: KRTyp
  | KRTypRegInitT: KRTyp
  | KRTypAttributeActionVoid: KRTyp
  | KRTypDefMethT: KRTyp
  | KRList: KRTyp -> KRTyp.

Fixpoint KRrealize (t: KRTyp) :=
  match t with
  | KRTypModuleElt => ModuleElt
  | KRTypRegInitT => RegInitT
  | KRTypAttributeActionVoid => Attribute (Action Void)
  | KRTypDefMethT => DefMethT
  | KRList t => list (KRrealize t)
  end.

Inductive KRExp : KRTyp -> Type :=
  | KRVar t : (KRrealize t) -> KRExp t
  | KRCons t : KRExp t -> KRExp (KRList t) -> KRExp (KRList t)
  | KRApp t : KRExp (KRList t) -> KRExp (KRList t) -> KRExp (KRList t)
  | KRMERegister : KRExp KRTypRegInitT -> KRExp KRTypModuleElt
  | KRRegisters : KRExp (KRList KRTypRegInitT) -> KRExp (KRList KRTypModuleElt)
  | KRMERule : KRExp KRTypAttributeActionVoid -> KRExp KRTypModuleElt
  | KRMEMeth : KRExp KRTypDefMethT -> KRExp KRTypModuleElt
  | KRMakeModule_rules : KRExp (KRList KRTypModuleElt) -> KRExp (KRList KRTypAttributeActionVoid)
  | KRMakeModule_regs : KRExp (KRList KRTypModuleElt) -> KRExp (KRList KRTypRegInitT)
  | KRMakeModule_meths : KRExp (KRList KRTypModuleElt) -> KRExp (KRList KRTypDefMethT).

