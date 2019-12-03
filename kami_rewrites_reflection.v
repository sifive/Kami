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

Fixpoint KRrealizeType (t: KRTyp) :=
  match t with
  | KRTypModuleElt => ModuleElt
  | KRTypRegInitT => RegInitT
  | KRTypAttributeActionVoid => Attribute (Action Void)
  | KRTypDefMethT => DefMethT
  | KRList t => list (KRrealizeType t)
  end.

Inductive KRExp: KRTyp -> Type :=
  | KRNil t : @KRExp (KRList t)
  | KRVar t : (KRrealizeType t) -> @KRExp t
  | KRCons t : @KRExp t -> @KRExp (KRList t) -> @KRExp (KRList t)
  | KRApp t : @KRExp (KRList t) -> @KRExp (KRList t) -> @KRExp (KRList t)
  | KRMERegister : @KRExp KRTypRegInitT -> @KRExp KRTypModuleElt
  | KRRegisters : @KRExp (KRList KRTypRegInitT) -> @KRExp (KRList KRTypModuleElt)
  | KRMERule : @KRExp KRTypAttributeActionVoid -> @KRExp KRTypModuleElt
  | KRMEMeth : @KRExp KRTypDefMethT -> @KRExp KRTypModuleElt
  | KRMakeModule_rules : @KRExp (KRList KRTypModuleElt) -> @KRExp (KRList KRTypAttributeActionVoid)
  | KRMakeModule_regs : @KRExp (KRList KRTypModuleElt) -> @KRExp (KRList KRTypRegInitT)
  | KRMakeModule_meths : @KRExp (KRList KRTypModuleElt) -> @KRExp (KRList KRTypDefMethT).

Fixpoint KRRealizeExp {t} (e: KRExp t) :=
  match e in KRExp t return (KRrealizeType t) with
  | KRNil t => @nil (@KRrealizeType t)
  | KRVar t e => e
  | KRCons t a b => @cons (@KRrealizeType t) (@KRRealizeExp t a) (@KRRealizeExp (KRList t) b)
  | KRApp t a b => @app (@KRrealizeType t) (@KRRealizeExp (KRList t) a) (@KRRealizeExp (KRList t) b)
  | KRMERegister e => MERegister (@KRRealizeExp KRTypRegInitT e)
  | KRRegisters l => Registers (@KRRealizeExp (KRList KRTypRegInitT) l)
  | KRMERule r => MERule (@KRRealizeExp KRTypAttributeActionVoid r)
  | KRMEMeth m => MEMeth (@KRRealizeExp KRTypDefMethT m)
  | KRMakeModule_rules r => makeModule_rules (@KRRealizeExp (KRList KRTypModuleElt) r)
  | KRMakeModule_regs r => makeModule_regs (@KRRealizeExp (KRList KRTypModuleElt) r)
  | KRMakeModule_meths m =>makeModule_meths (@KRRealizeExp (KRList KRTypModuleElt) m)
  end.

Ltac KRReifyExp e t :=
  match e with
  | nil => constr:(@KRNil t)
  | cons ?F ?R => match t with
                  | KRList ?T => constr:(@KRCons T (ltac:(KRReifyExp F T)) (ltac:(KRReifyExp R t)))
                  | ?T => constr:(@KRVar t e)
                  end
  | app ?F ?R => match t with
                 | KRList ?T => constr:(@KRApp T (ltac:(KRReifyExp F t)) (ltac:(KRReifyExp R t)))
                 | ?T => constr:(@KRVar t e)
                 end
  | ?X => constr:(@KRVar t X)
  | MERegister ?E => match t with
                     | KRTypModuleElt => constr:(@KRMERegister (ltac:(KRReifyExp E KRTypRegInitT)))
                     | ?T => constr:(@KRVar t e)
                     end
  | Registers ?E => match t with
                    | KRList KRTypModuleElt => constr:(@KRRegisters (ltac:(KRReifyExp E (KRList KRTypRegInitT))))
                    | ?T => constr:(@KRVar t e)
                    end
  | MERule ?E => match t with
                 | KRTypModuleElt => constr:(@KRMERule (ltac:(KRReifyExp E KRTypAttributeActionVoid)))
                 | ?T => constr:(@KRVar t e)
                 end
  | MEMeth ?E => match t with
                 | KRTypModuleElt => constr:(@KRMEMeth (ltac:(KRReifyExp E KRTypDefMethT)))
                 | ?T => constr:(@KRVar t e)
                 end
  | makeModule_rules ?E => match t with
                           | KRList KRTypAttributeActionVoid => constr:(@KRMakeModule_rules (ltac:(KRReifyExp E (KRList KRTypModuleElt))))
                           | ?T => constr:(@KRVar t e)
                           end
  | makeModule_regs ?E => match t with
                          | KRList KRTypRegInitT => constr:(@KRMakeModule_regs (ltac:(KRReifyExp E (KRList KRTypModuleElt))))
                          | ?T => constr:(@KRVar t e)
                          end
  | makeModule_meths ?E => match t with
                          | KRList KRTypDefMethT => constr:(@KRMakeModule_meths (ltac:(KRReifyExp E (KRList KRTypModuleElt))))
                          | ?T => constr:(@KRVar t e)
                          end
  end.

Fixpoint KRSimplifyTop {t} (e : KRExp t) :=
  match e in KRExp t return KRExp t with
  | @KRApp KRTypModuleElt f c => match f with
                                 | @KRCons KRTypModuleElt a b => @KRCons KRTypModuleElt a (@KRApp KRTypModuleElt b c)
                                 | _ => @KRApp KRTypModuleElt f c
                                 end
  | KRRegisters x => match x with
                     | @KRApp KRTypRegInitT a b => @KRApp KRTypModuleElt (KRRegisters a) (KRRegisters b)
                     | @KRCons KRTypRegInitT a b => @KRCons KRTypModuleElt (KRMERegister a) (KRRegisters b)
                     | KRNil KRTypModuleElt => KRNil KRTypModuleElt
                     | e => KRRegisters e
                     end
  | e => e
  end.

Fixpoint KRSimplify {t} (e: KRExp t) :=
  match e in KRExp t return KRExp t with
  | @KRCons t a b => KRSimplifyTop (@KRCons t (KRSimplify a) (KRSimplify b))
  | @KRApp t a b => KRSimplifyTop (@KRApp t (KRSimplify a) (KRSimplify b))
  | @KRMERegister a => KRSimplifyTop (@KRMERegister (KRSimplify a))
  | @KRRegisters a => KRSimplifyTop (@KRRegisters (KRSimplify a))
  | @KRMEMeth a => KRSimplifyTop (@KRMEMeth (KRSimplify a))
  | @KRMERule a => KRSimplifyTop (@KRMERule (KRSimplify a))
  | @KRMakeModule_rules a => KRSimplifyTop (@KRMakeModule_rules (KRSimplify a))
  | @KRMakeModule_regs a => KRSimplifyTop (@KRMakeModule_regs (KRSimplify a))
  | @KRMakeModule_meths a => KRSimplifyTop (@KRMakeModule_meths (KRSimplify a))
  | e => e
  end.


Theorem KRSimplifySound: forall t e, @KRRealizeExp t e = @KRRealizeExp t (@KRSimplify t e).
Admitted.

(*Fixpoint KRSimplifyTop {t} (e : KRExp t) :=
  match e in KRExp t return KRExp t with
  (*| KRApp KRTypModuleElt (KRCons KRTypModuleElt a b) c => @KRCons KRTypModuleElt a (@KRApp KRTypModuleElt b c)
  | KRRegisters (KRCons KRTypRegInitT a b) => @KRCons KRTypModuleElt (KRMERegister a) (KRRegisters b)
  | KRRegisters (@KRApp KRTypRegInitT a b) => @KRApp KRTypModuleElt (KRRegisters a) (KRRegisters b)*)
  | @KRRegisters (@KRNil KRTypModuleElt) => @KRNil KRTypModuleElt
  | e => e
  end.*)

