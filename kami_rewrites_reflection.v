Require Import Kami.Notations.
Require Import Kami.Syntax.
Require Import List.
(*
 * kami_rewrites_reflection.v
 *
 * Code to perform all the rewrites in kami_rewrites_db by reflection
 *)

Inductive KRElem: Type :=
| KRRegInitT : KRElem
| KRRule : KRElem
| KRMeth : KRElem.

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

Inductive KRExp: Type :=
  | KRNil (t:KRTyp) : @KRExp
  | KRVar (t:KRTyp) : KRrealizeType t -> @KRExp
  | KRCons (t:KRTyp) : @KRExp -> @KRExp-> @KRExp
  | KRApp (t:KRTyp) : @KRExp -> @KRExp -> @KRExp
  | KRMERegister : @KRExp -> @KRExp
  | KRRegisters : @KRExp -> @KRExp
  | KRMERule : @KRExp -> @KRExp
  | KRMEMeth : @KRExp -> @KRExp
  | KRMakeModule_rules : @KRExp -> @KRExp
  | KRMakeModule_regs : @KRExp -> @KRExp
  | KRMakeModule_meths : @KRExp -> @KRExp.

Fixpoint KRExpType (e: KRExp) :=
  match e in KRExp return KRTyp with
  | KRNil t => KRList t
  | KRVar t e => t
  | KRCons t a b => (KRList t)
  | KRApp t a b => (KRList t)
  | KRMERegister e => KRTypModuleElt
  | KRRegisters l => (KRList KRTypModuleElt)
  | KRMERule r => KRTypModuleElt
  | KRMEMeth m => KRTypModuleElt
  | KRMakeModule_rules r => KRList KRTypAttributeActionVoid
  | KRMakeModule_regs r => KRList KRTypDefMethT
  | KRMakeModule_meths m => KRList KRTypModuleElt
  end.

Fixpoint KRRealizeExp {typ} (e: KRExp) : option (KRrealizeType typ).
refine
  match e in KRExp return option (@KRrealizeType typ) with
  | KRNil t => match typ with
               | KRList x => Some (@nil (KRrealizeType x))
               | _ => None
               end
  | KRVar t e => _
  | KRCons t a b => match typ,@KRRealizeExp t a,@KRRealizeExp (KRList t) b with
                    | (KRList t),Some f,Some r => _
                    | _,_,_ => None
                    end
  | KRApp t a b => match typ,@KRRealizeExp (KRList t) a,@KRRealizeExp (KRList t) b with
                    | (KRList t),Some f,Some r => _
                    | _,_,_ => None
                    end
  | KRMERegister e => match typ,@KRRealizeExp KRTypRegInitT e with
                     | KRTypModuleElt,Some p => Some (MERegister p)
                     | _,_ => None
                     end
  | KRMERule e => match typ,@KRRealizeExp KRTypAttributeActionVoid e with
                  | KRTypModuleElt,Some p => Some (MERule p)
                  | _,_ => None
                  end
  | KRMEMeth e => match typ,@KRRealizeExp KRTypDefMethT e with
                  | KRTypModuleElt,Some p => Some (MEMeth p)
                  | _,_ => None
                  end
  | KRMakeModule_rules e => match typ,@KRRealizeExp (KRList KRTypModuleElt) e with
                            | (KRList KRTypAttributeActionVoid),Some p => Some (makeModule_rules p)
                            | _,_ => None
                            end
  | KRMakeModule_meths e => match typ,@KRRealizeExp (KRList KRTypModuleElt) e with
                            | (KRList KRTypDefMethT),Some p => Some (makeModule_meths p)
                            | _,_ => None
                            end
  | KRMakeModule_regs e => match typ,@KRRealizeExp (KRList KRTypModuleElt) e with
                            | (KRList KRTypRegInitT),Some p => Some (makeModule_regs p)
                            | _,_ => None
                            end
  | KRRegisters l => match typ,@KRRealizeExp (KRList KRTypRegInitT) l with
                     | KRList KRTypModuleElt,Some p => Some (Registers p)
                     | _,_ => None
                     end
  end.
  + assert ({t=typ}+{t<>typ}).
    decide equality.
    destruct H.
    - subst.
      apply (Some e).
    - apply None.
  + assert ({t=t0}+{t<>t0}).
    decide equality.
    destruct H.
    - subst.
      apply (Some (@cons (KRrealizeType t0) f r)).
    - apply None.
  + assert ({t=t0}+{t<>t0}).
    decide equality.
    destruct H.
    - subst.
      apply (Some (@app (KRrealizeType t0) f r)).
    - apply None.
Defined.

Definition KRDenote {typ} e def :=
  match @KRRealizeExp typ e with
  | Some x => x
  | _ => def
  end.

Ltac KRReifyExp e t :=
  match e with
  | nil => constr:(@KRNil t)
  | cons ?F nil => match t with
                  | KRList ?T => let fr :=ltac:(KRReifyExp F T) in
                                 constr:(@KRCons T fr (@KRNil T))
                  | ?T => constr:(@KRVar t e)
                  end
  | cons ?F ?R => match t with
                  | KRList ?T => let fr :=ltac:(KRReifyExp F T) in
                                 let re:=ltac:(KRReifyExp R t) in
                                 constr:(@KRCons T fr re)
                  | ?T => constr:(@KRVar t e)
                  end
  | app ?F ?R => let x1 := ltac:(KRReifyExp F t) in
                 let x2 := ltac:(KRReifyExp R t) in
                 match t with
                 | KRList ?T => constr:(@KRApp T x1 x2)
                 | ?T => constr:(@KRVar t e)
                 end
  | MERegister ?E => let x := ltac:(KRReifyExp E KRTypRegInitT) in
                         constr:(@KRMERegister x)
  | Registers ?E => let x := ltac:(KRReifyExp E (KRList KRTypRegInitT)) in
                       constr:(@KRRegisters x)
  | MERule ?E => let  x := ltac:(KRReifyExp E KRTypAttributeActionVoid) in
                     constr:(@KRMERule x)
  | MEMeth ?E => let x := ltac:(KRReifyExp E KRTypDefMethT) in
                     constr:(@KRMEMeth x)
  | makeModule_rules ?E => let x := ltac:(KRReifyExp E (KRList KRTypModuleElt)) in
                               constr:(@KRMakeModule_rules x)
  | makeModule_regs ?X => let x := ltac:(KRReifyExp X (KRList KRTypModuleElt)) in
                              constr:(@KRMakeModule_regs x)
  | makeModule_meths ?E => let x := ltac:(KRReifyExp E (KRList KRTypModuleElt)) in 
                              constr:(@KRMakeModule_meths x)
  | ?X => constr:(@KRVar t X)
  end.



Axiom cheat: forall x, x.

(*Fixpoint KRSimplifyTop2 t' (x:KRExp t'): KRExp t'.
  refine
  match x in KRExp t' return KRExp t' with
  | KRNil t => KRNil t
  | KRVar t e => KRVar t e
  | KRCons t a b => KRCons a b
  | KRApp t a b => match a in KRExp (KRList t') return
                         KRExp (KRList t') -> KRExp (KRList t') with
                   | KRCons t'' a' b' => fun b => KRCons a' (KRApp b' b)
                   | KRNil t => fun b => b
                   | KRVar _ _ => cheat _
                   | q => fun b => KRApp q b
                   end b
  (* | KRVar t e => e *)
  (* | KRCons t a b => @cons (@KRrealizeType t) (@KRRealizeExp t a) (@KRRealizeExp (KRList t) b) *)
  (* | KRApp t a b => @app (@KRrealizeType t) (@KRRealizeExp (KRList t) a) (@KRRealizeExp (KRList t) b) *)
  (* | KRMERegister e => MERegister (@KRRealizeExp KRTypRegInitT e) *)
  (* | KRMERule r => MERule (@KRRealizeExp KRTypAttributeActionVoid r) *)
  (* | KRMEMeth m => MEMeth (@KRRealizeExp KRTypDefMethT m) *)
  (* | KRMakeModule_rules r => makeModule_rules (KRRealizeExp r) *)
  (* | KRMakeModule_regs r => makeModule_regs (KRRealizeExp r) *)
  (* | KRMakeModule_meths m =>makeModule_meths (KRRealizeExp m) *)
                     (* | KRRegisters l => Registers (KRRealizeExp l) *)
  | _ => cheat _
  end.

  (*| @KRApp tp a b => match tp in KRTyp return KRTyp with
                     | KRTypModuleElt => @KRApp KRTypRegInitT (KRMakeModule_regs a) (KRMakeModule_regs b)
                     | _ => @KRMakeModule_regs x
                     end*)
  (*| @KRCons KRTypRegInitT aa  b => match aa in (KRExp KRTypRegInitT) with
                                   | KRMERegister a => @KRCons KRTypRegInitT a (KRMakeModule_regs b)
                                   | _ => @KRMakeModule_regs x
                                   end*)
  | @KRNil tp => cheat _
      (*match tp return KRExp (KRList KRTypRegInitT) with
                 | _ => @KRMa
                 end*)
  | _ => @KRMakeModule_regs x
  end.
                 (*| KRTypModuleElt => @KRNil KRTypRegInitT*)
  *)

Fixpoint KRSimplifyTop (e : KRExp) :=
  match e with
  | KRApp tp (KRCons tp2 a b) c => KRCons tp a (KRApp tp b c)
  | KRRegisters (KRApp KRTypRegInitT a b) => KRApp KRTypModuleElt (KRRegisters a) (KRRegisters b)
  | KRRegisters (KRCons KRTypRegInitT a b) => KRCons KRTypModuleElt (KRMERegister a) (KRRegisters b)
  | KRRegisters (KRNil KRTypRegInitT) => KRNil KRTypModuleElt
  | KRMakeModule_regs (KRNil KRTypModuleElt) => KRNil KRTypRegInitT
  | KRMakeModule_regs (KRCons KRTypModuleElt (KRMERegister a) b) => KRCons KRTypRegInitT a (KRMakeModule_regs b)
  | KRMakeModule_regs (KRApp KRTypModuleElt a b) => KRApp KRTypRegInitT (KRMakeModule_regs a) (KRMakeModule_regs b)
  | _ => e
  end.

Fixpoint KRSimplify (e: KRExp) :=
  match e with
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


Theorem KRSimplifySound: forall t e d, @KRDenote t e d = @KRDenote t (@KRSimplify e) d.
Admitted.

Ltac KRSimplifyTac t e :=
  match goal with
  | |- ?A = ?B =>
      let x := (ltac:(KRReifyExp e t)) in
          replace A with (KRRealizeExp x);[(rewrite KRSimplifySound;cbv [KRRealizeExp]) | (cbv [KRSimplify KRSimplifyTop];reflexivity)]
  end.
  (*let x := ltac:(KRReifyExp e) in
      (replace e with (KRRealizeExp x);[cbv [KRSimplify KRSimplifySound];reflexivity | replace (KRRealizeExp x) with (KRRealizeExp (KRSimplify x));[rewrite KRSimplifySound;reflexivity | compute]]).
*)

Check KRDenote.

Goal forall a b c d e, Registers ([a;b]++[c;d])=e.
  intros.
  (*match goal with
  | |- ?A = ?B => 
      let x := (ltac:(KRReifyExp A (KRList KRTypRegInitT))) in
          replace A with (KRRealizeExp x);[(rewrite KRSimplifySound;cbv [KRRealizeExp KRSimplify KRSimplifyTop]) | cbv [KRRealizeExp];reflexivity]
  end.*)
  match goal with
  | |- ?A = ?B => 
      let x := (ltac:(KRReifyExp A (KRList KRTypModuleElt))) in
          change A with (@KRDenote (KRList KRTypModuleElt) x nil);rewrite KRSimplifySound
  end.
  cbv [KRSimplify KRSimplifyTop KRDenote KRRealizeExp].
Abort.

(*Goal forall a b c d e, makeModule_regs [MERegister a;MERule b;MEMeth c;MERegister d]=e.
  intros.
  (*match goal with
  | |- ?A = ?B => 
      let x := (ltac:(KRReifyExp A (KRList KRTypRegInitT))) in
          replace A with (KRRealizeExp x);[(rewrite KRSimplifySound;cbv [KRRealizeExp KRSimplify KRSimplifyTop]) | cbv [KRRealizeExp];reflexivity]
  end.*)
  match goal with
  | |- ?A = ?B => 
      let x := (ltac:(KRReifyExp A (KRList KRTypRegInitT))) in
          change A with (KRRealizeExp x);rewrite KRSimplifySound
  end.
  cbv [KRSimplify KRSimplifyTop KRRealizeExp].

Abort.*)

(*Fixpoint KRSimplifyTop {t} (e : KRExp t) :=
  match e in KRExp t return KRExp t with
  (*| KRApp KRTypModuleElt (KRCons KRTypModuleElt a b) c => @KRCons KRTypModuleElt a (@KRApp KRTypModuleElt b c)
  | KRRegisters (KRCons KRTypRegInitT a b) => @KRCons KRTypModuleElt (KRMERegister a) (KRRegisters b)
  | KRRegisters (@KRApp KRTypRegInitT a b) => @KRApp KRTypModuleElt (KRRegisters a) (KRRegisters b)*)
  | @KRRegisters (@KRNil KRTypModuleElt) => @KRNil KRTypModuleElt
  | e => e
  end.*)

