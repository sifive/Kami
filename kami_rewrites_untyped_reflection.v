Require Import Kami.Notations.
Require Import Kami.Syntax.
Require Import List.
Require Import Kami.Notations_rewrites.
Require Import Program.Equality.

Inductive KRExpr_RegInitT: Type :=
  | KRVar_RegInitT : RegInitT -> KRExpr_RegInitT

with KRExpr_Rule: Type :=
  | KRVar_Rule : Attribute (Action Void) -> KRExpr_Rule

with KRExpr_DefMethT: Type :=
  | KRVar_DefMethT : DefMethT -> KRExpr_DefMethT

with KRExpr_ModuleElt: Type :=
  | KRVar_ModuleElt : ModuleElt -> KRExpr_ModuleElt
  | KRMERegister : KRExpr_RegInitT -> KRExpr_ModuleElt
  | KRMERule : KRExpr_Rule -> KRExpr_ModuleElt
  | KRMEMeth : KRExpr_DefMethT -> KRExpr_ModuleElt

with KRExpr_list_RegInitT: Type :=
  | KRVar_list_RegInitT : list RegInitT -> KRExpr_list_RegInitT
  | KRNil_list_RegInitT : KRExpr_list_RegInitT
  | KRCons_list_RegInitT : KRExpr_RegInitT -> KRExpr_list_RegInitT -> KRExpr_list_RegInitT
  | KRApp_list_RegInitT : KRExpr_list_RegInitT -> KRExpr_list_RegInitT -> KRExpr_list_RegInitT
  | KRgetRegisters : KRExpr_BaseModule -> KRExpr_list_RegInitT
  | KRgetAllRegisters : KRExpr_Mod -> KRExpr_list_RegInitT
  | KRMakeModule_regs : KRExpr_list_ModuleElt -> KRExpr_list_RegInitT
  
with KRExpr_list_Rule: Type :=
  | KRVar_list_Rule : list (Attribute (Action Void)) -> KRExpr_list_Rule
  | KRNil_list_Rule : KRExpr_list_Rule
  | KRCons_list_Rule : KRExpr_Rule -> KRExpr_list_Rule -> KRExpr_list_Rule
  | KRApp_list_Rule : KRExpr_list_Rule -> KRExpr_list_Rule -> KRExpr_list_Rule
  | KRgetRules : KRExpr_BaseModule -> KRExpr_list_Rule
  | KRgetAllRules : KRExpr_Mod -> KRExpr_list_Rule
  | KRMakeModule_rules : KRExpr_list_ModuleElt -> KRExpr_list_Rule

with KRExpr_list_DefMethT: Type :=
  | KRVar_list_DefMethT : list DefMethT -> KRExpr_list_DefMethT
  | KRNil_list_DefMethT : KRExpr_list_DefMethT
  | KRCons_list_DefMethT : KRExpr_DefMethT -> KRExpr_list_DefMethT -> KRExpr_list_DefMethT
  | KRApp_list_DefMethT : KRExpr_list_DefMethT -> KRExpr_list_DefMethT -> KRExpr_list_DefMethT
  | KRgetMethods : KRExpr_BaseModule -> KRExpr_list_DefMethT
  | KRgetAllMethods : KRExpr_Mod -> KRExpr_list_DefMethT
  | KRMakeModule_meths : KRExpr_list_ModuleElt -> KRExpr_list_DefMethT

with KRExpr_list_ModuleElt: Type :=
  | KRVar_list_ModuleElt : list ModuleElt -> KRExpr_list_ModuleElt
  | KRNil_list_ModuleElt : KRExpr_list_ModuleElt
  | KRCons_list_ModuleElt : KRExpr_ModuleElt -> KRExpr_list_ModuleElt -> KRExpr_list_ModuleElt
  | KRApp_list_ModuleElt : KRExpr_list_ModuleElt -> KRExpr_list_ModuleElt -> KRExpr_list_ModuleElt
  | KRRegisters : KRExpr_list_RegInitT -> KRExpr_list_ModuleElt
  | KRRules : KRExpr_list_Rule -> KRExpr_list_ModuleElt
  | KRMethods : KRExpr_list_DefMethT -> KRExpr_list_ModuleElt

with KRExpr_list_list_ModuleElt: Type :=
  | KRVar_list_list_ModuleElt : list (list ModuleElt) -> KRExpr_list_list_ModuleElt
  | KRNil_list_list_ModuleElt : KRExpr_list_list_ModuleElt
  | KRCons_list_list_ModuleElt : KRExpr_list_ModuleElt -> KRExpr_list_list_ModuleElt -> KRExpr_list_list_ModuleElt
  | KRApp_list_list_ModuleElt : KRExpr_list_list_ModuleElt -> KRExpr_list_list_ModuleElt -> KRExpr_list_list_ModuleElt

with KRExpr_BaseModule: Type :=
  | KRVar_BaseModule : BaseModule -> KRExpr_BaseModule
  | KRMakeModule : KRExpr_list_ModuleElt -> KRExpr_BaseModule
  | KRBaseMod : KRExpr_list_RegInitT -> KRExpr_list_Rule -> KRExpr_list_DefMethT -> KRExpr_BaseModule

with KRExpr_Mod: Type :=
  | KRVar_Mod : Mod -> KRExpr_Mod
  | KRBase : KRExpr_BaseModule -> KRExpr_Mod.

Fixpoint KRExprDenote_RegInitT (e:KRExpr_RegInitT) : RegInitT :=
  match e with
  | KRVar_RegInitT v => v
  end

with KRExprDenote_Rule (e:KRExpr_Rule) : Attribute (Action Void) :=
  match e with
  | KRVar_Rule v => v
  end

with KRExprDenote_DefMethT (e:KRExpr_DefMethT) : DefMethT :=
  match e with
  | KRVar_DefMethT v => v
  end
    
with KRExprDenote_ModuleElt (e:KRExpr_ModuleElt) : ModuleElt :=
  match e with
  | KRVar_ModuleElt v => v
  | KRMERegister r => MERegister (KRExprDenote_RegInitT r)
  | KRMERule r => MERule (KRExprDenote_Rule r)
  | KRMEMeth m => MEMeth (KRExprDenote_DefMethT m)
  end

with KRExprDenote_list_RegInitT (e:KRExpr_list_RegInitT) : list RegInitT :=
  match e with
  | KRVar_list_RegInitT v => v
  | KRNil_list_RegInitT => nil
  | KRCons_list_RegInitT f r => cons (KRExprDenote_RegInitT f) (KRExprDenote_list_RegInitT r)
  | KRApp_list_RegInitT f r => app (KRExprDenote_list_RegInitT f) (KRExprDenote_list_RegInitT r)
  | KRgetRegisters m => getRegisters (KRExprDenote_BaseModule m)
  | KRgetAllRegisters m => getAllRegisters (KRExprDenote_Mod m)
  | KRMakeModule_regs r => makeModule_regs (KRExprDenote_list_ModuleElt r)
  end
    
with KRExprDenote_list_Rule (e:KRExpr_list_Rule) : list (Attribute (Action Void)) :=
  match e with
  | KRVar_list_Rule v => v
  | KRNil_list_Rule => nil
  | KRCons_list_Rule f r => cons (KRExprDenote_Rule f) (KRExprDenote_list_Rule r)
  | KRApp_list_Rule f r => app (KRExprDenote_list_Rule f) (KRExprDenote_list_Rule r)
  | KRgetRules m => getRules (KRExprDenote_BaseModule m)
  | KRgetAllRules m => getAllRules (KRExprDenote_Mod m)
  | KRMakeModule_rules r => makeModule_rules (KRExprDenote_list_ModuleElt r)
  end
    
with KRExprDenote_list_DefMethT (e:KRExpr_list_DefMethT) : list DefMethT :=
  match e with
  | KRVar_list_DefMethT v => v
  | KRNil_list_DefMethT => nil
  | KRCons_list_DefMethT f r => cons (KRExprDenote_DefMethT f) (KRExprDenote_list_DefMethT r)
  | KRApp_list_DefMethT f r => app (KRExprDenote_list_DefMethT f) (KRExprDenote_list_DefMethT r)
  | KRgetMethods m => getMethods (KRExprDenote_BaseModule m)
  | KRgetAllMethods m => getAllMethods (KRExprDenote_Mod m)
  | KRMakeModule_meths r => makeModule_meths (KRExprDenote_list_ModuleElt r)
  end

with KRExprDenote_list_ModuleElt (e:KRExpr_list_ModuleElt) : list ModuleElt :=
  match e with
  | KRVar_list_ModuleElt v => v
  | KRNil_list_ModuleElt => nil
  | KRCons_list_ModuleElt f r => cons (KRExprDenote_ModuleElt f) (KRExprDenote_list_ModuleElt r)
  | KRApp_list_ModuleElt f r => app (KRExprDenote_list_ModuleElt f) (KRExprDenote_list_ModuleElt r)
  | KRRegisters r => Registers (KRExprDenote_list_RegInitT r)
  | KRRules r => Rules (KRExprDenote_list_Rule r)
  | KRMethods m => Methods (KRExprDenote_list_DefMethT m)
  end

with KRExprDenote_BaseModule (e:KRExpr_BaseModule) : BaseModule :=
  match e with
  | KRVar_BaseModule v => v
  | KRMakeModule e => makeModule (KRExprDenote_list_ModuleElt e)
  | KRBaseMod regs rules meths => BaseMod (KRExprDenote_list_RegInitT regs) (KRExprDenote_list_Rule rules) (KRExprDenote_list_DefMethT meths)
  end

with KRExprDenote_Mod (e:KRExpr_Mod) : Mod :=
  match e with
  | KRVar_Mod v => v
  | KRBase b => Base (KRExprDenote_BaseModule b)
  end.

Inductive KRElem: Type :=
| KRElemRegInitT : KRElem
| KRElemRule : KRElem
| KRElemDefMethT : KRElem
| KRElemModuleElt: KRElem
| KRElemMod : KRElem
| KRElemBaseModule : KRElem.

Inductive KRType : Type :=
  | KRTypeElem: KRElem -> KRType
  | KRTypeList: KRType -> KRType.

Ltac KRExprReify e t :=
  match e with
  | nil => match t with
           | KRTypeList (KRTypeElem KRElemRegInitT) => constr:(@KRNil_list_RegInitT)
           | KRTypeList (KRTypeElem KRElemRule) => constr:(@KRNil_list_Rule)
           | KRTypeList (KRTypeElem KRElemDefMethT) => constr:(@KRNil_list_DefMethT)
           | KRTypeList (KRTypeElem KRElemModuleElt) => constr:(@KRNil_list_ModuleElt)
           | KRTypeList (KRTypeList (KRTypeElem KRElemModuleElt)) => constr:(@KRNil_list_list_ModuleElt)
           end
  | cons ?F ?R => match t with
                  | KRTypeList (KRTypeElem KRElemRegInitT)  => let fr :=ltac:(KRExprReify F (KRTypeElem KRElemRegInitT)) in
                                                               let re:=ltac:(KRExprReify R (KRTypeList (KRTypeElem KRElemRegInitT))) in
                                                               constr:(KRCons_list_RegInitT fr re)
                  | KRTypeList (KRTypeElem KRElemRule)  => let fr :=ltac:(KRExprReify F (KRTypeElem KRElemRule)) in
                                                               let re:=ltac:(KRExprReify R (KRTypeList (KRTypeElem KRElemRule))) in
                                                               constr:(KRCons_list_Rule fr re)
                  | KRTypeList (KRTypeElem KRElemDefMethT)  => let fr :=ltac:(KRExprReify F (KRTypeElem KRElemDefMethT)) in
                                                               let re:=ltac:(KRExprReify R (KRTypeList (KRTypeElem KRElemDefMethT))) in
                                                               constr:(KRCons_list_DefMethT fr re)
                  | KRTypeList (KRTypeElem KRElemModuleElt)  => let fr :=ltac:(KRExprReify F (KRTypeElem KRElemModuleElt)) in
                                                               let re:=ltac:(KRExprReify R (KRTypeList (KRTypeElem KRElemModuleElt))) in
                                                               constr:(KRCons_list_ModuleElt fr re)
                  | KRTypeList (KRTypeList (KRTypeElem KRElemModuleElt))  => let fr :=ltac:(KRExprReify F (KRTypeList (KRTypeElem KRElemModuleElt))) in
                                                               let re:=ltac:(KRExprReify R (KRTypeList (KRTypeList (KRTypeElem KRElemModuleElt)))) in
                                                               constr:(KRCons_list_list_ModuleElt fr re)
                  end
  | app ?F ?R => let x1 := ltac:(KRExprReify F t) in
                 let x2 := ltac:(KRExprReify R t) in
                 match t with
                 | KRTypeList (KRTypeElem KRElemRegInitT) => constr:(KRApp_list_RegInitT x1 x2)
                 | KRTypeList (KRTypeElem KRElemRule) => constr:(KRApp_list_Rule x1 x2)
                 | KRTypeList (KRTypeElem KRElemDefMethT) => constr:(KRApp_list_DefMethT x1 x2)
                 | KRTypeList (KRTypeElem KRElemModuleElt) => constr:(KRApp_list_ModuleElt x1 x2)
                 | KRTypeList (KRTypeList (KRTypeElem KRElemModuleElt)) => constr:(KRApp_list_list_ModuleElt x1 x2)
                 end
  | MERegister ?E => let x := ltac:(KRExprReify E (KRTypeElem KRElemRegInitT)) in
                         constr:(KRMERegister x)
  | Registers ?E => let x := ltac:(KRExprReify E (KRTypeList (KRTypeElem KRElemRegInitT))) in
                       constr:(KRRegisters x)
  | getRegisters ?E => let x := ltac:(KRExprReify E (KRTypeList (KRTypeElem KRElemBaseModule))) in
                       constr:(KRgetRegisters x)
  | getAllRegisters ?E => let x := ltac:(KRExprReify E (KRTypeElem KRElemMod)) in
                          constr:(KRgetAllRegisters x)
  | getAllRegisters ?E => let x := ltac:(KRExprReify E (KRTypeElem KRElemMod)) in
                          constr:(KRgetAllRegisters (@KRBase x))
  | getAllRegisters ?E => let x := ltac:(KRExprReify E (KRTypeElem KRElemBaseModule)) in
                          constr:(KRgetAllRegisters x)
  | getAllRegisters ?E => let x := ltac:(KRExprReify E (KRTypeElem KRElemBaseModule)) in
                          constr:(KRgetAllRegisters (@KRBase x))
  | MERule ?E => let  x := ltac:(KRExprReify E (KRTypeElem KRElemRule)) in
                     constr:(KRMERule x)
  | Rules ?E => let x := ltac:(KRExprReify E (KRTypeList (KRTypeElem KRElemRule))) in
                         constr:(KRRules x)
  | getRules ?E => let x := ltac:(KRExprReify E (KRTypeElem KRElemBaseModule)) in
                   constr:(KRgetRules x)
  | getAllRules ?E => let x := ltac:(KRExprReify E (KRTypeElem KRElemMod)) in
                      constr:(KRgetAllRules x)
  | MEMeth ?E => let x := ltac:(KRExprReify E (KRTypeElem KRElemDefMethT)) in
                     constr:(KRMEMeth x)
  | Methods ?E => let x := ltac:(KRExprReify E (KRTypeList (KRTypeElem KRElemDefMethT))) in
                           constr:(KRMethods x)
  | getMethods ?E => let x := ltac:(KRExprReify E (KRTypeElem KRElemBaseModule)) in
                     constr:(KRgetMethods x)
  | getAllMethods ?E => let x := ltac:(KRExprReify E (KRTypeElem KRElemMod)) in
                        constr:(KRgetAllMethods x)
  | makeModule_regs ?X => let x := ltac:(KRExprReify X (KRTypeList (KRTypeElem KRElemModuleElt))) in
                              constr:(KRMakeModule_regs x)
  | makeModule_rules ?E => let x := ltac:(KRExprReify E (KRTypeList (KRTypeElem KRElemModuleElt))) in
                               constr:(KRMakeModule_rules x)
  | makeModule_meths ?E => let x := ltac:(KRExprReify E (KRTypeList (KRTypeElem KRElemModuleElt))) in 
                           constr:(KRMakeModule_meths x)
  | makeModule ?E => let x := ltac:(KRExprReify E (KRTypeList (KRTypeElem KRElemModuleElt))) in 
                     constr:(KRMakeModule x)
  | BaseMod ?R ?U ?M => let regs := ltac:(KRExprReify R (KRTypeList (KRTypeElem KRElemRegInitT))) in
                        let rules := ltac:(KRExprReify U (KRTypeList (KRTypeElem KRElemRule))) in
                        let meths := ltac:(KRExprReify M (KRTypeList (KRTypeElem KRElemDefMethT))) in
                        constr:(KRBaseMod regs rules meths)
  | Base ?B => let m := ltac:(KRExprReify B (KRTypeElem KRElemBaseModule)) in
               constr:(KRBase m)
  | ?X => match t with
          | (KRTypeElem KRElemRegInitT) => constr:(KRVar_RegInitT X)
          | (KRTypeElem KRElemRule) => constr:(KRVar_Rule X)
          | (KRTypeElem KRElemDefMethT) => constr:(KRVar_RegInitT X)
          | (KRTypeElem KRElemModuleElt) => constr:(KRVar_ModuleElt X)
          | (KRTypeList (KRTypeElem KRElemRegInitT)) => constr:(KRVar_list_RegInitT X)
          | (KRTypeList (KRTypeElem KRElemRule)) => constr:(KRVar_list_Rule X)
          | (KRTypeList (KRTypeElem KRElemDefMethT)) => constr:(KRVar_list_RegInitT X)
          | (KRTypeList (KRTypeElem KRElemModuleElt)) => constr:(KRVar_list_ModuleElt X)
          | (KRTypeList (KRTypeList (KRTypeElem KRElemModuleElt))) => constr:(KRVar_list_list_ModuleElt X)
          | (KRTypeElem KRElemBaseModule) => constr:(KRVar_BaseModule X)
          | (KRTypeElem KRElemMod) => constr:(KRVar_Mod X)
          end
  end.

Axiom cheat: forall x, x.

Definition KRSimplifyTop_RegInitT (e : KRExpr_RegInitT) := e.

Definition KRSimplifyTop_Rule (e : KRExpr_Rule) := e.

Definition KRSimplifyTop_DefMethT (e : KRExpr_DefMethT) := e.

Definition KRSimplifyTop_ModuleElt (e : KRExpr_ModuleElt) := e.

Definition KRSimplifyTop_list_RegInitT (e : KRExpr_list_RegInitT) : KRExpr_list_RegInitT :=
  match e with
  | KRApp_list_RegInitT f c => match f with
                    | KRCons_list_RegInitT ff rr => KRCons_list_RegInitT ff (KRApp_list_RegInitT rr c)
                    | KRNil_list_RegInitT => c
                    | x => match c with
                           | KRNil_list_RegInitT => c
                           | y => KRApp_list_RegInitT f c
                           end
                    end
   | KRMakeModule_regs x =>
     match x with
     | KRApp_list_ModuleElt a b =>
       KRApp_list_RegInitT (KRMakeModule_regs a) (KRMakeModule_regs b)
     | KRCons_list_ModuleElt aa b =>
       match aa with
       | KRMERule a => KRMakeModule_regs b
       | KRMEMeth a => KRMakeModule_regs b
       | KRMERegister a => KRCons_list_RegInitT a (KRMakeModule_regs b)
       | _ => KRMakeModule_regs x
       end
     | KRNil_list_ModuleElt => KRNil_list_RegInitT
     | _ => KRMakeModule_regs x
     end
   | e => e
   end.

Definition KRSimplifyTop_list_Rule (e : KRExpr_list_Rule) : KRExpr_list_Rule :=
  match e with
  | KRApp_list_Rule f c => match f with
                    | KRCons_list_Rule ff rr => KRCons_list_Rule ff (KRApp_list_Rule rr c)
                    | KRNil_list_Rule => c
                    | x => match c with
                           | KRNil_list_Rule => c
                           | y => KRApp_list_Rule f c
                           end
                    end
   | KRMakeModule_rules x =>
     match x with
     | KRApp_list_ModuleElt a b =>
       KRApp_list_Rule (KRMakeModule_rules a) (KRMakeModule_rules b)
     | KRCons_list_ModuleElt aa b =>
       match aa with
       | KRMERegister a => KRMakeModule_rules b
       | KRMEMeth a => KRMakeModule_rules b
       | KRMERule a => KRCons_list_Rule a (KRMakeModule_rules b)
       | _ => KRMakeModule_rules x
       end
     | KRNil_list_ModuleElt => KRNil_list_Rule
     | _ => KRMakeModule_rules x
     end
   | e => e
   end.

Definition KRSimplifyTop_list_DefMethT (e : KRExpr_list_DefMethT) : KRExpr_list_DefMethT :=
  match e with
  | KRApp_list_DefMethT f c => match f with
                               | KRCons_list_DefMethT ff rr => KRCons_list_DefMethT ff (KRApp_list_DefMethT rr c)
                               | KRNil_list_DefMethT => c
                               | x => match c with
                                      | KRNil_list_DefMethT => c
                                      | y => KRApp_list_DefMethT f c
                                      end
                               end
   | KRMakeModule_meths x =>
     match x with
     | KRApp_list_ModuleElt a b =>
       KRApp_list_DefMethT (KRMakeModule_meths a) (KRMakeModule_meths b)
     | KRCons_list_ModuleElt aa b =>
       match aa with
       | KRMERegister a => KRMakeModule_meths b
       | KRMERule a => KRMakeModule_meths b
       | KRMEMeth a => KRCons_list_DefMethT a (KRMakeModule_meths b)
       | _ => KRMakeModule_meths x
       end
     | KRNil_list_ModuleElt => KRNil_list_DefMethT
     | _ => KRMakeModule_meths x
     end
   | e => e
   end.

Definition KRSimplifyTop_list_ModuleElt (e : KRExpr_list_ModuleElt) : KRExpr_list_ModuleElt :=
  match e with
  | KRApp_list_ModuleElt f c => match f with
                                | KRCons_list_ModuleElt ff rr => KRCons_list_ModuleElt ff (KRApp_list_ModuleElt rr c)
                                | KRNil_list_ModuleElt => c
                                | x => match c with
                                       | KRNil_list_ModuleElt => c
                                       | y => KRApp_list_ModuleElt f c
                                       end
                                end
   | e => e
   end.

Definition KRSimplifyTop_list_list_ModuleElt (e : KRExpr_list_list_ModuleElt) : KRExpr_list_list_ModuleElt :=
  match e with
  | KRApp_list_list_ModuleElt f c => match f with
                                     | KRCons_list_list_ModuleElt ff rr => KRCons_list_list_ModuleElt ff (KRApp_list_list_ModuleElt rr c)
                                     | KRNil_list_list_ModuleElt => c
                                     | x => match c with
                                            | KRNil_list_list_ModuleElt => c
                                            | y => KRApp_list_list_ModuleElt f c
                                            end
                                     end
   | e => e
   end.

Definition KRSimplifyTop_BaseModule (e : KRExpr_BaseModule) := e.

Definition KRSimplifyTop_Mod (e : KRExpr_Mod) := e.

(*Definition KRSimplifyTop (e : KRExpr) : KRExpr :=
  match e with
  | KRApp tp f c => match f with
                    | KRCons ttp ff rr => KRCons tp ff (KRApp tp rr c)
                    | KRNil ttp => c
                    | x => match c with
                           | KRNil ttp => c
                           | y => KRApp tp f c
                           end
                    end
  | KRRegisters x => match x with
                     | KRApp tp f r => KRApp (KRTypeElem KRElemModuleElt) (KRRegisters f) (KRRegisters r)
                     | KRCons tp f r => KRCons (KRTypeElem KRElemModuleElt) (KRMERegister f) (KRRegisters r)
                     | KRNil tp => KRNil (KRTypeElem KRElemModuleElt)
                     | _ => KRRegisters x
                     end
  | KRRules x => match x with
                 | KRApp tp f r => KRApp (KRTypeElem KRElemModuleElt) (KRRules f) (KRRules r)
                 | KRCons tp f r => KRCons (KRTypeElem KRElemModuleElt) (KRMERule f) (KRRules r)
                 | KRNil tp => KRNil (KRTypeElem KRElemModuleElt)
                 | _ => KRRules x
                 end
  | KRMethods x => match x with
                   | KRApp tp f r => KRApp (KRTypeElem KRElemModuleElt) (KRMethods f) (KRMethods r)
                   | KRCons tp f r => KRCons (KRTypeElem KRElemModuleElt) (KRMEMeth f) (KRMethods r)
                   | KRNil tp => KRNil (KRTypeElem KRElemModuleElt)
                   | _ => KRMethods x
                   end
   (*| KRgetRegisters x => _
   | KRgetAllRegisters x => _
   | KRgetRules x => _
   | KRgetAllRules x => _
   | KRgetMethods x => _
   | KRgetAllMethods x =>*)
   | KRMakeModule_regs x =>
     match x with
     | KRApp (KRTypeElem KRElemModuleElt) a b =>
       KRApp (KRTypeElem KRElemRegInitT) (KRMakeModule_regs a) (KRMakeModule_regs b)
     | KRCons (KRTypeElem KRElemModuleElt) aa b =>
       match aa with
       | KRMERule a => KRMakeModule_regs b
       | KRMEMeth a => KRMakeModule_regs b
       | KRMERegister a => KRCons (KRTypeElem KRElemRegInitT) a (KRMakeModule_regs b)
       | _ => KRMakeModule_regs x
       end
     | KRNil (KRTypeElem KRElemModuleElt) => KRNil (KRTypeElem KRElemRegInitT)
     | _ => KRMakeModule_regs x
     end
   | KRMakeModule_rules x =>
      match x with
     | KRApp (KRTypeElem KRElemModuleElt) a b =>
       KRApp (KRTypeElem KRElemRule) (KRMakeModule_rules a) (KRMakeModule_rules b)
     | KRCons (KRTypeElem KRElemModuleElt) aa  b =>
       match aa with
       | KRMERegister a => KRMakeModule_rules b
       | KRMEMeth a => KRMakeModule_rules b
       | KRMERule a => KRCons (KRTypeElem KRElemRule) a (KRMakeModule_rules b)
       | _ => KRMakeModule_rules x
       end
     | KRNil (KRTypeElem KRElemModuleElt) => KRNil (KRTypeElem KRElemRule)
     | qr => KRMakeModule_rules x
     end
   | KRMakeModule_meths x =>
     match x with
     | KRApp (KRTypeElem KRElemModuleElt) a b =>
       KRApp (KRTypeElem KRElemDefMethT) (KRMakeModule_meths a) (KRMakeModule_meths b)
     | KRCons (KRTypeElem KRElemModuleElt) aa b =>
       match aa with
       | KRMERule a => KRMakeModule_meths b
       | KRMERegister a => KRMakeModule_meths b
       | KRMEMeth a => @KRCons (KRTypeElem KRElemDefMethT) a (KRMakeModule_meths b)
       | _ => KRMakeModule_meths x
       end
     | KRNil (KRTypeElem KRElemModuleElt) => KRNil (KRTypeElem KRElemDefMethT)
     | qm => KRMakeModule_meths x
     end
   | e => e
   end.*)

Fixpoint KRSimplify_RegInitT (e : KRExpr_RegInitT) : KRExpr_RegInitT := KRSimplifyTop_RegInitT e

with KRSimplify_Rule (e :KRExpr_Rule) : KRExpr_Rule := KRSimplifyTop_Rule e

with KRSimplify_DefMethT (e :KRExpr_DefMethT) : KRExpr_DefMethT := KRSimplifyTop_DefMethT e

with KRSimplify_ModuleElt (e :KRExpr_ModuleElt) : KRExpr_ModuleElt :=
     KRSimplifyTop_ModuleElt (match e with
                              | KRMERegister r => KRMERegister (KRSimplify_RegInitT r)
                              | KRMERule r => KRMERule (KRSimplify_Rule r)
                              | KRMEMeth m => KRMEMeth (KRSimplify_DefMethT m)
                              | e => e
                              end)
                             
with KRSimplify_list_RegInitT (e: KRExpr_list_RegInitT) : KRExpr_list_RegInitT :=
       KRSimplifyTop_list_RegInitT (match e with
                                    | KRCons_list_RegInitT f r =>
                                      KRCons_list_RegInitT (KRSimplify_RegInitT f) (KRSimplify_list_RegInitT r)
                                    | KRApp_list_RegInitT f r =>
                                      KRApp_list_RegInitT (KRSimplify_list_RegInitT f) (KRSimplify_list_RegInitT r)
                                    | KRgetRegisters m => KRgetRegisters (KRSimplify_BaseModule m)
                                    | KRgetAllRegisters m => KRgetAllRegisters (KRSimplify_Mod m)
                                    | KRMakeModule_regs r => KRMakeModule_regs (KRSimplify_list_ModuleElt r)
                                    | e => e
                                   end)
  
with KRSimplify_list_Rule (e: KRExpr_list_Rule) : KRExpr_list_Rule :=
       KRSimplifyTop_list_Rule (match e with
                                | KRCons_list_Rule f r =>
                                  KRCons_list_Rule (KRSimplify_Rule f) (KRSimplify_list_Rule r)
                                | KRApp_list_Rule f r =>
                                  KRApp_list_Rule (KRSimplify_list_Rule f) (KRSimplify_list_Rule r)
                                | KRgetRules m => KRgetRules (KRSimplify_BaseModule m)
                                | KRgetAllRules m => KRgetAllRules (KRSimplify_Mod m)
                                | KRMakeModule_rules r => KRMakeModule_rules (KRSimplify_list_ModuleElt r)
                                | e => e
                               end)

with KRSimplify_list_DefMethT (e: KRExpr_list_DefMethT) : KRExpr_list_DefMethT :=
       KRSimplifyTop_list_DefMethT (match e with
                                    | KRCons_list_DefMethT f r =>
                                      KRCons_list_DefMethT (KRSimplify_DefMethT f) (KRSimplify_list_DefMethT r)
                                    | KRApp_list_DefMethT f r =>
                                      KRApp_list_DefMethT (KRSimplify_list_DefMethT f) (KRSimplify_list_DefMethT r)
                                    | KRgetMethods m => KRgetMethods (KRSimplify_BaseModule m)
                                    | KRgetAllMethods m => KRgetAllMethods (KRSimplify_Mod m)
                                    | KRMakeModule_meths r => KRMakeModule_meths (KRSimplify_list_ModuleElt r)
                                    | e => e
                                    end)

with KRSimplify_list_ModuleElt (e: KRExpr_list_ModuleElt) : KRExpr_list_ModuleElt :=
       KRSimplifyTop_list_ModuleElt (match e with
                                      | KRCons_list_ModuleElt f r =>
                                        KRCons_list_ModuleElt (KRSimplify_ModuleElt f) (KRSimplify_list_ModuleElt r)
                                      | KRApp_list_ModuleElt f r =>
                                        KRApp_list_ModuleElt (KRSimplify_list_ModuleElt f) (KRSimplify_list_ModuleElt r)
                                      | KRRegisters r => KRRegisters (KRSimplify_list_RegInitT r)
                                      | KRRules r => KRRules (KRSimplify_list_Rule r)
                                      | KRMethods m => KRMethods (KRSimplify_list_DefMethT m)
                                      | e => e
                                     end)

with KRSimplify_list_list_ModuleElt (e: KRExpr_list_list_ModuleElt) : KRExpr_list_list_ModuleElt :=
       KRSimplifyTop_list_list_ModuleElt (match e with
                                      | KRCons_list_list_ModuleElt f r =>
                                        KRCons_list_list_ModuleElt (KRSimplify_list_ModuleElt f) (KRSimplify_list_list_ModuleElt r)
                                      | KRApp_list_list_ModuleElt f r =>
                                        KRApp_list_list_ModuleElt (KRSimplify_list_list_ModuleElt f) (KRSimplify_list_list_ModuleElt r)
                                      | e => e
                                     end)

with KRSimplify_BaseModule (e : KRExpr_BaseModule) : KRExpr_BaseModule :=
       KRSimplifyTop_BaseModule
         (match e with
          | KRMakeModule e => KRMakeModule (KRSimplify_list_ModuleElt e)
          | KRBaseMod regs rules meths => KRBaseMod (KRSimplify_list_RegInitT regs) (KRSimplify_list_Rule rules) (KRSimplify_list_DefMethT meths)
          | e => e
          end)

with KRSimplify_Mod (e : KRExpr_Mod) : KRExpr_Mod :=
       KRSimplifyTop_Mod
         (match e with
          | KRBase b => KRBase (KRSimplify_BaseModule b)
          | e => e
          end).

(*Fixpoint KRSimplify e : KRExpr :=
  KRSimplifyTop (match e with
  | KRNil tp => KRNil tp
  | KRVar tp val => KRVar tp val
  | KRCons tp f r => KRCons tp (KRSimplify f) (KRSimplify r)
  | KRApp tp f r => KRApp tp (KRSimplify f) (KRSimplify r)
  | KRMERegister r => KRMERegister (KRSimplify r)
  | KRRegisters r => KRRegisters (KRSimplify r)
  | KRRules r => KRRules (KRSimplify r)
  | KRMethods r => KRMethods (KRSimplify r)
  | KRMERule r => KRMERule (KRSimplify r)
  | KRMEMeth r => KRMEMeth (KRSimplify r)
  | KRgetRegisters r => KRgetRegisters (KRSimplify r)
  | KRgetAllRegisters r => KRgetAllRegisters (KRSimplify r)
  | KRgetRules r => KRgetRules (KRSimplify r)
  | KRgetAllRules r => KRgetAllRules (KRSimplify r)
  | KRgetMethods r => KRgetMethods (KRSimplify r)
  | KRgetAllMethods r => KRgetAllMethods (KRSimplify r)
  | KRMakeModule_regs r => KRMakeModule_regs (KRSimplify r)
  | KRMakeModule_rules r => KRMakeModule_rules (KRSimplify r)
  | KRMakeModule_meths m => KRMakeModule_meths (KRSimplify m)
  | KRBaseMod re ru me => KRBaseMod (KRSimplify re) (KRSimplify ru) (KRSimplify me)
  | KRMakeModule l => KRMakeModule (KRSimplify l)
  | KRBase m => KRBase (KRSimplify m)
  end).*)

Theorem KRSimplifyTopSound_RegInitT: forall e,
    KRExprDenote_RegInitT e = KRExprDenote_RegInitT (KRSimplifyTop_RegInitT e).
Proof.
  intros.
  reflexivity.
Qed.

Theorem KRSimplifyTopSound_Rule: forall e,
    KRExprDenote_Rule e = KRExprDenote_Rule (KRSimplifyTop_Rule e).
Proof.
  intros.
  reflexivity.
Qed.

Theorem KRSimplifyTopSound_DefMethT: forall e,
    KRExprDenote_DefMethT e = KRExprDenote_DefMethT (KRSimplifyTop_DefMethT e).
Proof.
  intros.
  reflexivity.
Qed.

Theorem KRSimplifyTopSound_ModuleElt: forall e,
    KRExprDenote_ModuleElt e = KRExprDenote_ModuleElt (KRSimplifyTop_ModuleElt e).
Proof.
  intros.
  reflexivity.
Qed.

(*  intros.
  inversion H;subst;clear H.
  induction e.
  - cbv [KRSimplifyTop KRSimplify].
    reflexivity.
  - cbv [KRSimplifyTop KRSimplify].
    reflexivity.
  - cbv [KRSimplifyTop KRSimplify].
    rewrite
Qed.*)

(*Theorem KRSimplifyCons:
  forall tp f r, KRSimplify (KRCons tp f r)=KRSimplifyTop (KRCons tp (KRSimplify f) (KRSimplify r)).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Hint Rewrite KRSimplifyCons : KRSimplify_simplify.

Theorem KRSimplifyApp:
  forall tp f r, KRSimplify (KRApp tp f r)=KRSimplifyTop (KRApp tp (KRSimplify f) (KRSimplify r)).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Hint Rewrite KRSimplifyApp : KRSimplify_simplify.

Theorem KRSimplifyMERegister:
  forall r, KRSimplify (KRMERegister r)=KRSimplifyTop (KRMERegister (KRSimplify r)).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Hint Rewrite KRSimplifyMERegister : KRSimplify_simplify.

Theorem KRSimplifyRegisters:
  forall r, KRSimplify (KRRegisters r)=KRSimplifyTop (KRRegisters (KRSimplify r)).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Hint Rewrite KRSimplifyRegisters : KRSimplify_simplify.

Theorem KRSimplifyRules:
  forall r, KRSimplify (KRRules r)=KRSimplifyTop (KRRules (KRSimplify r)).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Hint Rewrite KRSimplifyRules : KRSimplify_simplify.

Theorem KRSimplifyMethods:
  forall r, KRSimplify (KRMethods r)=KRSimplifyTop (KRMethods (KRSimplify r)).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Hint Rewrite KRSimplifyMethods : KRSimplify_simplify.

Theorem KRSimplifyMERule:
  forall r, KRSimplify (KRMERule r)=KRSimplifyTop (KRMERule (KRSimplify r)).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Hint Rewrite KRSimplifyMERule : KRSimplify_simplify.

Theorem KRSimplifyMEMeth:
  forall r, KRSimplify (KRMEMeth r)=KRSimplifyTop (KRMEMeth (KRSimplify r)).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Hint Rewrite KRSimplifyMEMeth : KRSimplify_simplify.

Theorem KRSimplifygetRegisters:
  forall r, KRSimplify (KRgetRegisters r)=KRSimplifyTop (KRgetRegisters (KRSimplify r)).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Hint Rewrite KRSimplifygetRegisters : KRSimplify_simplify.

Theorem KRSimplifygetAllRegisters:
  forall r, KRSimplify (KRgetAllRegisters r)=KRSimplifyTop (KRgetAllRegisters (KRSimplify r)).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Hint Rewrite KRSimplifygetAllRegisters : KRSimplify_simplify.

Theorem KRSimplifygetRules:
  forall r, KRSimplify (KRgetRules r)=KRSimplifyTop (KRgetRules (KRSimplify r)).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Hint Rewrite KRSimplifygetRules : KRSimplify_simplify.

Theorem KRSimplifygetAllRules:
  forall r, KRSimplify (KRgetAllRules r)=KRSimplifyTop (KRgetAllRules (KRSimplify r)).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Hint Rewrite KRSimplifygetAllRules : KRSimplify_simplify.

Theorem KRSimplifygetMethods:
  forall r, KRSimplify (KRgetMethods r)=KRSimplifyTop (KRgetMethods (KRSimplify r)).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Hint Rewrite KRSimplifygetMethods : KRSimplify_simplify.

Theorem KRSimplifygetAllMethods:
  forall r, KRSimplify (KRgetAllMethods r)=KRSimplifyTop (KRgetAllMethods (KRSimplify r)).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Hint Rewrite KRSimplifygetAllMethods : KRSimplify_simplify.

Theorem KRSimplifyMakeModule_regs:
  forall r, KRSimplify (KRMakeModule_regs r)=KRSimplifyTop (KRMakeModule_regs (KRSimplify r)).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Hint Rewrite KRSimplifyMakeModule_regs : KRSimplify_simplify.

Theorem KRSimplifyMakeModule_rules:
  forall r, KRSimplify (KRMakeModule_rules r)=KRSimplifyTop (KRMakeModule_rules (KRSimplify r)).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Hint Rewrite KRSimplifyMakeModule_rules : KRSimplify_simplify.

Theorem KRSimplifyMakeModule_meths:
  forall r, KRSimplify (KRMakeModule_meths r)=KRSimplifyTop (KRMakeModule_meths (KRSimplify r)).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Hint Rewrite KRSimplifyMakeModule_meths : KRSimplify_simplify.

Theorem KRSimplifyMakeModule:
  forall r, KRSimplify (KRMakeModule r)=KRSimplifyTop (KRMakeModule (KRSimplify r)).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Hint Rewrite KRSimplifyMakeModule : KRSimplify_simplify.

Theorem KRSimplifyBase:
  forall r, KRSimplify (KRBase r)=KRSimplifyTop (KRBase (KRSimplify r)).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Hint Rewrite KRSimplifyBase : KRSimplify_simplify.


(*Theorem KRExprDenoteKRCons: forall k f r, KRExprDenote (KRCons k f r)=match (KRExprDenote f),(KRExprDenote r) with
                                                                                      | KRSome f',Some r' => Some (cons f' r')
                                                                                      | _,_ => None
                                                                                      end.*)
(*Proof.
  intros.
  remember (KRExprDenote' k f).
  destruct o.
  -  remember (KRExprDenote' (KRTypeList k) r).
     destruct o.
     + simpl.
       rewrite <- Heqo.
       rewrite <- Heqo0.
       erewrite beq_KRType_refl at 1.
       simpl.*)

Theorem KRSimplifySound: forall e, KRExprDenote e = KRExprDenote (KRSimplify e).
Proof.
  intros.
  induction e; try (autorewrite with KRSimplify_simplify; rewrite <- KRSimplifyTopSound; simpl [KRExprDenote]; repeat (rewrite <- IHe)).
Admitted.
 (* - reflexivity.
  - reflexivity.
  - rewrite KRSimplifyCons.
    rewrite <- KRSimplifyTopSound.
    destruct k.
    + destruct k; try (simpl; rewrite <- IHe1; rewrite <- IHe2; reflexivity).
    + destruct k.
      * destruct k; try (simpl; try (rewrite <- IHe1; rewrite <- IHe2); reflexivity).
      * simpl. rewrite <- IHe1. rewrite <- IHe2. reflexivity.
  - rewrite KRSimplifyApp.
    rewrite <- KRSimplifyTopSound.
    destruct k.
    + destruct k; try (simpl; rewrite <- IHe1; rewrite <- IHe2; reflexivity).
    + destruct k.
      * destruct k; try (simpl; try (rewrite <- IHe1; rewrite <- IHe2); reflexivity).
      * simpl. rewrite <- IHe1. rewrite <- IHe2. reflexivity.
  - simpl [KRSimplify].
    repeat (rewrite <- KRSimplifyTopSound).
    repeat (rewrite <- IHe). reflexivity.
  - rewrite KRSimplifyRegisters.
    rewrite <- KRSimplifyTopSound.
    simpl [KRExprDenote].
    repeat (rewrite <- IHe).
    reflexivity.
  - rewrite KRSimplifyRules.
    rewrite <- KRSimplifyTopSound.
    simpl [KRExprDenote].
    repeat (rewrite <- IHe).
    reflexivity.
  - rewrite KRSimplifyMethods.
    rewrite <- KRSimplifyTopSound.
    simpl [KRExprDenote].
    repeat (rewrite <- IHe).
    reflexivity.
  - rewrite KRSimplifyMERule.
    rewrite <- KRSimplifyTopSound.
    simpl [KRExprDenote].
    repeat (rewrite <- IHe).
    reflexivity.
  - rewrite KRSimplifyMEMeth.
    rewrite <- KRSimplifyTopSound.
    simpl [KRExprDenote].
    repeat (rewrite <- IHe).
    reflexivity.
  - rewrite KRSimplifygetRegisters.
    rewrite <- KRSimplifyTopSound.
    simpl [KRExprDenote].
    repeat (rewrite <- IHe).
    reflexivity.
  - rewrite KRSimplifygetAllRegisters.
    rewrite <- KRSimplifyTopSound.
    simpl [KRExprDenote].
    repeat (rewrite <- IHe).
    reflexivity.
  - rewrite KRSimplifygetRegisters.
    rewrite <- KRSimplifyTopSound.
    simpl [KRExprDenote].
    repeat (rewrite <- IHe).
    reflexivity.
  - rewrite KRSimplifygetAllRegisters.
    rewrite <- KRSimplifyTopSound.
    simpl [KRExprDenote].
    repeat (rewrite <- IHe).
    reflexivity.
  - rewrite KRSimplifygetRegisters.
    rewrite <- KRSimplifyTopSound.
    simpl [KRExprDenote].
    repeat (rewrite <- IHe).
    reflexivity.
  - rewrite KRSimplifygetAllRegisters.
    rewrite <- KRSimplifyTopSound.
    simpl [KRExprDenote].
    repeat (rewrite <- IHe).
    reflexivity.
  -
    
  - simpl [KRSimplify].
    repeat (rewrite <- KRSimplifyTopSound).
    repeat (rewrite <- IHe). reflexivity.
  - simpl [KRSimplify].
    repeat (rewrite <- KRSimplifyTopSound).
    repeat (rewrite <- IHe). reflexivity.
  - simpl [KRSimplify].
    repeat (rewrite <- KRSimplifyTopSound).
    repeat (rewrite <- IHe). reflexivity.
  - simpl [KRSimplify].
    repeat (rewrite <- KRSimplifyTopSound).
    repeat (rewrite <- IHe). reflexivity.
  - simpl [KRSimplify].
    repeat (rewrite <- KRSimplifyTopSound).
    repeat (rewrite <- IHe). reflexivity.
  - simpl [KRSimplify].
    repeat (rewrite <- KRSimplifyTopSound).
    repeat (rewrite <- IHe). reflexivity.
  - simpl [KRSimplify].
    repeat (rewrite <- KRSimplifyTopSound).
    repeat (rewrite <- IHe). reflexivity.
  - simpl [KRSimplify].
    repeat (rewrite <- KRSimplifyTopSound).
    repeat (rewrite <- IHe). reflexivity.
  - simpl [KRSimplify].
    repeat (rewrite <- KRSimplifyTopSound).
    repeat (rewrite <- IHe). reflexivity.
  - simpl [KRSimplify].
    repeat (rewrite <- KRSimplifyTopSound).
    repeat (rewrite <- IHe). reflexivity.
  - simpl [KRSimplify].
    repeat (rewrite <- KRSimplifyTopSound).
    repeat (rewrite <- IHe). reflexivity.
Admitted.*)

Theorem sum_elim: forall tp (x:tp) (y:tp), Some x=Some y -> x=y.
  intros.
  inversion H.
  subst.
  reflexivity.
Qed.

Goal forall (a:ModuleElt) (b:list ModuleElt) c, app (cons a b) c=cons a (app b c).
  intros.
  match goal with
  | |- ?A = ?B => let x := (ltac:(KRExprReify A (KRTypeList (KRTypeElem KRElemModuleElt)))) in
                  let H := fresh in
                  assert (KROption_Some (KRTypeList (KRTypeElem KRElemModuleElt)) A = (KRExprDenote (KRSimplify x))) as H ; [ rewrite <- KRSimplifySound;idtac | idtac ]
                      (*rewrite <- KRSimplifySound;[compute [KRExprDenote]; reflexivity |
                                                  simpl; reflexivity |
                                                  compute [KRExprDenote KRTypeDenote KRElemDenote KRExprType]; (*eapply ex_intro;reflexivity*) idtac] |
                                                  cbv [KRSimplify KRSimplifyTop KRExprDenote] in H]*)
  end.
  assert (KRExprDenote (KRApp (KRTypeElem KRElemModuleElt) (KRVar (KRTypeList (KRTypeElem KRElemModuleElt)) c) (KRVar (KRTypeList (KRTypeElem KRElemModuleElt)) b))=KROption_Some (KRTypeList (KRTypeElem KRElemModuleElt)) []).
  simpl.
  
Abort.

(*  destruct H.
  constructor H.
  rewrite H.
  cbv [KRExprDenote] in H.
  simpl [KRSimplify KRSimplifyTop] in H.
  simpl in H.
  match goal with

  end.


  
  compute in H.
  destruct H.*)

Ltac KRSimplifyTac e tp :=
       let x := (ltac:(KRExprReify e tp)) in
       let H := fresh in
                (assert (Some e = (KRExprDenote tp x)) as H;
                 [cbv [KRExprDenote KRExprDenote'];reflexivity | idtac];
                 repeat (rewrite KRSimplifySound in H;[cbv [KRSimplify KRSimplifyTop] in H |
                                                       simpl; reflexivity | compute [KRExprDenote KRExprDenote' KRTypeDenote KRElemDenote KRExprType]; eapply ex_intro; reflexivity]);
                cbv [KRExprDenote KRExprDenote'] in H;apply sum_elim in H;rewrite H;clear H).

(*Ltac KRPrintReify e :=
  let x := (ltac:(KRExprReify e t)) in
  let t := eval compute in (KRTypeDenote x) in
  let xx := (ltac:(KRExprReify e t)) in
      idtac t;idtac x.
 *)

Goal forall a b c d e, Registers ([a;b]++[c;d])=e.
  intros.
  match goal with
  | |- ?A = ?B => KRSimplifyTac A (KRTypeList (KRTypeElem KRElemModuleElt))
  end.
Abort.
Goal forall a b c d e, makeModule_regs [MERegister a;MERule b;MEMeth c;MERegister d]=e.
  intros.
  match goal with
  | |- ?A = ?B => 
      KRSimplifyTac A (KRTypeList (KRTypeElem KRElemRegInitT))
  end.
Abort.
Goal forall a b c d e, makeModule_rules [MERegister a;MERule b;MEMeth c;MERegister d]=e.
  intros.
  match goal with
  | |- ?A = ?B => 
      KRSimplifyTac A (KRTypeList (KRTypeElem KRElemRule))
  end.
Abort.
Goal forall a b c d e, makeModule_meths [MERegister a;MERule b;MEMeth c;MERegister d]=e.
  intros.
  match goal with
  | |- ?A = ?B => 
      KRSimplifyTac A (KRTypeList (KRTypeElem KRElemDefMethT))
  end.
Abort.
Goal forall e, makeModule_regs []=e.
  intros.
  match goal with
  | |- ?A = ?B => 
      KRSimplifyTac A (KRTypeList (KRTypeElem KRElemRegInitT))
  end.
Abort.*)
