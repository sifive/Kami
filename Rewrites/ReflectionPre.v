Require Import Kami.Notations.
Require Import Kami.Syntax.
Require Import List.
Require Import Kami.Notations_rewrites.
Require Import Program.Equality.

Inductive KRExpr_RegInitT: Type :=
  | KRVar_RegInitT : RegInitT -> KRExpr_RegInitT
  | KRPair_RegInitT : KRExpr_string -> KRExpr_RegInitValT -> KRExpr_RegInitT

with KRExpr_RegInitValT: Type :=
  | KRVar_RegInitValT: sigT RegInitValT -> KRExpr_RegInitValT

with KRExpr_Rule: Type :=
  | KRVar_Rule : Attribute (Action Void) -> KRExpr_Rule
  | KRPair_Rule: KRExpr_string -> KRExpr_ActionVoid -> KRExpr_Rule

with KRExpr_ActionVoid: Type :=
  | KRVar_ActionVoid: Action Void -> KRExpr_ActionVoid

with KRExpr_MethodT: Type :=
  | KRVar_MethodT: sigT MethodT -> KRExpr_MethodT

with KRExpr_DefMethT: Type :=
  | KRVar_DefMethT : DefMethT -> KRExpr_DefMethT
  | KRPair_DefMethT : KRExpr_string -> KRExpr_MethodT -> KRExpr_DefMethT

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
  | KRConcat_RegInitT : KRExpr_list_list_RegInitT -> KRExpr_list_RegInitT
  
with KRExpr_list_list_RegInitT: Type :=
  | KRVar_list_list_RegInitT : list (list RegInitT) -> KRExpr_list_list_RegInitT
  | KRNil_list_list_RegInitT : KRExpr_list_list_RegInitT
  | KRCons_list_list_RegInitT : KRExpr_list_RegInitT -> KRExpr_list_list_RegInitT -> KRExpr_list_list_RegInitT
  | KRApp_list_list_RegInitT : KRExpr_list_list_RegInitT -> KRExpr_list_list_RegInitT -> KRExpr_list_list_RegInitT
  | KRMap_list_Mod_list_list_RegInitT : KRExpr_Mod_list_RegInitT_Func -> KRExpr_list_Mod -> KRExpr_list_list_RegInitT
  | KRMap_list_RegFileBase_list_list_RegInitT : KRExpr_RegFileBase_list_RegInitT_Func -> KRExpr_list_RegFileBase -> KRExpr_list_list_RegInitT
  
with KRExpr_RegFileBase_list_RegInitT_Func :=
  | KRVar_RegFileBase_list_RegInitT_Func : (RegFileBase -> list (RegInitT)) -> KRExpr_RegFileBase_list_RegInitT_Func
  | KRgetRegFileRegistersFunc : KRExpr_RegFileBase_list_RegInitT_Func

with KRExpr_Mod_list_RegInitT_Func :=
  | KRVar_Mod_list_RegInitT_Func : (Mod -> list (RegInitT)) -> KRExpr_Mod_list_RegInitT_Func
  | KRgetAllRegistersFunc : KRExpr_Mod_list_RegInitT_Func

with KRExpr_list_Rule: Type :=
  | KRVar_list_Rule : list (Attribute (Action Void)) -> KRExpr_list_Rule
  | KRNil_list_Rule : KRExpr_list_Rule
  | KRCons_list_Rule : KRExpr_Rule -> KRExpr_list_Rule -> KRExpr_list_Rule
  | KRApp_list_Rule : KRExpr_list_Rule -> KRExpr_list_Rule -> KRExpr_list_Rule
  | KRgetRules : KRExpr_BaseModule -> KRExpr_list_Rule
  | KRgetAllRules : KRExpr_Mod -> KRExpr_list_Rule
  | KRMakeModule_rules : KRExpr_list_ModuleElt -> KRExpr_list_Rule
  | KRConcat_Rule : KRExpr_list_list_Rule -> KRExpr_list_Rule
 
with KRExpr_list_list_Rule: Type :=
  | KRVar_list_list_Rule : list (list (Attribute (Action Void))) -> KRExpr_list_list_Rule
  | KRNil_list_list_Rule : KRExpr_list_list_Rule
  | KRCons_list_list_Rule : KRExpr_list_Rule -> KRExpr_list_list_Rule -> KRExpr_list_list_Rule
  | KRApp_list_list_Rule : KRExpr_list_list_Rule -> KRExpr_list_list_Rule -> KRExpr_list_list_Rule
  | KRMap_list_Mod_list_list_Rule : KRExpr_Mod_list_Rule_Func -> KRExpr_list_Mod -> KRExpr_list_list_Rule
  
with KRExpr_Mod_list_Rule_Func :=
  | KRVar_Mod_list_Rule_Func : (Mod-> list (Attribute (Action Void))) -> KRExpr_Mod_list_Rule_Func
  | KRgetAllRulesFunc : KRExpr_Mod_list_Rule_Func

with KRExpr_list_DefMethT: Type :=
  | KRVar_list_DefMethT : list DefMethT -> KRExpr_list_DefMethT
  | KRNil_list_DefMethT : KRExpr_list_DefMethT
  | KRCons_list_DefMethT : KRExpr_DefMethT -> KRExpr_list_DefMethT -> KRExpr_list_DefMethT
  | KRApp_list_DefMethT : KRExpr_list_DefMethT -> KRExpr_list_DefMethT -> KRExpr_list_DefMethT
  | KRgetMethods : KRExpr_BaseModule -> KRExpr_list_DefMethT
  | KRgetAllMethods : KRExpr_Mod -> KRExpr_list_DefMethT
  | KRMakeModule_meths : KRExpr_list_ModuleElt -> KRExpr_list_DefMethT
  | KRConcat_DefMethT : KRExpr_list_list_DefMethT -> KRExpr_list_DefMethT

with KRExpr_list_list_DefMethT: Type :=
  | KRVar_list_list_DefMethT : list (list DefMethT) -> KRExpr_list_list_DefMethT
  | KRNil_list_list_DefMethT : KRExpr_list_list_DefMethT
  | KRCons_list_list_DefMethT : KRExpr_list_DefMethT -> KRExpr_list_list_DefMethT -> KRExpr_list_list_DefMethT
  | KRApp_list_list_DefMethT : KRExpr_list_list_DefMethT -> KRExpr_list_list_DefMethT -> KRExpr_list_list_DefMethT
  | KRMap_list_Mod_list_list_DefMethT : KRExpr_Mod_list_DefMethT_Func -> KRExpr_list_Mod -> KRExpr_list_list_DefMethT
  | KRMap_list_RegFileBase_list_list_DefMethT : KRExpr_RegFileBase_list_DefMethT_Func -> KRExpr_list_RegFileBase -> KRExpr_list_list_DefMethT
  
with KRExpr_Mod_list_DefMethT_Func :=
  | KRVar_Mod_list_DefMethT_Func : (Mod-> list (DefMethT)) -> KRExpr_Mod_list_DefMethT_Func
  | KRgetAllMethodsFunc : KRExpr_Mod_list_DefMethT_Func

with KRExpr_RegFileBase_list_DefMethT_Func :=
  | KRVar_RegFileBase_list_DefMethT_Func : (RegFileBase -> list (DefMethT)) -> KRExpr_RegFileBase_list_DefMethT_Func
  | KRgetRegFileMethodsFunc : KRExpr_RegFileBase_list_DefMethT_Func

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

with KRExpr_CallWithSign: Type :=
  | KRVar_CallWithSign: (string * (Kind * Kind)) -> KRExpr_CallWithSign

with KRExpr_list_CallWithSign: Type :=
  | KRVar_list_CallWithSign : list (string * (Kind * Kind)) -> KRExpr_list_CallWithSign
  | KRNil_list_CallWithSign : KRExpr_list_CallWithSign
  | KRCons_list_CallWithSign : KRExpr_CallWithSign -> KRExpr_list_CallWithSign -> KRExpr_list_CallWithSign
  | KRApp_list_CallWithSign : KRExpr_list_CallWithSign -> KRExpr_list_CallWithSign -> KRExpr_list_CallWithSign
  | KRConcat_CallWithSign : KRExpr_list_list_CallWithSign -> KRExpr_list_CallWithSign

with KRExpr_list_list_CallWithSign: Type :=
  | KRVar_list_list_CallWithSign : list (list (string * (Kind * Kind))) -> KRExpr_list_list_CallWithSign
  | KRNil_list_list_CallWithSign : KRExpr_list_list_CallWithSign
  | KRCons_list_list_CallWithSign : KRExpr_list_CallWithSign -> KRExpr_list_list_CallWithSign -> KRExpr_list_list_CallWithSign
  | KRApp_list_list_CallWithSign : KRExpr_list_list_CallWithSign -> KRExpr_list_list_CallWithSign -> KRExpr_list_list_CallWithSign
  (*| KRMap_list_Mod_list_list_CallWithSign : KRExpr_Mod_list_CallWithSign_Func -> KRExpr_list_Mod -> KRExpr_list_list_CallWithSign*)

with KRExpr_Mod_list_string_Func :=
  | KRVar_Mod_list_string_Func : (Mod-> list string) -> KRExpr_Mod_list_string_Func
  | KRgetCallsPerModFunc : KRExpr_Mod_list_string_Func

with KRExpr_BaseModule: Type :=
  | KRVar_BaseModule : BaseModule -> KRExpr_BaseModule
  | KRMakeModule : KRExpr_list_ModuleElt -> KRExpr_BaseModule
  | KRBaseMod : KRExpr_list_RegInitT -> KRExpr_list_Rule -> KRExpr_list_DefMethT -> KRExpr_BaseModule
  | KRBaseRegFile : KRExpr_RegFileBase -> KRExpr_BaseModule

with KRExpr_list_BaseModule: Type :=
  | KRVar_list_BaseModule : list BaseModule -> KRExpr_list_BaseModule
  | KRNil_list_BaseModule : KRExpr_list_BaseModule
  | KRCons_list_BaseModule : KRExpr_BaseModule -> KRExpr_list_BaseModule -> KRExpr_list_BaseModule
  | KRApp_list_BaseModule : KRExpr_list_BaseModule -> KRExpr_list_BaseModule -> KRExpr_list_BaseModule

with KRExpr_RegFileBase: Type :=
  | KRVar_RegFileBase: RegFileBase -> KRExpr_RegFileBase

with KRExpr_list_RegFileBase: Type :=
  | KRVar_list_RegFileBase : list RegFileBase -> KRExpr_list_RegFileBase
  | KRNil_list_RegFileBase : KRExpr_list_RegFileBase
  | KRCons_list_RegFileBase : KRExpr_RegFileBase -> KRExpr_list_RegFileBase -> KRExpr_list_RegFileBase
  | KRApp_list_RegFileBase : KRExpr_list_RegFileBase -> KRExpr_list_RegFileBase -> KRExpr_list_RegFileBase

with KRExpr_Mod: Type :=
  | KRVar_Mod : Mod -> KRExpr_Mod
  | KRBase : KRExpr_BaseModule -> KRExpr_Mod
  | KRConcatMod : KRExpr_Mod -> KRExpr_Mod -> KRExpr_Mod
  | KRFold_right_Mod : KRExpr_Mod_Mod_PairFunc -> KRExpr_Mod -> KRExpr_list_Mod -> KRExpr_Mod

with KRExpr_Mod_Mod_PairFunc :=
  | KRVar_Mod_Mod_PairFunc : (Mod -> Mod -> Mod) -> KRExpr_Mod_Mod_PairFunc
  | KRConcatMod_Func : KRExpr_Mod_Mod_PairFunc

with KRExpr_list_Mod: Type :=
  | KRVar_list_Mod : (list Mod) -> KRExpr_list_Mod
  | KRNil_list_Mod : KRExpr_list_Mod
  | KRCons_list_Mod : KRExpr_Mod -> KRExpr_list_Mod -> KRExpr_list_Mod
  | KRApp_list_Mod : KRExpr_list_Mod -> KRExpr_list_Mod -> KRExpr_list_Mod

with KRExpr_RegFileBase_Mod_Func :=
  | KRVar_RegFileBase_Mod_Func : (RegFileBase -> Mod) -> KRExpr_RegFileBase_Mod_Func
  | KRCastFunc: KRExpr_RegFileBase_Mod_Func

with KRExpr_RegInitT_string_Func :=
  | KRVar_RegInitT_string_Func : (RegInitT -> string) -> KRExpr_RegInitT_string_Func
  | KRfst_RegInitT_string_Func: KRExpr_RegInitT_string_Func

with KRExpr_DefMethT_string_Func :=
  | KRVar_DefMethT_string_Func : (DefMethT -> string) -> KRExpr_DefMethT_string_Func
  | KRfst_DefMethT_string_Func: KRExpr_DefMethT_string_Func

with KRExpr_Rule_string_Func :=
  | KRVar_Rule_string_Func : (Attribute (Action Void) -> string) -> KRExpr_Rule_string_Func
  | KRfst_Rule_string_Func: KRExpr_Rule_string_Func

with KRExpr_string: Type :=
  | KRVar_string : string -> KRExpr_string
  | KRConst_string : string -> KRExpr_string                           
  | KRstring_append : KRExpr_string -> KRExpr_string -> KRExpr_string
  | KRfst_RegInitT_string : KRExpr_RegInitT -> KRExpr_string
  | KRfst_DefMethT_string : KRExpr_DefMethT -> KRExpr_string
  | KRfst_Rule_string : KRExpr_Rule -> KRExpr_string

with KRExpr_list_string: Type :=
  | KRVar_list_string : list string -> KRExpr_list_string
  | KRNil_list_string : KRExpr_list_string
  | KRCons_list_string : KRExpr_string -> KRExpr_list_string -> KRExpr_list_string
  | KRApp_list_string : KRExpr_list_string -> KRExpr_list_string -> KRExpr_list_string
  | KRConcat_string : KRExpr_list_list_string -> KRExpr_list_string
  | KRgetCallsPerMod : KRExpr_Mod -> KRExpr_list_string
  | KRmap_RegInitT_string : KRExpr_RegInitT_string_Func -> KRExpr_list_RegInitT -> KRExpr_list_string
  | KRmap_DefMethT_string : KRExpr_DefMethT_string_Func -> KRExpr_list_DefMethT -> KRExpr_list_string
  | KRmap_Rule_string : KRExpr_Rule_string_Func -> KRExpr_list_Rule -> KRExpr_list_string

with KRExpr_list_list_string: Type :=
  | KRVar_list_list_string : list (list string) -> KRExpr_list_list_string
  | KRNil_list_list_string : KRExpr_list_list_string
  | KRCons_list_list_string : KRExpr_list_string -> KRExpr_list_list_string -> KRExpr_list_list_string
  | KRApp_list_list_string : KRExpr_list_list_string -> KRExpr_list_list_string -> KRExpr_list_list_string

with KRExpr_Prop: Type :=
  | KRVar_Prop : Prop -> KRExpr_Prop
  | KRTrue_Prop : KRExpr_Prop
  | KRFalse_Prop : KRExpr_Prop
  | KRAnd_Prop : KRExpr_Prop -> KRExpr_Prop -> KRExpr_Prop
  | KROr_Prop : KRExpr_Prop -> KRExpr_Prop -> KRExpr_Prop
  | KRNot_Prop : KRExpr_Prop -> KRExpr_Prop
  | KRIn_string_Prop : KRExpr_string -> KRExpr_list_string -> KRExpr_Prop
  | KREq_string_Prop : KRExpr_string -> KRExpr_string -> KRExpr_Prop
  | KRIn_RegInitT_Prop : KRExpr_RegInitT -> KRExpr_list_RegInitT -> KRExpr_Prop
  | KREq_RegInitT_Prop : KRExpr_RegInitT -> KRExpr_RegInitT -> KRExpr_Prop
  | KRIn_Rule_Prop : KRExpr_Rule -> KRExpr_list_Rule -> KRExpr_Prop
  | KREq_Rule_Prop : KRExpr_Rule -> KRExpr_Rule -> KRExpr_Prop
  | KRIn_DefMethT_Prop : KRExpr_DefMethT -> KRExpr_list_DefMethT -> KRExpr_Prop
  | KREq_DefMethT_Prop : KRExpr_DefMethT -> KRExpr_DefMethT -> KRExpr_Prop
  | KRDisjKey_RegInitT : KRExpr_list_RegInitT -> KRExpr_list_RegInitT -> KRExpr_Prop
  | KRDisjKey_DefMethT : KRExpr_list_DefMethT -> KRExpr_list_DefMethT -> KRExpr_Prop
  | KRDisjKey_Rule : KRExpr_list_Rule -> KRExpr_list_Rule -> KRExpr_Prop.








(******************************************************************************************)


Fixpoint KRExprDenote_RegInitValT(e: KRExpr_RegInitValT) : sigT RegInitValT :=
  match e with
  | KRVar_RegInitValT x => x
  end.

Fixpoint KRExprDenote_ActionVoid (e: KRExpr_ActionVoid) : Action Void :=
  match e with
  | KRVar_ActionVoid v => v
  end.
         
Fixpoint KRExprDenote_MethodT (e: KRExpr_MethodT) : sigT MethodT :=
  match e with
  | KRVar_MethodT v => v
  end.

(******************************************************************************************)

Fixpoint KRExprDenote_RegFileBase_Mod_Func(f: KRExpr_RegFileBase_Mod_Func) :=
  match f with
  | KRCastFunc => (fun m : RegFileBase => Base (BaseRegFile m))
  | KRVar_RegFileBase_Mod_Func f => f
  end.

Fixpoint KRExprDenote_RegInitT_string_Func(f: KRExpr_RegInitT_string_Func) : (RegInitT -> string) :=
  match f with
  | KRVar_RegInitT_string_Func v => v
  | KRfst_RegInitT_string_Func => fst
  end.

Fixpoint KRExprDenote_DefMethT_string_Func(f: KRExpr_DefMethT_string_Func) : (DefMethT -> string) :=
  match f with
  | KRVar_DefMethT_string_Func v => v
  | KRfst_DefMethT_string_Func => fst
  end.

Fixpoint KRExprDenote_RegFileBase_list_RegInitT_Func (f: KRExpr_RegFileBase_list_RegInitT_Func) :=
  match f with
  | KRVar_RegFileBase_list_RegInitT_Func f => f
  | KRgetRegFileRegistersFunc => getRegFileRegisters
  end.

Fixpoint KRExprDenote_Mod_list_RegInitT_Func (f: KRExpr_Mod_list_RegInitT_Func) :=
  match f with
  | KRVar_Mod_list_RegInitT_Func f => f
  | KRgetAllRegistersFunc => getAllRegisters
  end.

Fixpoint KRExprDenote_Mod_list_Rule_Func(f: KRExpr_Mod_list_Rule_Func) :=
  match f with
  | KRVar_Mod_list_Rule_Func f' => f'
  | KRgetAllRulesFunc => getAllRules
  end.

Fixpoint KRExprDenote_Mod_list_DefMethT_Func(f: KRExpr_Mod_list_DefMethT_Func) : (Mod -> list DefMethT) :=
  match f with
  | KRVar_Mod_list_DefMethT_Func f => f
  | KRgetAllMethodsFunc => getAllMethods
  end.

Fixpoint KRExprDenote_RegFileBase_list_DefMethT_Func(f: KRExpr_RegFileBase_list_DefMethT_Func) :=
  match f with
  | KRVar_RegFileBase_list_DefMethT_Func f => f
  | KRgetRegFileMethodsFunc => getRegFileMethods
  end.

Fixpoint KRExprDenote_Mod_list_string_Func(f: KRExpr_Mod_list_string_Func) : (Mod -> (list string)) :=
  match f with
  | KRVar_Mod_list_string_Func f => f
  | KRgetCallsPerModFunc => getCallsPerMod
  end.

Fixpoint KRExprDenote_Mod_Mod_PairFunc(f: KRExpr_Mod_Mod_PairFunc) :=
  match f with
  | KRVar_Mod_Mod_PairFunc f => f
  | KRConcatMod_Func => ConcatMod
  end.

Fixpoint KRExprDenote_Rule_string_Func(f: KRExpr_Rule_string_Func) : (Attribute (Action Void) -> string) :=
  match f with
  | KRVar_Rule_string_Func v => v
  | KRfst_Rule_string_Func => fst
  end.

(******************************************************************************************)

Fixpoint KRExprDenote_RegInitT (e:KRExpr_RegInitT) : RegInitT :=
  match e with
  | KRVar_RegInitT v => v
  | KRPair_RegInitT s v => (KRExprDenote_string s, KRExprDenote_RegInitValT v)
  end

with KRExprDenote_DefMethT (e:KRExpr_DefMethT) : DefMethT :=
  match e with
  | KRVar_DefMethT v => v
  | KRPair_DefMethT s v => (KRExprDenote_string s,KRExprDenote_MethodT v)
end
    
with KRExprDenote_string(s:KRExpr_string) :=
  match s with
  | KRVar_string s => s
  | KRConst_string s => s
  | KRstring_append a b => ((KRExprDenote_string a)++(KRExprDenote_string b))%string
  | KRfst_RegInitT_string r => fst (KRExprDenote_RegInitT r)
  | KRfst_DefMethT_string r => fst (KRExprDenote_DefMethT r)
  | KRfst_Rule_string r => fst (KRExprDenote_Rule r)
  end

with KRExprDenote_Rule (e:KRExpr_Rule) : Attribute (Action Void) :=
  match e with
  | KRVar_Rule v => v
  | KRPair_Rule s v => (KRExprDenote_string s, KRExprDenote_ActionVoid v)
  end.

(******************************************************************************************)

Fixpoint KRExprDenote_ModuleElt (e:KRExpr_ModuleElt) : ModuleElt :=
  match e with
  | KRVar_ModuleElt v => v
  | KRMERegister r => MERegister (KRExprDenote_RegInitT r)
  | KRMERule r => MERule (KRExprDenote_Rule r)
  | KRMEMeth m => MEMeth (KRExprDenote_DefMethT m)
  end.

(******************************************************************************************)

Fixpoint KRExprDenote_RegFileBase(m: KRExpr_RegFileBase) :=
  match m with
  | KRVar_RegFileBase m => m
  end.

(******************************************************************************************)

Fixpoint KRExprDenote_list_RegFileBase(l: KRExpr_list_RegFileBase) :=
  match l with
  | KRVar_list_RegFileBase l => l
  | KRNil_list_RegFileBase => nil
  | KRCons_list_RegFileBase f r => cons (KRExprDenote_RegFileBase f) (KRExprDenote_list_RegFileBase r)
  | KRApp_list_RegFileBase a b => app (KRExprDenote_list_RegFileBase a) (KRExprDenote_list_RegFileBase b)
  end.

(******************************************************************************************)

Fixpoint KRExprDenote_list_RegInitT (e:KRExpr_list_RegInitT) : list RegInitT :=
  match e with
  | KRVar_list_RegInitT v => v
  | KRNil_list_RegInitT => nil
  | KRCons_list_RegInitT f r => cons (KRExprDenote_RegInitT f) (KRExprDenote_list_RegInitT r)
  | KRApp_list_RegInitT f r => app (KRExprDenote_list_RegInitT f) (KRExprDenote_list_RegInitT r)
  | KRgetRegisters m => getRegisters (KRExprDenote_BaseModule m)
  | KRgetAllRegisters m => getAllRegisters (KRExprDenote_Mod m)
  | KRMakeModule_regs r => makeModule_regs (KRExprDenote_list_ModuleElt r)
  | KRConcat_RegInitT r => concat (KRExprDenote_list_list_RegInitT r)
  end

with KRExprDenote_BaseModule (e:KRExpr_BaseModule) : BaseModule :=
  match e with
  | KRVar_BaseModule v => v
  | KRMakeModule e => makeModule (KRExprDenote_list_ModuleElt e)
  | KRBaseMod regs rules meths => BaseMod (KRExprDenote_list_RegInitT regs) (KRExprDenote_list_Rule rules) (KRExprDenote_list_DefMethT meths)
  | KRBaseRegFile b => BaseRegFile (KRExprDenote_RegFileBase b)
  end

with KRExprDenote_Mod (e:KRExpr_Mod) : Mod :=
  match e with
  | KRVar_Mod v => v
  | KRBase b => Base (KRExprDenote_BaseModule b)
  | KRConcatMod a b => ConcatMod (KRExprDenote_Mod a) (KRExprDenote_Mod b)
  | KRFold_right_Mod f a b => fold_right (KRExprDenote_Mod_Mod_PairFunc f) (KRExprDenote_Mod a) (KRExprDenote_list_Mod b)
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

with KRExprDenote_list_list_RegInitT (e:KRExpr_list_list_RegInitT) : list (list RegInitT) :=
  match e with
  | KRVar_list_list_RegInitT v => v
  | KRNil_list_list_RegInitT => nil
  | KRCons_list_list_RegInitT f r => cons (KRExprDenote_list_RegInitT f) (KRExprDenote_list_list_RegInitT r)
  | KRApp_list_list_RegInitT f r => app (KRExprDenote_list_list_RegInitT f) (KRExprDenote_list_list_RegInitT r)
  | KRMap_list_Mod_list_list_RegInitT f l => map (KRExprDenote_Mod_list_RegInitT_Func f) (KRExprDenote_list_Mod l)
  | KRMap_list_RegFileBase_list_list_RegInitT f l => map (KRExprDenote_RegFileBase_list_RegInitT_Func f) (KRExprDenote_list_RegFileBase l)
  end

with KRExprDenote_list_DefMethT (e:KRExpr_list_DefMethT) : list DefMethT :=
  match e with
  | KRVar_list_DefMethT v => v
  | KRNil_list_DefMethT => nil
  | KRCons_list_DefMethT f r => cons (KRExprDenote_DefMethT f) (KRExprDenote_list_DefMethT r)
  | KRApp_list_DefMethT f r => app (KRExprDenote_list_DefMethT f) (KRExprDenote_list_DefMethT r)
  | KRConcat_DefMethT r => concat (KRExprDenote_list_list_DefMethT r)
  | KRgetMethods m => getMethods (KRExprDenote_BaseModule m)
  | KRgetAllMethods m => getAllMethods (KRExprDenote_Mod m)
  | KRMakeModule_meths r => makeModule_meths (KRExprDenote_list_ModuleElt r)
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
  | KRConcat_Rule r => concat (KRExprDenote_list_list_Rule r)
  end

with KRExprDenote_list_Mod(m: KRExpr_list_Mod) : list Mod :=
  match m with
  | KRVar_list_Mod v => v
  | KRNil_list_Mod => nil
  | KRCons_list_Mod f r => cons (KRExprDenote_Mod f) (KRExprDenote_list_Mod r)
  | KRApp_list_Mod f r => app (KRExprDenote_list_Mod f) (KRExprDenote_list_Mod r)
  end

with KRExprDenote_list_list_DefMethT (e:KRExpr_list_list_DefMethT) : list (list DefMethT) :=
  match e with
  | KRVar_list_list_DefMethT v => v
  | KRNil_list_list_DefMethT => nil
  | KRCons_list_list_DefMethT f r => cons (KRExprDenote_list_DefMethT f) (KRExprDenote_list_list_DefMethT r)
  | KRApp_list_list_DefMethT f r => app (KRExprDenote_list_list_DefMethT f) (KRExprDenote_list_list_DefMethT r)
  | KRMap_list_Mod_list_list_DefMethT f l => map (KRExprDenote_Mod_list_DefMethT_Func f) (KRExprDenote_list_Mod l)
  | KRMap_list_RegFileBase_list_list_DefMethT f l => map (KRExprDenote_RegFileBase_list_DefMethT_Func f) (KRExprDenote_list_RegFileBase l)
  end

with KRExprDenote_list_list_Rule (e:KRExpr_list_list_Rule) : list (list (Attribute (Action Void))) :=
  match e with
  | KRVar_list_list_Rule v => v
  | KRNil_list_list_Rule => nil
  | KRCons_list_list_Rule f r => cons (KRExprDenote_list_Rule f) (KRExprDenote_list_list_Rule r)
  | KRApp_list_list_Rule f r => app (KRExprDenote_list_list_Rule f) (KRExprDenote_list_list_Rule r)
  | KRMap_list_Mod_list_list_Rule f l => map (KRExprDenote_Mod_list_Rule_Func f) (KRExprDenote_list_Mod l)
  end.

(******************************************************************************************)

Fixpoint KRExprDenote_CallWithSign(c: KRExpr_CallWithSign) :=
  match c with
  | KRVar_CallWithSign v => v
  end.
    
(******************************************************************************************)

Fixpoint KRExprDenote_list_CallWithSign(c: KRExpr_list_CallWithSign) :=
  match c with
  | KRVar_list_CallWithSign c => c
  | KRNil_list_CallWithSign => nil
  | KRCons_list_CallWithSign f r => cons (KRExprDenote_CallWithSign f) (KRExprDenote_list_CallWithSign r)
  | KRApp_list_CallWithSign f r => app (KRExprDenote_list_CallWithSign f) (KRExprDenote_list_CallWithSign r)
  | KRConcat_CallWithSign l => concat (KRExprDenote_list_list_CallWithSign l)
  end

with KRExprDenote_list_list_CallWithSign(c:  KRExpr_list_list_CallWithSign) :=
  match c with
  | KRVar_list_list_CallWithSign c => c
  | KRNil_list_list_CallWithSign => nil
  | KRCons_list_list_CallWithSign f r => cons (KRExprDenote_list_CallWithSign f) (KRExprDenote_list_list_CallWithSign r)
  | KRApp_list_list_CallWithSign f r => app (KRExprDenote_list_list_CallWithSign f) (KRExprDenote_list_list_CallWithSign r)
  (*| KRMap_list_Mod_list_list_CallWithSign f l =>  (KRExprDenote_Mod_list_CallWithSign_Func f) (KRExprDenote_list_Mod l)*)
  end.
    
(******************************************************************************************)

Fixpoint KRExprDenote_list_list_ModuleElt (e:KRExpr_list_list_ModuleElt) : list (list ModuleElt) :=
  match e with
  | KRVar_list_list_ModuleElt v => v
  | KRNil_list_list_ModuleElt => nil
  | KRCons_list_list_ModuleElt f r => cons (KRExprDenote_list_ModuleElt f) (KRExprDenote_list_list_ModuleElt r)
  | KRApp_list_list_ModuleElt f r => app (KRExprDenote_list_list_ModuleElt f) (KRExprDenote_list_list_ModuleElt r)
  end.

(******************************************************************************************)

Fixpoint KRExprDenote_list_BaseModule(e:KRExpr_list_BaseModule): list BaseModule :=
  match e with
  | KRVar_list_BaseModule v => v
  | KRNil_list_BaseModule => nil
  | KRCons_list_BaseModule f r => cons (KRExprDenote_BaseModule f) (KRExprDenote_list_BaseModule r)
  | KRApp_list_BaseModule f r => app (KRExprDenote_list_BaseModule f) (KRExprDenote_list_BaseModule r)
  end.

(******************************************************************************************)

Fixpoint KRExprDenote_list_string(l: KRExpr_list_string) : list string :=
  match l with
  | KRVar_list_string v => v
  | KRNil_list_string => nil
  | KRCons_list_string a b => cons (KRExprDenote_string a) (KRExprDenote_list_string b)
  | KRApp_list_string a b => app (KRExprDenote_list_string a) (KRExprDenote_list_string b)
  | KRgetCallsPerMod m => getCallsPerMod (KRExprDenote_Mod m)
  | KRConcat_string l => concat (KRExprDenote_list_list_string l)
  | KRmap_RegInitT_string f l => map (KRExprDenote_RegInitT_string_Func f) (KRExprDenote_list_RegInitT l)
  | KRmap_DefMethT_string f l => map (KRExprDenote_DefMethT_string_Func f) (KRExprDenote_list_DefMethT l)
  | KRmap_Rule_string f l => map (KRExprDenote_Rule_string_Func f) (KRExprDenote_list_Rule l)
  end

with KRExprDenote_list_list_string(l : KRExpr_list_list_string) : list (list string) :=
  match l with
  | KRVar_list_list_string v => v
  | KRNil_list_list_string => nil
  | KRCons_list_list_string a b => cons (KRExprDenote_list_string a) (KRExprDenote_list_list_string b)
  | KRApp_list_list_string a b => app (KRExprDenote_list_list_string a) (KRExprDenote_list_list_string b)
  end.

Fixpoint KRExprDenote_Prop(p: KRExpr_Prop) :=
  match p with           
  | KRVar_Prop p => p
  | KRTrue_Prop => True
  | KRFalse_Prop => False
  | KRAnd_Prop a b => (KRExprDenote_Prop a) /\ (KRExprDenote_Prop b)
  | KROr_Prop a b => (KRExprDenote_Prop a) \/ (KRExprDenote_Prop b)
  | KRNot_Prop a => ~(KRExprDenote_Prop a)
  | KRIn_string_Prop a b => In (KRExprDenote_string a) (KRExprDenote_list_string b)
  | KREq_string_Prop a b => ((KRExprDenote_string a)=(KRExprDenote_string b))
  | KRIn_RegInitT_Prop a b => In (KRExprDenote_RegInitT a) (KRExprDenote_list_RegInitT b)
  | KREq_RegInitT_Prop a b => ((KRExprDenote_RegInitT a)=(KRExprDenote_RegInitT b))
  | KRIn_Rule_Prop a b => In (KRExprDenote_Rule a) (KRExprDenote_list_Rule b)
  | KREq_Rule_Prop a b => ((KRExprDenote_Rule a)=(KRExprDenote_Rule b))
  | KRIn_DefMethT_Prop a b => In (KRExprDenote_DefMethT a) (KRExprDenote_list_DefMethT b)
  | KREq_DefMethT_Prop a b => ((KRExprDenote_DefMethT a)=(KRExprDenote_DefMethT b))
  | KRDisjKey_RegInitT a b => DisjKey (KRExprDenote_list_RegInitT a) (KRExprDenote_list_RegInitT b)
  | KRDisjKey_DefMethT a b => DisjKey (KRExprDenote_list_DefMethT a) (KRExprDenote_list_DefMethT b)
  | KRDisjKey_Rule a b => DisjKey (KRExprDenote_list_Rule a) (KRExprDenote_list_Rule b)
  end.

(******************************************************************************************)




Inductive KRElem: Type :=
| KRElemRegInitT : KRElem
| KRElemRegInitValT : KRElem
| KRElemRule : KRElem
| KRElemActionVoid : KRElem
| KRElemMethodT : KRElem
| KRElemDefMethT : KRElem
| KRElemModuleElt: KRElem
| KRElemMod : KRElem
| KRElemBaseModule : KRElem
| KRElemString : KRElem
| KRElemProp : KRElem
| KRElemRegFileBase : KRElem
| KRElemCallWithSign : KRElem
| KRElemMod_Mod_PairFunc : KRElem
| KRElemRegFileBase_list_RegInitT_Func : KRElem
| KRElemRegFileBase_Mod_Func : KRElem
| KRElemMod_list_string_Func : KRElem
| KRElemMod_list_DefMethT_Func : KRElem
| KRElemRegFileBase_list_DefMethT_Func : KRElem
| KRElemMod_list_Rule_Func : KRElem
| KRElemMod_list_RegInitT_Func : KRElem
| KRElemRegInitT_string_Func : KRElem
| KRElemDefMethT_string_Func : KRElem
| KRElemRule_string_Func : KRElem.


Inductive KRType : Type :=
  | KRTypeElem: KRElem -> KRType
  | KRTypeList: KRType -> KRType.

Ltac isBoolConstant x :=
  match x with
  | true => idtac
  | false => idtac
  end.

Ltac isAsciiConstant x :=
  match x with
  | Ascii ?A ?B ?C ?D ?E ?F ?G ?H => isBoolConstant A;isBoolConstant B;isBoolConstant C;isBoolConstant D;
                                     isBoolConstant E;isBoolConstant F;isBoolConstant G;isBoolConstant H
  end.

Ltac isStringConstant s :=
  match s with
  | EmptyString => idtac
  | String.String ?A ?R => isAsciiConstant A;isStringConstant R
  end.

Ltac KRExprReify e t :=
  match e with
  | nil => match t with
           | KRTypeList (KRTypeElem KRElemRegInitT) => constr:(@KRNil_list_RegInitT)
           | KRTypeList (KRTypeList (KRTypeElem KRElemRegInitT)) => constr:(@KRNil_list_list_RegInitT)
           | KRTypeList (KRTypeElem KRElemRule) => constr:(@KRNil_list_Rule)
           | KRTypeList (KRTypeList (KRTypeElem KRElemRule)) => constr:(@KRNil_list_list_Rule)
           | KRTypeList (KRTypeElem KRElemDefMethT) => constr:(@KRNil_list_DefMethT)
           | KRTypeList (KRTypeList (KRTypeElem KRElemDefMethT)) => constr:(@KRNil_list_list_DefMethT)
           | KRTypeList (KRTypeElem KRElemModuleElt) => constr:(@KRNil_list_ModuleElt)
           | KRTypeList (KRTypeList (KRTypeElem KRElemModuleElt)) => constr:(@KRNil_list_list_ModuleElt)
           | KRTypeList (KRTypeElem KRElemMod) => constr:(@KRNil_list_Mod)
           | KRTypeList (KRTypeElem KRElemCallWithSign) => constr:(@KRNil_list_CallWithSign)
           | KRTypeList (KRTypeList (KRTypeElem KRElemCallWithSign)) => constr:(@KRNil_list_list_CallWithSign)
           | KRTypeList (KRTypeElem KRElemString) => constr:(@KRNil_list_string)
           | KRTypeList (KRTypeList (KRTypeElem KRElemString)) => constr:(@KRNil_list_list_string)
           | KRTypeList (KRTypeElem KRElemRegFileBase) => constr:(@KRNil_list_RegFileBase)
           end
  | cons ?F ?R => match t with
                  | KRTypeList (KRTypeElem KRElemRegInitT)  => let fr :=ltac:(KRExprReify F (KRTypeElem KRElemRegInitT)) in
                                                               let re:=ltac:(KRExprReify R (KRTypeList (KRTypeElem KRElemRegInitT))) in
                                                               constr:(KRCons_list_RegInitT fr re)
                  | KRTypeList (KRTypeList (KRTypeElem KRElemRegInitT))  => let fr :=ltac:(KRExprReify F (KRTypeList (KRTypeElem KRElemRegInitT))) in
                                                               let re:=ltac:(KRExprReify R (KRTypeList (KRTypeList (KRTypeElem KRElemRegInitT)))) in
                                                               constr:(KRCons_list_list_RegInitT fr re)
                  | KRTypeList (KRTypeElem KRElemRule)  => let fr :=ltac:(KRExprReify F (KRTypeElem KRElemRule)) in
                                                               let re:=ltac:(KRExprReify R (KRTypeList (KRTypeElem KRElemRule))) in
                                                               constr:(KRCons_list_Rule fr re)
                  | KRTypeList (KRTypeList (KRTypeElem KRElemRule))  => let fr :=ltac:(KRExprReify F (KRTypeList (KRTypeElem KRElemRule))) in
                                                               let re:=ltac:(KRExprReify R (KRTypeList (KRTypeList (KRTypeElem KRElemRule)))) in
                                                               constr:(KRCons_list_list_Rule fr re)
                  | KRTypeList (KRTypeElem KRElemDefMethT)  => let fr :=ltac:(KRExprReify F (KRTypeElem KRElemDefMethT)) in
                                                               let re:=ltac:(KRExprReify R (KRTypeList (KRTypeElem KRElemDefMethT))) in
                                                               constr:(KRCons_list_DefMethT fr re)
                  | KRTypeList (KRTypeList (KRTypeElem KRElemDefMethT))  => let fr :=ltac:(KRExprReify F (KRTypeList (KRTypeElem KRElemDefMethT))) in
                                                               let re:=ltac:(KRExprReify R (KRTypeList (KRTypeList (KRTypeElem KRElemDefMethT)))) in
                                                               constr:(KRCons_list_list_DefMethT fr re)
                  | KRTypeList (KRTypeElem KRElemModuleElt)  => let fr :=ltac:(KRExprReify F (KRTypeElem KRElemModuleElt)) in
                                                               let re:=ltac:(KRExprReify R (KRTypeList (KRTypeElem KRElemModuleElt))) in
                                                               constr:(KRCons_list_ModuleElt fr re)
                  | KRTypeList (KRTypeList (KRTypeElem KRElemModuleElt))  => let fr :=ltac:(KRExprReify F (KRTypeList (KRTypeElem KRElemModuleElt))) in
                                                               let re:=ltac:(KRExprReify R (KRTypeList (KRTypeList (KRTypeElem KRElemModuleElt)))) in
                                                               constr:(KRCons_list_list_ModuleElt fr re)
                  | KRTypeList (KRTypeElem KRElemMod)  => let fr :=ltac:(KRExprReify F (KRTypeElem KRElemMod)) in
                                                               let re:=ltac:(KRExprReify R (KRTypeList (KRTypeElem KRElemMod))) in
                                                               constr:(KRCons_list_Mod fr re)
                  | KRTypeList (KRTypeElem KRElemCallWithSign)  => let fr :=ltac:(KRExprReify F (KRTypeElem KRElemCallWithSign)) in
                                                               let re:=ltac:(KRExprReify R (KRTypeList (KRTypeElem KRElemCallWithSign))) in
                                                               constr:(KRCons_list_CallWithSign fr re)
                  | KRTypeList (KRTypeList (KRTypeElem KRElemCallWithSign))  => let fr :=ltac:(KRExprReify F (KRTypeList (KRTypeElem KRElemCallWithSign))) in
                                                               let re:=ltac:(KRExprReify R (KRTypeList (KRTypeList (KRTypeElem KRElemCallWithSign)))) in
                                                               constr:(KRCons_list_list_CallWithSign fr re)
                  | KRTypeList (KRTypeElem KRElemString)  => let fr :=ltac:(KRExprReify F (KRTypeElem KRElemString)) in
                                                               let re:=ltac:(KRExprReify R (KRTypeList (KRTypeElem KRElemString))) in
                                                               constr:(KRCons_list_string fr re)
                  | KRTypeList (KRTypeList (KRTypeElem KRElemString))  => let fr :=ltac:(KRExprReify F (KRTypeList (KRTypeElem KRElemString))) in
                                                               let re:=ltac:(KRExprReify R (KRTypeList (KRTypeList (KRTypeElem KRElemString)))) in
                                                               constr:(KRCons_list_list_string fr re)
                  | KRTypeList (KRTypeElem KRElemRegFileBase)  => let fr :=ltac:(KRExprReify F (KRTypeElem KRElemRegFileBase)) in
                                                                  let re:=ltac:(KRExprReify R (KRTypeList (KRTypeElem KRElemRegFileBase))) in
                                                                  constr:(KRCons_list_RegFileBase fr re)
                  end
  | (?A ++ ?B)%string => let a := ltac:(KRExprReify A (KRTypeElem KRElemString)) in
                         let b := ltac:(KRExprReify B (KRTypeElem KRElemString)) in
                         match t with
                         | (KRTypeElem KRElemString) => constr:(KRstring_append a b)
                         end
  | app ?F ?R => let x1 := ltac:(KRExprReify F t) in
                 let x2 := ltac:(KRExprReify R t) in
                 match t with
                 | KRTypeList (KRTypeElem KRElemRegInitT) => constr:(KRApp_list_RegInitT x1 x2)
                 | KRTypeList (KRTypeList (KRTypeElem KRElemRegInitT)) => constr:(KRApp_list_list_RegInitT x1 x2)
                 | KRTypeList (KRTypeElem KRElemRule) => constr:(KRApp_list_Rule x1 x2)
                 | KRTypeList (KRTypeList (KRTypeElem KRElemRule)) => constr:(KRApp_list_list_Rule x1 x2)
                 | KRTypeList (KRTypeElem KRElemDefMethT) => constr:(KRApp_list_DefMethT x1 x2)
                 | KRTypeList (KRTypeList (KRTypeElem KRElemDefMethT)) => constr:(KRApp_list_list_DefMethT x1 x2)
                 | KRTypeList (KRTypeElem KRElemModuleElt) => constr:(KRApp_list_ModuleElt x1 x2)
                 | KRTypeList (KRTypeList (KRTypeElem KRElemModuleElt)) => constr:(KRApp_list_list_ModuleElt x1 x2)
                 | KRTypeList (KRTypeElem KRElemMod) => constr:(KRApp_list_Mod x1 x2)
                 | KRTypeList (KRTypeElem KRElemCallWithSign) => constr:(KRApp_list_CallWithSign x1 x2)
                 | KRTypeList (KRTypeElem KRElemString) => constr:(KRApp_list_string x1 x2)
                 | KRTypeList (KRTypeList (KRTypeElem KRElemString)) => constr:(KRApp_list_list_string x1 x2)
                 | KRTypeList (KRTypeElem KRElemRegFileBase) => constr:(KRApp_list_RegFileBase x1 x2)
                 | KRTypeElem KRElemString => constr:(KRstring_append x1 x2)
                 end
  | concat ?F => let x := ltac:(KRExprReify F (KRTypeList t)) in
                 match t with
                 | KRTypeList (KRTypeElem KRElemRegInitT) => constr:(KRConcat_RegInitT x)
                 | KRTypeList (KRTypeElem KRElemRule) => constr:(KRConcat_Rule x)
                 | KRTypeList (KRTypeElem KRElemDefMethT) => constr:(KRConcat_DefMethT x)
                 | KRTypeList (KRTypeElem KRElemString) => constr:(KRConcat_string x)
                 end
  | map ?F ?L => match F with
                 | getAllRegisters => let l := ltac:(KRExprReify L (KRTypeList (KRTypeElem KRElemMod))) in
                                          constr:(KRMap_list_Mod_list_list_RegInitT KRgetAllRegistersFunc l)
                 | getRegFileRegisters => let l := ltac:(KRExprReify L (KRTypeList (KRTypeElem KRElemRegFileBase))) in
                                              constr:(KRMap_list_RegFileBase_list_list_RegInitT KRgetRegFileRegistersFunc l)
                 | getAllRules => let l := ltac:(KRExprReify L (KRTypeList (KRTypeElem KRElemMod))) in
                                      constr:(KRMap_list_Mod_list_list_Rule KRgetAllRulesFunc l)
                 | getAllMethods => let l := ltac:(KRExprReify L (KRTypeList (KRTypeElem KRElemMod))) in
                                        constr:(KRMap_list_Mod_list_list_DefMethT KRgetAllMethodsFunc l)
                 | getRegFileMethods => let l := ltac:(KRExprReify L (KRTypeList (KRTypeElem KRElemRegFileBase))) in
                                            constr:(KRMap_list_Mod_list_list_DefMethT KRgetRegFileMethodsFunc l)
                 | fst => let l := ltac:(KRExprReify L (KRTypeList (KRTypeElem KRElemRegInitT))) in
                                        constr:(KRmap_RegInitT_string KRfst_RegInitT_string l)
                 | fst => let l := ltac:(KRExprReify L (KRTypeList (KRTypeElem KRElemDefMethT))) in
                                        constr:(KRmap_DefMethT_string KRfst_DefMethT_string l)
                 | fst => let l := ltac:(KRExprReify L (KRTypeList (KRTypeElem KRElemRule))) in
                                        constr:(KRmap_Rule_string KRfst_Rule_string l)
                 end
  | MERegister ?E => let x := ltac:(KRExprReify E (KRTypeElem KRElemRegInitT)) in
                         constr:(KRMERegister x)
  | Registers ?E => let x := ltac:(KRExprReify E (KRTypeList (KRTypeElem KRElemRegInitT))) in
                       constr:(KRRegisters x)
  | getRegisters ?E => let x := ltac:(KRExprReify E (KRTypeList (KRTypeElem KRElemBaseModule))) in
                       constr:(KRgetRegisters x)
  | getAllRegisters ?E => match t with
                            (KRTypeList (KRTypeElem KRElemRegInitT)) =>  let x := ltac:(KRExprReify E (KRTypeElem KRElemMod)) in
                                                                  constr:(KRgetAllRegisters x)
                          end
  | getAllRegisters ?E => match t with
                            (KRTypeList (KRTypeElem KRElemRegInitT)) => let x := ltac:(KRExprReify E (KRTypeElem KRElemMod)) in
                                                                 constr:(KRgetAllRegisters (@KRBase x))
                          end
  | getAllRegisters ?E => match t with
                            (KRTypeList (KRTypeElem KRElemRegInitT)) => let x := ltac:(KRExprReify E (KRTypeElem KRElemBaseModule)) in
                                                                 constr:(KRgetAllRegisters x)
                          | _ => fail 1
                          end
  | getAllRegisters ?E => match t with
                            (KRTypeList (KRTypeElem KRElemRegInitT)) => let x := ltac:(KRExprReify E (KRTypeElem KRElemBaseModule)) in
                                                                        constr:(KRgetAllRegisters (@KRBase x))
                          | _ => fail 1
                          end
  | MERule ?E => let  x := ltac:(KRExprReify E (KRTypeElem KRElemRule)) in
                     constr:(KRMERule x)
  | Rules ?E =>  match t with
                   (KRTypeList (KRTypeElem KRElemRule)) => let x := ltac:(KRExprReify E (KRTypeList (KRTypeElem KRElemRule))) in
                                                        
                                                        constr:(KRRules x)
                 end
  | getRules ?E => match t with
                     (KRTypeList (KRTypeElem KRElemRule)) => let x := ltac:(KRExprReify E (KRTypeElem KRElemBaseModule)) in
                                                      constr:(KRgetRules x)
                   | _ => fail 1
                   end
  | getAllRules ?E => match t with
                         (KRTypeList (KRTypeElem KRElemRule)) => let x := ltac:(KRExprReify E (KRTypeElem KRElemMod)) in
                                                          constr:(KRgetAllRules x)
                       | _ => fail 1
                       end
  | MEMeth ?E => match t with
                         (KRTypeElem KRElemModuleElt) => let x := ltac:(KRExprReify E (KRTypeElem KRElemDefMethT)) in
                                                                  constr:(KRMEMeth x)
                 end
  | Methods ?E => match t with
                         (KRTypeList (KRTypeElem KRElemModuleElt)) => let x := ltac:(KRExprReify E (KRTypeList (KRTypeElem KRElemDefMethT))) in
                                                          constr:(KRMethods x)
                  end
  | getMethods ?E => match t with
                         (KRTypeList (KRTypeElem KRElemDefMethT)) => let x := ltac:(KRExprReify E (KRTypeElem KRElemBaseModule)) in
                                                                     constr:(KRgetMethods x)
                     | _ => fail 1
                     end
  | getAllMethods ?E => match t with
                         (KRTypeList (KRTypeElem KRElemDefMethT)) => let x := ltac:(KRExprReify E (KRTypeElem KRElemMod)) in
                                                                     constr:(KRgetAllMethods x)
                        | _ => fail 1
                        end
  | makeModule_regs ?X => let x := ltac:(KRExprReify X (KRTypeList (KRTypeElem KRElemModuleElt))) in
                              constr:(KRMakeModule_regs x)
  | makeModule_rules ?E => let x := ltac:(KRExprReify E (KRTypeList (KRTypeElem KRElemModuleElt))) in
                               constr:(KRMakeModule_rules x)
  | makeModule_meths ?E => let x := ltac:(KRExprReify E (KRTypeList (KRTypeElem KRElemModuleElt))) in 
                           constr:(KRMakeModule_meths x)
  | makeModule ?E => let x := ltac:(KRExprReify E (KRTypeList (KRTypeElem KRElemModuleElt))) in 
                     constr:(KRMakeModule x)
  | BaseRegFile ?E => let x := ltac:(KRExprReify E (KRTypeList (KRTypeElem KRElemRegFileBase))) in 
                      constr:(KRBaseRegFile x)
  | BaseMod ?R ?U ?M => let regs := ltac:(KRExprReify R (KRTypeList (KRTypeElem KRElemRegInitT))) in
                        let rules := ltac:(KRExprReify U (KRTypeList (KRTypeElem KRElemRule))) in
                        let meths := ltac:(KRExprReify M (KRTypeList (KRTypeElem KRElemDefMethT))) in
                        constr:(KRBaseMod regs rules meths)
  | Base ?B => let m := ltac:(KRExprReify B (KRTypeElem KRElemBaseModule)) in
               constr:(KRBase m)
  | ConcatMod ?A ?B => match t with
                       | (KRTypeElem KRElemMod) => let a := ltac:(KRExprReify A (KRTypeElem KRElemMod)) in
                                                   let b := ltac:(KRExprReify B (KRTypeElem KRElemMod)) in
                                                   constr:(KRConcatMod a b)
                       | _ => fail 1
                       end
  | True => constr:(KRTrue_Prop)
  | False => constr:(KRFalse_Prop)
  | ?A /\ ?B => let a := ltac:(KRExprReify A (KRTypeElem KRElemProp)) in
                let b := ltac:(KRExprReify B (KRTypeElem KRElemProp)) in
                    constr:(KRAnd_Prop a b)
  | ?A \/ ?B => let a := ltac:(KRExprReify A (KRTypeElem KRElemProp)) in
                let b := ltac:(KRExprReify B (KRTypeElem KRElemProp)) in
                    constr:(KROr_Prop a b)
  | ~ ?A => let a := ltac:(KRExprReify A (KRTypeElem KRElemProp)) in
                     constr:(KRNot_Prop a)
  | ( ?A , ?B ) => match t with
                   | (KRTypeElem KRElemRegInitT) => let a := ltac:(KRExprReify A (KRTypeElem KRElemString)) in
                                                    let b := ltac:(KRExprReify B (KRTypeElem KRElemRegInitValT)) in
                                                    constr:(KRPair_RegInitT A B)
                   | (KRTypeElem KRElemDefMethT) => let a := ltac:(KRExprReify A (KRTypeElem KRElemString)) in
                                                    let b := ltac:(KRExprReify B (KRTypeElem KRElemMethodT)) in
                                                    constr:(KRPair_RegInitT A B)
                   end
  | In ?A ?B => let a := ltac:(KRExprReify A (KRTypeElem KRElemString)) in
             let b := ltac:(KRExprReify B (KRTypeList (KRTypeElem KRElemString))) in
             constr:(KRIn_string_Prop a b)
  | In ?A ?B => let a := ltac:(KRExprReify A (KRTypeElem KRElemRegInitT)) in
             let b := ltac:(KRExprReify B (KRTypeList (KRTypeElem KRElemRegInitT))) in
             constr:(KRIn_RegInitT_Prop a b)
  | In ?A ?B => let a := ltac:(KRExprReify A (KRTypeElem KRElemRule)) in
             let b := ltac:(KRExprReify B (KRTypeList (KRTypeElem KRElemRule))) in
             constr:(KRIn_Rule_Prop a b)
  | In ?A ?B => let a := ltac:(KRExprReify A (KRTypeElem KRElemDefMethT)) in
             let b := ltac:(KRExprReify B (KRTypeList (KRTypeElem KRElemDefMethT))) in
             constr:(KRIn_DefMethT_Prop a b)
  | DisjKey ?A ?B => let a := ltac:(KRExprReify A (KRTypeList (KRTypeElem KRElemRegInitT))) in
                     let b := ltac:(KRExprReify B (KRTypeList (KRTypeElem KRElemRegInitT))) in
                     constr:(KRDisjKey_RegInitT a b)
  | DisjKey ?A ?B => let a := ltac:(KRExprReify A (KRTypeList (KRTypeElem KRElemDefMethT))) in
                     let b := ltac:(KRExprReify B (KRTypeList (KRTypeElem KRElemDefMethT))) in
                     constr:(KRDisjKey_DefMethT a b)
  | DisjKey ?A ?B => let a := ltac:(KRExprReify A (KRTypeList (KRTypeElem KRElemRule))) in
                     let b := ltac:(KRExprReify B (KRTypeList (KRTypeElem KRElemRule))) in
                     constr:(KRDisjKey_Rule a b)
  | fst ?A => match t with
              (KRTypeElem KRElemString) => let a := ltac:(KRExprReify A (KRTypeElem KRElemRegInitT)) in
                                           constr:(KRfst_RegInitT_string a)
              end
  | fst ?A => match t with
              (KRTypeElem KRElemString) => let a := ltac:(KRExprReify A (KRTypeElem KRElemDefMethT)) in
                                           constr:(KRfst_RegInitT_string a)
              end
  | ?A = ?B => match t with
               | (KRTypeElem KRElemProp) => let a := ltac:(KRExprReify A (KRTypeElem KRElemString)) in
                                            let b := ltac:(KRExprReify B (KRTypeElem KRElemString)) in
                                            constr:(KREq_string_Prop a b)
               end
  | fold_right ConcatMod ?M ?L =>
          match t with
          | (KRTypeElem KRElemMod) => let m := ltac:(KRExprReify M (KRTypeElem KRElemMod)) in
                                      let l := ltac:(KRExprReify L (KRTypeList (KRTypeElem KRElemMod))) in
                                      constr:(KRFold_right_Mod KRConcatMod_Func m l)
          | _ => fail 1
          end
  | ?X => match t with
          | (KRTypeElem KRElemString) => let q := isStringConstant X in
                                         constr:(KRConst_string X)
          | _ => fail 1
          end
  | ?X => match t with
          | (KRTypeElem KRElemRegInitT) => constr:(KRVar_RegInitT X)
          | (KRTypeElem KRElemRegInitValT) => constr:(KRVar_RegInitValT X)
          | (KRTypeElem KRElemRule) => constr:(KRVar_Rule X)
          | (KRTypeElem KRElemActionVoid) => constr:(KRVar_ActionVoid X)
          | (KRTypeElem KRElemDefMethT) => constr:(KRVar_DefMethT X)
          | (KRTypeElem KRElemMethodT) => constr:(KRVar_MethodT X)
          | (KRTypeElem KRElemModuleElt) => constr:(KRVar_ModuleElt X)
          | (KRTypeList (KRTypeElem KRElemRegInitT)) => constr:(KRVar_list_RegInitT X)
          | (KRTypeList (KRTypeList (KRTypeElem KRElemRegInitT))) => constr:(KRVar_list_list_RegInitT X)
          | (KRTypeList (KRTypeElem KRElemRule)) => constr:(KRVar_list_Rule X)
          | (KRTypeList (KRTypeList (KRTypeElem KRElemRule))) => constr:(KRVar_list_list_Rule X)
          | (KRTypeList (KRTypeElem KRElemDefMethT)) => constr:(KRVar_list_DefMethT X)
          | (KRTypeList (KRTypeList (KRTypeElem KRElemDefMethT))) => constr:(KRVar_list_list_DefMethT X)
          | (KRTypeList (KRTypeElem KRElemModuleElt)) => constr:(KRVar_list_ModuleElt X)
          | (KRTypeList (KRTypeList (KRTypeElem KRElemModuleElt))) => constr:(KRVar_list_list_ModuleElt X)
          | (KRTypeElem KRElemBaseModule) => constr:(KRVar_BaseModule X)
          | (KRTypeList (KRTypeElem KRElemBaseModule)) => constr:(KRVar_list_BaseModule X)
          | (KRTypeElem KRElemMod) => constr:(KRVar_Mod X)
          | (KRTypeList (KRTypeElem KRElemMod)) => constr:(KRVar_list_Mod X)
          | (KRTypeElem KRElemString) => constr:(KRVar_string X)
          | (KRTypeList (KRTypeElem KRElemString)) => constr:(KRVar_list_string X)
          | (KRTypeList (KRTypeList (KRTypeElem KRElemString))) => constr:(KRVar_list_list_string X)
          | (KRTypeElem KRElemProp) => constr:(KRVar_Prop X)
          | (KRTypeElem KRElemRegFileBase) => constr:(KRVar_RegFileBase X)
          | (KRTypeList (KRTypeElem KRElemRegFileBase)) => constr:(KRVar_list_RegFileBase X)
          | (KRTypeElem KRElemCallWithSign) => constr:(KRVar_CallWithSign X)
          | (KRTypeList (KRTypeElem KRElemCallWithSign)) => constr:(KRVar_list_CallWithSign X)
          | (KRTypeList (KRTypeList (KRTypeElem KRElemCallWithSign))) => constr:(KRVar_list_list_CallWithSign X)
          | (KRTypeElem KRElemMod_Mod_PairFunc) => constr:(KRVar_Mod_Mod_PairFunc)
          | (KRTypeElem KRElemRegFileBase_list_RegInitT_Func) => constr:(KRVar_RegFileBase_list_RegInitT_Func)
          | (KRTypeElem KRElemRegFileBase_Mod_Func) => constr:(KRVar_RegFileBase_Mod_Func)
          | (KRTypeElem KRElemMod_list_string_Func) => constr:(KRVar_Mod_list_string_Func)
          | (KRTypeElem KRElemMod_list_DefMethT_Func) => constr:(KRVar_Mod_list_DefMethT_Func)
          | (KRTypeElem KRElemRegFileBase_list_DefMethT_Func) => constr:(KRVar_RegFileBase_list_DefMethT_Func)
          | (KRTypeElem KRElemMod_list_Rule_Func) => constr:(KRVar_Mod_list_Rule_Func)
          | (KRTypeElem KRElemMod_list_RegInitT_Func) => constr:(KRVar_Mod_list_RegInitT_Func)
          | (KRTypeElem KRElemRegInitT_string_Func) => constr:(KRVar_RegInitT_string_Func)
          end
  end.

Set Printing Implicit.

Goal forall meth mdev, In meth (concat (map getAllMethods (map (fun m : RegFileBase => Base (BaseRegFile m)) mdev))).
  intros.
  match goal with
  | |- ?X => let r := (ltac:(KRExprReify X (KRTypeElem KRElemProp))) in idtac r
  end.
  match goal with
  | |- In _ (concat (map getAllMethods ?X)) => let r := (ltac:(KRExprReify (map getAllMethods X) (KRTypeList (KRTypeList (KRTypeElem KRElemDefMethT))))) in idtac r
  end.
Abort.

Axiom cheat: forall x, x.

Definition KRSimplifyTop_RegInitT (e : KRExpr_RegInitT) := e.

Definition KRSimplifyTop_RegInitValT (e : KRExpr_RegInitValT) := e.

Definition KRSimplifyTop_Rule (e : KRExpr_Rule) := e.

Definition KRSimplifyTop_ActionVoid (e : KRExpr_ActionVoid) := e.

Definition KRSimplifyTop_MethodT (e : KRExpr_MethodT) := e.

Definition KRSimplifyTop_DefMethT (e : KRExpr_DefMethT) := e.

Definition KRSimplifyTop_ModuleElt (e : KRExpr_ModuleElt) := e.

Definition KRSimplifyTop_list_RegInitT (e : KRExpr_list_RegInitT) : KRExpr_list_RegInitT :=
  match e with
  | KRApp_list_RegInitT f c => match f with
                    | KRCons_list_RegInitT ff rr => KRCons_list_RegInitT ff (KRApp_list_RegInitT rr c)
                    | KRNil_list_RegInitT => c
                    | x => match c with
                           | KRNil_list_RegInitT => f
                           | y => KRApp_list_RegInitT f c
                           end
                               end
  | KRgetAllRegisters (KRBase (KRMakeModule l)) =>
    match l with
    | KRApp_list_ModuleElt a b => KRApp_list_RegInitT (KRgetAllRegisters (KRBase (KRMakeModule a))) (KRgetAllRegisters (KRBase (KRMakeModule b)))
    | KRCons_list_ModuleElt (KRMERegister f) r => KRCons_list_RegInitT f (KRgetAllRegisters (KRBase (KRMakeModule r)))
    | KRCons_list_ModuleElt (KRMERule f) r => KRgetAllRegisters (KRBase (KRMakeModule r))
    | KRCons_list_ModuleElt (KRMEMeth f) r => KRgetAllRegisters (KRBase (KRMakeModule r))
    | KRNil_list_ModuleElt => KRNil_list_RegInitT
    | _ => e
    end
   | KRgetAllRegisters (KRFold_right_Mod KRConcatMod_Func a b) => KRApp_list_RegInitT (KRConcat_RegInitT (KRMap_list_Mod_list_list_RegInitT KRgetAllRegistersFunc b)) (KRgetAllRegisters a)
   | KRgetAllRegisters (KRConcatMod a b) => KRApp_list_RegInitT (KRgetAllRegisters a) (KRgetAllRegisters b)
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
     | KRRegisters r => r
     | KRNil_list_ModuleElt => KRNil_list_RegInitT
     | _ => KRMakeModule_regs x
     end
   | e => e
   end.

Definition KRSimplifyTop_list_list_RegInitT (e : KRExpr_list_list_RegInitT) : KRExpr_list_list_RegInitT :=
  match e with
  | KRApp_list_list_RegInitT f c => match f with
                    | KRCons_list_list_RegInitT ff rr => KRCons_list_list_RegInitT ff (KRApp_list_list_RegInitT rr c)
                    | KRNil_list_list_RegInitT => c
                    | x => match c with
                           | KRNil_list_list_RegInitT => f
                           | y => KRApp_list_list_RegInitT f c
                           end
                                    end
   | e => e
   end.

Definition KRSimplifyTop_list_Rule (e : KRExpr_list_Rule) : KRExpr_list_Rule :=
  match e with
  | KRApp_list_Rule f c => match f with
                    | KRCons_list_Rule ff rr => KRCons_list_Rule ff (KRApp_list_Rule rr c)
                    | KRNil_list_Rule => c
                    | x => match c with
                           | KRNil_list_Rule => f
                           | y => KRApp_list_Rule f c
                           end
                    end
   | KRgetAllRules (KRConcatMod a b) => KRApp_list_Rule (KRgetAllRules a) (KRgetAllRules b)
   | KRgetAllRules (KRFold_right_Mod KRConcatMod_Func a b) => KRApp_list_Rule (KRConcat_Rule (KRMap_list_Mod_list_list_Rule KRgetAllRulesFunc b)) (KRgetAllRules a)
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
     | KRRegisters r => KRNil_list_Rule
     | KRNil_list_ModuleElt => KRNil_list_Rule
     | _ => KRMakeModule_rules x
     end
   | e => e
   end.

Definition KRSimplifyTop_list_list_Rule (e : KRExpr_list_list_Rule) : KRExpr_list_list_Rule :=
  match e with
  | KRApp_list_list_Rule f c => match f with
                    | KRCons_list_list_Rule ff rr => KRCons_list_list_Rule ff (KRApp_list_list_Rule rr c)
                    | KRNil_list_list_Rule => c
                    | x => match c with
                           | KRNil_list_list_Rule => f
                           | y => KRApp_list_list_Rule f c
                           end
                    end
   | e => e
   end.

Definition KRSimplifyTop_list_DefMethT (e : KRExpr_list_DefMethT) : KRExpr_list_DefMethT :=
  match e with
  | KRApp_list_DefMethT f c => match f with
                               | KRCons_list_DefMethT ff rr => KRCons_list_DefMethT ff (KRApp_list_DefMethT rr c)
                               | KRNil_list_DefMethT => c
                               | x => match c with
                                      | KRNil_list_DefMethT => f
                                      | y => KRApp_list_DefMethT f c
                                      end
                               end
   | KRgetAllMethods (KRBase (KRMakeModule l)) =>
    match l with
    | KRApp_list_ModuleElt a b => KRApp_list_DefMethT (KRgetAllMethods (KRBase (KRMakeModule a))) (KRgetAllMethods (KRBase (KRMakeModule b)))
    | KRCons_list_ModuleElt (KRMERegister f) r => KRgetAllMethods (KRBase (KRMakeModule r))
    | KRCons_list_ModuleElt (KRMERule f) r => KRgetAllMethods (KRBase (KRMakeModule r))
    | KRCons_list_ModuleElt (KRMEMeth f) r => (KRCons_list_DefMethT f (KRgetAllMethods (KRBase (KRMakeModule r))))
    | KRNil_list_ModuleElt => KRNil_list_DefMethT
    | KRRegisters _ => KRNil_list_DefMethT
    | _ => e
    end
   | KRgetAllMethods (KRConcatMod a b) => KRApp_list_DefMethT (KRgetAllMethods a) (KRgetAllMethods b)
   | KRgetAllMethods (KRFold_right_Mod KRConcatMod_Func a b) => KRApp_list_DefMethT (KRConcat_DefMethT (KRMap_list_Mod_list_list_DefMethT KRgetAllMethodsFunc b)) (KRgetAllMethods a)
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
     | KRRegisters r => KRNil_list_DefMethT
     | _ => KRMakeModule_meths x
     end
   | e => e
   end.

Definition KRSimplifyTop_list_list_DefMethT (e : KRExpr_list_list_DefMethT) : KRExpr_list_list_DefMethT :=
  match e with
  | KRApp_list_list_DefMethT f c => match f with
                    | KRCons_list_list_DefMethT ff rr => KRCons_list_list_DefMethT ff (KRApp_list_list_DefMethT rr c)
                    | KRNil_list_list_DefMethT => c
                    | x => match c with
                           | KRNil_list_list_DefMethT => f
                           | y => KRApp_list_list_DefMethT f c
                           end
                    end
   | e => e
   end.

Definition KRSimplifyTop_list_ModuleElt (e : KRExpr_list_ModuleElt) : KRExpr_list_ModuleElt :=
  match e with
  | KRApp_list_ModuleElt f c => match f with
                                | KRCons_list_ModuleElt ff rr => KRCons_list_ModuleElt ff (KRApp_list_ModuleElt rr c)
                                | KRNil_list_ModuleElt => c
                                | x => match c with
                                       | KRNil_list_ModuleElt => f
                                       | y => KRApp_list_ModuleElt f c
                                       end
                                end
   | KRRegisters (KRCons_list_RegInitT f r) => (KRCons_list_ModuleElt (KRMERegister f) (KRRegisters r))
   | KRRegisters (KRApp_list_RegInitT f r) => (KRApp_list_ModuleElt (KRRegisters f) (KRRegisters r))
   | KRRegisters (KRNil_list_RegInitT) => KRNil_list_ModuleElt
   | e => e
   end.

Definition KRSimplifyTop_list_list_ModuleElt (e : KRExpr_list_list_ModuleElt) : KRExpr_list_list_ModuleElt :=
  match e with
  | KRApp_list_list_ModuleElt f c => match f with
                                     | KRCons_list_list_ModuleElt ff rr => KRCons_list_list_ModuleElt ff (KRApp_list_list_ModuleElt rr c)
                                     | KRNil_list_list_ModuleElt => c
                                     | x => match c with
                                            | KRNil_list_list_ModuleElt => f
                                            | y => KRApp_list_list_ModuleElt f c
                                            end
                                     end
   | e => e
   end.

Fixpoint sappend (s1 s2 : string) : string :=
  match s1 with
  | EmptyString => s2
  | String c s1' => String c (sappend s1' s2)
  end.

Fixpoint srev (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | (String f r) => sappend (srev r) (String f EmptyString)
  end.

Theorem sappendEmpty: forall s, sappend s ""=s.
Proof.
  intros.
  induction s.
  - reflexivity.
  - simpl.
    rewrite IHs.
    reflexivity.
Qed.

Theorem sappendNotEmpty: forall s c s', sappend s (String c s')<>"".
Proof.
  intros.
  induction s.
  - simpl.
    intro X.
    inversion X.
  - simpl.
    intro X.
    inversion X.
Qed.

Theorem sappendNotEmpty': forall s c s', sappend s (String c s') =? ""=false.
Proof.
  intros.
  induction s.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
Qed.

Theorem sappend_String_assoc: forall s c s', sappend s (String c s')=sappend (sappend s (String c "")) s'.
Proof.
  intro s.
  induction s.
  - simpl.
    reflexivity.
  - intros.
    simpl.
    f_equal.
    rewrite IHs.
    reflexivity.
Qed.

(*Theorem sappend_eq: forall a s b, ((sappend a s) =? (sappend b s))= (a =? b).
Proof.
  intro a.
  induction a.
  - intros.
    destruct b.
    + simpl.
      rewrite String.eqb_refl.
      reflexivity.
    +
    intros.
    rewrite ?sappendEmpty.
    reflexivity.
  - intros.
    destruct b.
    + simpl.
      rewrite sappend_String_assoc.
      rewrite IHs.
      rewrite String.eqb_refl.
      reflexivity.
    +
  -*)

Theorem sappend_empty_eq: forall a s, (sappend s a  =? a) = (s =? "").
Proof.
  intro a.
  induction a.
  - simpl.
    intros.
    rewrite sappendEmpty.
    reflexivity.
  - intros.
    rewrite sappend_String_assoc.
    destruct s.
    + simpl.
      rewrite ?String.eqb_refl.
      rewrite Ascii.eqb_refl.
      reflexivity.
    + simpl.
      remember (a1 =? a)%char.
      destruct b.
      * rewrite IHa.
        simpl.
        destruct s.
        -- reflexivity.
        -- reflexivity.
      * reflexivity.
Qed.

Theorem sappend_empty_equal: forall a s, (sappend s a=a) <-> (s="").
Proof.
  intros.
  split.
  - intros.
    rewrite <- String.eqb_eq in H.
    rewrite sappend_empty_eq in H.
    rewrite String.eqb_eq in H.
    apply H.
  - intros.
    subst.
    reflexivity.
Qed.

Theorem sappend_assoc: forall a b c, sappend a (sappend b c)=sappend (sappend a b) c.
Proof.
  intro a.
  induction a.
  - simpl.
    reflexivity.
  - intros.
    simpl.
    rewrite IHa.
    reflexivity.
Qed.

Theorem sappend_eq_reduce: forall a s b, (sappend a s =? sappend b s)=(a =? b).
Proof.
  intro a.
  induction a.
  - intros.
    simpl.
    destruct b.
    + simpl.
      rewrite String.eqb_refl.
      reflexivity.
    + rewrite String.eqb_sym.
      rewrite sappend_empty_eq.
      simpl.
      reflexivity.
  - intros.
    destruct b.
    + simpl.
      destruct s.
      * reflexivity.
      * remember (a =? a1)%char.
        destruct b.
        -- rewrite sappend_String_assoc.
           rewrite sappend_empty_eq.
           destruct a0.
           ** reflexivity.
           ** reflexivity.
        -- reflexivity.
    + simpl.
      remember (a =? a1)%char.
      destruct b0.
      * rewrite IHa.
        reflexivity.
      * reflexivity.
Qed.

Theorem sappend_tail_diff: forall s1 a b s2, ((a =? b)%char = false) -> ((sappend s1 (String a "") =? sappend s2 (String b ""))=false).
Proof.
  intro s1.
  induction s1.
  - intros.
    simpl.
    destruct s2.
    + simpl.
      rewrite H.
      reflexivity.
    + simpl.
      destruct (a =? a0)%char.
      * destruct s2.
        -- reflexivity.
        -- reflexivity.
      * reflexivity.
  - intros.
    destruct s2.
    + simpl.
      remember (a =? b)%char.
      destruct b0.
      * destruct s1.
        ++ reflexivity.
        ++ reflexivity.
      * reflexivity.
    + simpl.
      remember (a =? a1)%char.
      destruct b0.
      * apply IHs1.
        apply H.
      * reflexivity.
Qed.

Theorem srev_eqb_gen: forall s1 s2 a,
    String.eqb (sappend s1 a) (sappend s2 a)=String.eqb (sappend (srev s1) a) (sappend (srev s2) a).
Proof.
  intros s1.
  induction s1.
  - intros.
    simpl.
    rewrite String.eqb_sym.
    rewrite sappend_empty_eq.
    assert (forall a b c, (a =? sappend b c)=(sappend b c =? a)).
    intros. rewrite String.eqb_sym. reflexivity.
    rewrite H.
    rewrite sappend_empty_eq.
    destruct s2.
    + reflexivity.
    + simpl.
      destruct (srev s2).
      * simpl.
        reflexivity.
      * simpl. reflexivity.
  - intros.
    destruct s2.
    + simpl.
      destruct a0.
      * simpl.
        rewrite sappendEmpty.
        rewrite sappendNotEmpty'.
        reflexivity.
      * remember (a=?a0)%char.
        destruct b.
        ++ rewrite sappend_empty_eq.
           rewrite sappend_String_assoc.
           rewrite sappend_empty_eq.
           rewrite ?sappendNotEmpty'.
           reflexivity.
        ++ rewrite sappend_empty_eq.
           rewrite sappendNotEmpty'.
           reflexivity.
    + simpl.
      remember (a=?a1)%char.
      destruct b.
      * rewrite <- sappend_assoc.
        rewrite <- sappend_assoc.
        remember (a=?a1)%char.
        destruct b.
        ++ symmetry in Heqb0.
           rewrite Ascii.eqb_eq in Heqb0.
           subst.
           rewrite <- IHs1.
           rewrite ?sappend_eq_reduce.
           reflexivity.
        ++ inversion Heqb.
      * rewrite sappend_eq_reduce.
        symmetry.
        apply sappend_tail_diff.
        rewrite <- Heqb.
        reflexivity.
Qed.

Theorem srev_eqb : forall s1 s2, String.eqb s1 s2=String.eqb (srev s1) (srev s2).
Proof.
  intros.
  erewrite <- sappend_eq_reduce.
  instantiate (1 := "").
  assert ((srev s1 =? srev s2) = (sappend (srev s1) "" =? sappend (srev s2) "")).
      rewrite sappend_eq_reduce.
      reflexivity.
  rewrite H.
  apply srev_eqb_gen.
Qed.

Fixpoint sdisjPrefix (s1: string) (s2: string) :=
  match s1,s2 with
  | (String c1 s1'),(String c2 s2') => if (c1 =? c2)%char then sdisjPrefix s1' s2' else true
  | _,_ => false
  end.

(*Goal sdisjPrefix (srev "_mode") (srev "_int_data_reg")=true.
  simpl.*)

Theorem srev_sappend: forall a b, srev (sappend a b)=sappend (srev b) (srev a).
Proof.
  intro a.
  induction a.
  - simpl.
    intros.
    rewrite sappendEmpty.
    reflexivity.
  - intros.
    simpl.
    rewrite IHa.
    rewrite sappend_assoc.
    reflexivity.
Qed.

Theorem String_same_false: forall b a, String a b=b -> False.
Proof.
  intro b.
  induction b.
  - simpl.
    intros.
    inversion H.
  - intros.
    remember (Ascii.eqb a a0) in H.
    destruct b0.
    + symmetry in Heqb0.
      rewrite Ascii.eqb_eq in Heqb0.
      subst.
      inversion H; subst; clear H.
      apply IHb in H1.
      inversion H1.
    + symmetry in Heqb0.
      apply Ascii.eqb_neq in Heqb0.
      inversion H;subst;clear H.
      apply Heqb0.
      reflexivity.
Qed.

Theorem sappend_String_equal: forall a b c, sappend a (String c "")=sappend b (String c "") -> a = b.
Proof.
  intro a.
  induction a.
  - intros.
    destruct b.
    + reflexivity.
    + simpl in H.
      inversion H; subst; clear H.
      destruct b.
      * inversion H2.
      * inversion H2.
  - intros.
    destruct b.
    + simpl in H.
      inversion H; subst; clear H.
      destruct a0.
      * inversion H2.
      * inversion H2.
    + simpl in H.
      inversion H; subst; clear H.
      f_equal.
      eapply IHa.
      apply H2.
Qed.

Theorem sappend_equal_tail: forall c b a, a=b <-> sappend a c=sappend b c.
Proof.
  split.
  - intros.
    subst.
    reflexivity.
  - generalize a.
    generalize b.
    induction c.
    + simpl.
      intros.
      rewrite sappendEmpty in H.
      rewrite sappendEmpty in H.
      subst.
      reflexivity.
    + simpl.
      intros.
      rewrite sappend_String_assoc in H.
      assert (sappend b0 (String a0 c)=(sappend (sappend b0 (String a0 "")) c)).
        rewrite <- sappend_String_assoc.
        reflexivity.
      rewrite H0 in H.
      apply IHc in H.
      apply sappend_String_equal in H.
      apply H.
Qed.

Theorem sappend_different_last: forall a b c d, sappend a (String b "")=sappend c (String d "") -> b<>d -> False.
Proof.
  intro a.
  induction a.
  - intros.
    simpl in H.
    destruct c.
    + simpl in H.
      inversion H; subst; clear H.
      apply H0.
      reflexivity.
    + simpl in H.
      inversion H; subst; clear H.
      destruct c.
      * inversion H3.
      * inversion H3.
  - intros.
    simpl in H.
    destruct c.
    + simpl in H.
      inversion H.
      destruct a0.
      * inversion H3.
      * inversion H3.
    + simpl in H.
      inversion H; subst; clear H.
      eapply IHa.
      apply H3.
      apply H0.
Qed.

Theorem equal_srev_sappend: forall a b c, a=b <-> sappend (srev a) c=sappend (srev b) c.
Proof.
  intro a.
  induction a.
  - simpl.
    intros.
    destruct b.
    + simpl.
      split.
      * reflexivity.
      * reflexivity.
    + simpl.
      split.
      * intros.
        inversion H.
      * intros.
        remember (srev b).
        destruct s.
        -- simpl in H.
           symmetry in H.
           apply String_same_false in H.
           inversion H.
        -- symmetry in H.
           rewrite sappend_empty_equal in H.
           inversion H.
  - split.
    + intros.
      subst.
      reflexivity.
    + intros.
      destruct b.
      * simpl in H.
        rewrite sappend_empty_equal in H.
        remember (srev a0).
        destruct s.
        -- inversion H.
        -- inversion H.
      * simpl in H.
        rewrite <- sappend_assoc in H.
        rewrite <- sappend_assoc in H.
        remember (Ascii.eqb a a1).
        destruct b0.
        -- symmetry in Heqb0.
           apply Ascii.eqb_eq in Heqb0.
           subst.
           apply <- IHa in H.
           subst.
           reflexivity.
        -- symmetry in Heqb0.
           apply Ascii.eqb_neq in Heqb0.
           rewrite sappend_assoc in H.
           rewrite sappend_assoc in H.
           apply sappend_equal_tail in H.
           apply sappend_different_last in H.
           ++ inversion H.
           ++ apply Heqb0.
Qed.

Theorem equal_srev: forall a b, a=b <-> srev a=srev b.
Proof.
  intros.
  split.
  - intros.
    subst.
    reflexivity.
  - intros.
    assert (sappend (srev a) ""=sappend (srev b) "").
    + rewrite H.
      reflexivity.
    + apply <- equal_srev_sappend in H0.
      apply H0.
Qed.

Theorem sdisjPrefix_sappend_not_equal: forall s1 s2 p1 p2,
    sdisjPrefix s1 s2=true -> (sappend s1 p1=sappend s2 p2)%string -> False.
Proof.
  intro s1.
  induction s1.
  - intros.
    inversion H.
  - destruct s2.
    + intros.
      inversion H.
    + intros.
      simpl in H.
      remember (Ascii.eqb a a0).
      destruct b.
      * symmetry in Heqb.
        rewrite Ascii.eqb_eq in Heqb.
        subst.
        simpl.
        simpl in H0.
        inversion H0; subst; clear H0.
        eapply IHs1.
        ++ apply H.
        ++ apply H2.
      * inversion H0; subst; clear H0.
        symmetry in Heqb.
        rewrite Ascii.eqb_neq in Heqb.
        apply Heqb.
        reflexivity.
Qed.

Theorem sdisjPrefix_sappend_false: forall p1 p2 s1 s2,
    sdisjPrefix (srev s1) (srev s2)=true -> sappend p1 s1=sappend p2 s2 -> False.
Proof.
  intros.
  eapply sdisjPrefix_sappend_not_equal in H.
  - inversion H.
  - instantiate (1 := (srev p2)).
    instantiate (1 := (srev p1)).
    rewrite <- srev_sappend.
    rewrite <- srev_sappend.
    rewrite H0.
    reflexivity.
Qed.

Theorem sappend_append: forall s1 s2, sappend s1 s2=String.append s1 s2.
Proof.
  intros.
  induction s1.
  - reflexivity.
  - simpl.
    rewrite IHs1.
    reflexivity.
Qed.

Theorem sdisjPrefix_false': forall p1 p2 s1 s2,
    sdisjPrefix (srev s1) (srev s2)=true -> (p1++s1=p2++s2)%string -> False.
Proof.
  intros p1 p2 s1 s2.
  repeat (rewrite <- sappend_append).
  assert ((p2++s2)%string=sappend p2 s2).
  - rewrite <- sappend_append.
    reflexivity.
  - rewrite H.
    intros.
    eapply sdisjPrefix_sappend_false.
    + apply H0.
    + apply H1.
Qed.

Theorem sdisjPrefix_false: forall p1 p2 s1 s2,
    sdisjPrefix (srev s1) (srev s2)=true -> False=(p1++s1=p2++s2)%string.
Admitted.

Hint Rewrite sappend_append : kami_rewrite_db.
    
Definition KRSimplifyTop_string (e: KRExpr_string) : KRExpr_string :=
  match e with
  | KRstring_append (KRConst_string a) (KRConst_string b) => KRConst_string ((sappend a b)%string)
  | KRfst_RegInitT_string (KRPair_RegInitT s v) => s
  | KRfst_DefMethT_string (KRPair_DefMethT s v) => s
  | KRfst_Rule_string (KRPair_Rule s v) => s
  | x => x
  end.

Definition KRSimplifyTop_list_string (e: KRExpr_list_string) : KRExpr_list_string :=
  match e with
  | KRApp_list_string f c => match f with
                             | KRCons_list_string ff rr => KRCons_list_string ff (KRApp_list_string rr c)
                             | KRNil_list_string => c
                             | x => match c with
                                    | KRNil_list_string => f
                                    | y => KRApp_list_string f c
                                    end
                             end
  | KRgetCallsPerMod (KRConcatMod a b) => KRApp_list_string (KRgetCallsPerMod a) (KRgetCallsPerMod b)
  | KRgetCallsPerMod (KRBase (KRBaseRegFile m)) => KRNil_list_string
  | KRmap_RegInitT_string f (KRApp_list_RegInitT a b) =>
    KRApp_list_string (KRmap_RegInitT_string f a) (KRmap_RegInitT_string f b)
  | KRmap_RegInitT_string KRfst_RegInitT_string_Func (KRCons_list_RegInitT f r) =>
    KRCons_list_string (KRfst_RegInitT_string f) (KRmap_RegInitT_string KRfst_RegInitT_string_Func r)
  | KRmap_DefMethT_string f (KRApp_list_DefMethT a b) =>
    KRApp_list_string (KRmap_DefMethT_string f a) (KRmap_DefMethT_string f b)
  | KRmap_DefMethT_string KRfst_DefMethT_string_Func (KRCons_list_DefMethT f r) =>
    KRCons_list_string (KRfst_DefMethT_string f) (KRmap_DefMethT_string KRfst_DefMethT_string_Func r)
  | KRmap_Rule_string f (KRApp_list_Rule a b) =>
    KRApp_list_string (KRmap_Rule_string f a) (KRmap_Rule_string f b)
  | KRmap_Rule_string KRfst_Rule_string_Func (KRCons_list_Rule f r) =>
    KRCons_list_string (KRfst_Rule_string f) (KRmap_Rule_string KRfst_Rule_string_Func r)
  | e => e
  end.

Definition KRSimplifyTop_list_list_string (e: KRExpr_list_list_string) : KRExpr_list_list_string :=
  match e with
  | KRApp_list_list_string f c => match f with
                                  | KRCons_list_list_string ff rr => KRCons_list_list_string ff (KRApp_list_list_string rr c)
                                  | KRNil_list_list_string => c
                                  | x => match c with
                                         | KRNil_list_list_string => f
                                         | y => KRApp_list_list_string f c
                                         end 
                                  end
   | e => e
   end.

Definition KRSimplifyTop_Prop (e: KRExpr_Prop) : KRExpr_Prop :=
  match e with
  | KRDisjKey_RegInitT a b => match a with
                              | KRApp_list_RegInitT x y => KRAnd_Prop (KRDisjKey_RegInitT x b) (KRDisjKey_RegInitT y b)
                              | KRCons_list_RegInitT x y => KRAnd_Prop (KRNot_Prop (KRIn_string_Prop (KRfst_RegInitT_string x) (KRmap_RegInitT_string KRfst_RegInitT_string_Func b))) (KRDisjKey_RegInitT y b)
                              | KRNil_list_RegInitT => KRTrue_Prop
                              | _ => match b with
                                     | KRApp_list_RegInitT x y => KRAnd_Prop (KRDisjKey_RegInitT a x) (KRDisjKey_RegInitT a y)
                                     | KRCons_list_RegInitT x y => KRAnd_Prop (KRNot_Prop (KRIn_string_Prop (KRfst_RegInitT_string x) (KRmap_RegInitT_string KRfst_RegInitT_string_Func a))) (KRDisjKey_RegInitT a y)
                                     | KRNil_list_RegInitT => KRTrue_Prop
                                     | _ => KRDisjKey_RegInitT a b
                                     end
                              end
  | KRDisjKey_DefMethT a b => match a with
                              | KRApp_list_DefMethT x y => KRAnd_Prop (KRDisjKey_DefMethT x b) (KRDisjKey_DefMethT y b)
                              | KRCons_list_DefMethT x y => KRAnd_Prop (KRNot_Prop (KRIn_string_Prop (KRfst_DefMethT_string x) (KRmap_DefMethT_string KRfst_DefMethT_string_Func b))) (KRDisjKey_DefMethT y b)
                              | KRNil_list_DefMethT => KRTrue_Prop
                              | _ => match b with
                                     | KRApp_list_DefMethT x y => KRAnd_Prop (KRDisjKey_DefMethT a x) (KRDisjKey_DefMethT a y)
                                     | KRCons_list_DefMethT x y => KRAnd_Prop (KRNot_Prop (KRIn_string_Prop (KRfst_DefMethT_string x) (KRmap_DefMethT_string KRfst_DefMethT_string_Func a))) (KRDisjKey_DefMethT a y)
                                     | KRNil_list_DefMethT => KRTrue_Prop
                                     | _ => KRDisjKey_DefMethT a b
                                     end
                              end
  | KRDisjKey_Rule a b => match a with
                          | KRApp_list_Rule x y => KRAnd_Prop (KRDisjKey_Rule x b) (KRDisjKey_Rule y b)
                          | KRCons_list_Rule x y => KRAnd_Prop (KRNot_Prop (KRIn_string_Prop (KRfst_Rule_string x) (KRmap_Rule_string KRfst_Rule_string_Func b))) (KRDisjKey_Rule y b)
                          | KRNil_list_Rule => KRTrue_Prop
                          | _ => match b with
                                 | KRApp_list_Rule x y => KRAnd_Prop (KRDisjKey_Rule a x) (KRDisjKey_Rule a y)
                                 | KRCons_list_Rule x y => KRAnd_Prop (KRNot_Prop (KRIn_string_Prop (KRfst_Rule_string x) (KRmap_Rule_string KRfst_Rule_string_Func a))) (KRDisjKey_Rule a y)
                                 | KRNil_list_Rule => KRTrue_Prop
                                 | _ => KRDisjKey_Rule a b
                                 end
                          end
  | KRAnd_Prop a KRTrue_Prop => a
  | KRAnd_Prop a KRFalse_Prop => KRFalse_Prop
  | KRAnd_Prop KRTrue_Prop a => a
  | KRAnd_Prop KRFalse_Prop a => KRFalse_Prop
  | KROr_Prop a KRTrue_Prop => KRTrue_Prop
  | KROr_Prop a KRFalse_Prop => a
  | KROr_Prop KRTrue_Prop a => KRTrue_Prop
  | KROr_Prop KRFalse_Prop a => a
  | KRNot_Prop (KRTrue_Prop) => KRFalse_Prop
  | KRNot_Prop (KRFalse_Prop) => KRTrue_Prop
  | KRNot_Prop (KRNot_Prop a) => a
  | KRNot_Prop (KRAnd_Prop a b) => (KROr_Prop (KRNot_Prop a) (KRNot_Prop b))
  | KRNot_Prop (KROr_Prop a b) => (KRAnd_Prop (KRNot_Prop a) (KRNot_Prop b))
  | KRIn_string_Prop x (KRApp_list_string a b) => (KROr_Prop (KRIn_string_Prop x a) (KRIn_string_Prop x b))
  | KRIn_string_Prop x (KRCons_list_string a b) => (KROr_Prop (KREq_string_Prop x a) (KRIn_string_Prop x b))
  | KRIn_string_Prop x (KRNil_list_string) => KRFalse_Prop
  | KRIn_RegInitT_Prop x (KRApp_list_RegInitT a b) => (KROr_Prop (KRIn_RegInitT_Prop x a) (KRIn_RegInitT_Prop x b))
  | KRIn_RegInitT_Prop x (KRCons_list_RegInitT a b) => (KROr_Prop (KREq_RegInitT_Prop x a) (KRIn_RegInitT_Prop x b))
  | KRIn_RegInitT_Prop x (KRNil_list_RegInitT) => KRFalse_Prop
  | KRIn_Rule_Prop x (KRApp_list_Rule a b) => (KROr_Prop (KRIn_Rule_Prop x a) (KRIn_Rule_Prop x b))
  | KRIn_Rule_Prop x (KRCons_list_Rule a b) => (KROr_Prop (KREq_Rule_Prop x a) (KRIn_Rule_Prop x b))
  | KRIn_Rule_Prop x (KRNil_list_Rule) => KRFalse_Prop
  | KRIn_DefMethT_Prop x (KRApp_list_DefMethT a b) => (KROr_Prop (KRIn_DefMethT_Prop x a) (KRIn_DefMethT_Prop x b))
  | KRIn_DefMethT_Prop x (KRCons_list_DefMethT a b) => (KROr_Prop (KREq_DefMethT_Prop x a) (KRIn_DefMethT_Prop x b))
  | KRIn_DefMethT_Prop x (KRNil_list_DefMethT) => KRFalse_Prop
  | KREq_string_Prop (KRstring_append p (KRConst_string a)) (KRstring_append q (KRConst_string b)) => if sdisjPrefix (srev a) (srev b) then KRFalse_Prop else e
  (*| KREq_string_Prop (KRstring_append (KRVar_string p) a) (KRstring_append (KRVar_string q) b) => if String.eqb p q then (KREq_string_Prop a b) else KREq_string_Prop (KRstring_append (KRVar_string p) a) (KRstring_append (KRVar_string q) b)
  | KREq_string_Prop (KRVar_string a) (KRVar_string b) => if String.eqb a b then KRTrue_Prop else
                                                            (KREq_string_Prop (KRVar_string a) (KRVar_string b))*)
  | e => e
  end.

Definition KRSimplifyTop_RegFileBase (e: KRExpr_RegFileBase) : KRExpr_RegFileBase := e.

Definition KRSimplifyTop_list_RegFileBase (e: KRExpr_list_RegFileBase) : KRExpr_list_RegFileBase :=
  match e with
  | KRApp_list_RegFileBase f c => match f with
                                  | KRCons_list_RegFileBase ff rr => KRCons_list_RegFileBase ff (KRApp_list_RegFileBase rr c)
                                  | KRNil_list_RegFileBase => c
                                  | x => match c with
                                         | KRNil_list_RegFileBase => f
                                         | y => KRApp_list_RegFileBase f c
                                         end
                                  end
   | e => e
   end.

Definition KRSimplifyTop_CallWithSign (e: KRExpr_CallWithSign) : KRExpr_CallWithSign := e.

Definition KRSimplifyTop_list_CallWithSign (e: KRExpr_list_CallWithSign) : KRExpr_list_CallWithSign :=
  match e with
  | KRApp_list_CallWithSign f c => match f with
                                  | KRCons_list_CallWithSign ff rr => KRCons_list_CallWithSign ff (KRApp_list_CallWithSign rr c)
                                  | KRNil_list_CallWithSign => c
                                  | x => match c with
                                         | KRNil_list_CallWithSign => f
                                         | y => KRApp_list_CallWithSign f c
                                         end
                                  end
   | e => e
   end.

Definition KRSimplifyTop_list_list_CallWithSign (e: KRExpr_list_list_CallWithSign) : KRExpr_list_list_CallWithSign :=
  match e with
  | KRApp_list_list_CallWithSign f c => match f with
                                        | KRCons_list_list_CallWithSign ff rr => KRCons_list_list_CallWithSign ff (KRApp_list_list_CallWithSign rr c)
                                        | KRNil_list_list_CallWithSign => c
                                        | x => match c with
                                               | KRNil_list_list_CallWithSign => f
                                               | y => KRApp_list_list_CallWithSign f c
                                               end
                                        end
   | e => e
   end.

Definition KRSimplifyTop_Mod_Mod_PairFunc(f: KRExpr_Mod_Mod_PairFunc) := f.

Definition KRSimplifyTop_RegFileBase_list_RegInitT_Func(f: KRExpr_RegFileBase_list_RegInitT_Func) := f.

Definition KRSimplifyTop_RegFileBase_list_DefMethT_Func(f: KRExpr_RegFileBase_list_DefMethT_Func) := f.

Definition KRSimplifyTop_Mod_list_string_Func(f: KRExpr_Mod_list_string_Func) := f.

Definition KRSimlpifyTop_RegFileBase_Mod_Func(f: KRExpr_RegFileBase_Mod_Func) := f.

Definition KRSimplifyTop_Mod_list_DefMethT_Func(f: KRExpr_Mod_list_DefMethT_Func) := f.

Definition KRSimplifyTop_Mod_list_Rule_Func(f:KRExpr_Mod_list_Rule_Func) := f.

Definition KRSimplifyTop_Mod_list_RegInitT_Func(f:KRExpr_Mod_list_RegInitT_Func) := f.

Definition KRSimplifyTop_BaseModule (e : KRExpr_BaseModule) := e.

Definition KRSimplifyTop_Mod (e : KRExpr_Mod) := e.

Definition KRSimplifyTop_list_Mod (e: KRExpr_list_Mod) : KRExpr_list_Mod :=
  match e with
  | KRApp_list_Mod f c => match f with
                          | KRCons_list_Mod ff rr => KRCons_list_Mod ff (KRApp_list_Mod rr c)
                          | KRNil_list_Mod => c
                          | x => match c with
                                 | KRNil_list_Mod => f
                                 | y => KRApp_list_Mod f c
                                 end
                          end
   | e => e
   end.

Fixpoint KRSimplify_RegInitT (e : KRExpr_RegInitT) : KRExpr_RegInitT :=
  KRSimplifyTop_RegInitT (match e with
                          | KRPair_RegInitT f s => KRPair_RegInitT (KRSimplify_string f) (KRSimplify_RegInitValT s)
                          | _ => e
                          end)
                         
with KRSimplify_RegInitValT (e : KRExpr_RegInitValT) : KRExpr_RegInitValT := KRSimplifyTop_RegInitValT e

with KRSimplify_Rule (e : KRExpr_Rule) : KRExpr_Rule := KRSimplifyTop_Rule e

with KRSimplify_DefMethT (e : KRExpr_DefMethT) : KRExpr_DefMethT := KRSimplifyTop_DefMethT e

with KRSimplify_ModuleElt (e : KRExpr_ModuleElt) : KRExpr_ModuleElt :=
     KRSimplifyTop_ModuleElt (match e with
                              | KRMERegister r => KRMERegister (KRSimplify_RegInitT r)
                              | KRMERule r => KRMERule (KRSimplify_Rule r)
                              | KRMEMeth m => KRMEMeth (KRSimplify_DefMethT m)
                              | e => e
                              end)
                             
with KRSimplify_list_RegInitT (e : KRExpr_list_RegInitT) : KRExpr_list_RegInitT :=
       KRSimplifyTop_list_RegInitT (match e with
                                    | KRCons_list_RegInitT f r =>
                                      KRCons_list_RegInitT (KRSimplify_RegInitT f) (KRSimplify_list_RegInitT r)
                                    | KRApp_list_RegInitT f r =>
                                      KRApp_list_RegInitT (KRSimplify_list_RegInitT f) (KRSimplify_list_RegInitT r)
                                    | KRgetRegisters m => KRgetRegisters (KRSimplify_BaseModule m)
                                    | KRgetAllRegisters m => KRgetAllRegisters (KRSimplify_Mod m)
                                    | KRMakeModule_regs r => KRMakeModule_regs (KRSimplify_list_ModuleElt r)
                                    | KRConcat_RegInitT r => KRConcat_RegInitT (KRSimplify_list_list_RegInitT r)
                                    | e => e
                                   end)
  
with KRSimplify_RegFileBase_list_RegInitT_Func (f: KRExpr_RegFileBase_list_RegInitT_Func) := f

with KRSimplify_list_list_RegInitT (e: KRExpr_list_list_RegInitT) : KRExpr_list_list_RegInitT :=
       KRSimplifyTop_list_list_RegInitT (match e with
                                         | KRCons_list_list_RegInitT f r =>
                                           KRCons_list_list_RegInitT (KRSimplify_list_RegInitT f) (KRSimplify_list_list_RegInitT r)
                                         | KRApp_list_list_RegInitT f r =>
                                      KRApp_list_list_RegInitT (KRSimplify_list_list_RegInitT f) (KRSimplify_list_list_RegInitT r)
                                         | KRMap_list_Mod_list_list_RegInitT f l => KRMap_list_Mod_list_list_RegInitT (KRSimplify_Mod_list_RegInitT_Func f) (KRSimplify_list_Mod l)
                                         | KRMap_list_RegFileBase_list_list_RegInitT f l => KRMap_list_RegFileBase_list_list_RegInitT (KRSimplify_RegFileBase_list_RegInitT_Func f) (KRSimplify_list_RegFileBase l)
                                         | e => e
                                         end)
  
with KRSimplify_Mod_list_RegInitT_Func (f: KRExpr_Mod_list_RegInitT_Func) := f

with KRSimplify_list_Rule (e: KRExpr_list_Rule) : KRExpr_list_Rule :=
       KRSimplifyTop_list_Rule (match e with
                                | KRCons_list_Rule f r =>
                                  KRCons_list_Rule (KRSimplify_Rule f) (KRSimplify_list_Rule r)
                                | KRApp_list_Rule f r =>
                                  KRApp_list_Rule (KRSimplify_list_Rule f) (KRSimplify_list_Rule r)
                                | KRgetRules m => KRgetRules (KRSimplify_BaseModule m)
                                | KRgetAllRules m => KRgetAllRules (KRSimplify_Mod m)
                                | KRMakeModule_rules r => KRMakeModule_rules (KRSimplify_list_ModuleElt r)
                                | KRConcat_Rule r => KRConcat_Rule (KRSimplify_list_list_Rule r)
                                | e => e
                               end)

with KRSimplify_Mod_list_Rule_Func(f: KRExpr_Mod_list_Rule_Func) := f

with KRSimplify_list_list_Rule (e: KRExpr_list_list_Rule) : KRExpr_list_list_Rule :=
       KRSimplifyTop_list_list_Rule (match e with
                                | KRCons_list_list_Rule f r =>
                                  KRCons_list_list_Rule (KRSimplify_list_Rule f) (KRSimplify_list_list_Rule r)
                                | KRApp_list_list_Rule f r =>
                                  KRApp_list_list_Rule (KRSimplify_list_list_Rule f) (KRSimplify_list_list_Rule r)
                                | KRMap_list_Mod_list_list_Rule f l =>  KRMap_list_Mod_list_list_Rule (KRSimplify_Mod_list_Rule_Func f) (KRSimplify_list_Mod l)
                                | e => e
                               end)

with KRSimplify_list_DefMethT (e: KRExpr_list_DefMethT) : KRExpr_list_DefMethT :=
       KRSimplifyTop_list_DefMethT (match e with
                                    | KRCons_list_DefMethT f r =>
                                      KRCons_list_DefMethT (KRSimplify_DefMethT f) (KRSimplify_list_DefMethT r)
                                    | KRApp_list_DefMethT f r =>
                                      KRApp_list_DefMethT (KRSimplify_list_DefMethT f) (KRSimplify_list_DefMethT r)
                                    | KRConcat_DefMethT r => KRConcat_DefMethT (KRSimplify_list_list_DefMethT r)
                                    | KRgetMethods m => KRgetMethods (KRSimplify_BaseModule m)
                                    | KRgetAllMethods m => KRgetAllMethods (KRSimplify_Mod m)
                                    | KRMakeModule_meths r => KRMakeModule_meths (KRSimplify_list_ModuleElt r)
                                    | e => e
                                    end)

with KRSimplify_list_list_DefMethT (e: KRExpr_list_list_DefMethT) : KRExpr_list_list_DefMethT :=
       KRSimplifyTop_list_list_DefMethT (match e with
                                    | KRCons_list_list_DefMethT f r =>
                                      KRCons_list_list_DefMethT (KRSimplify_list_DefMethT f) (KRSimplify_list_list_DefMethT r)
                                    | KRApp_list_list_DefMethT f r =>
                                      KRApp_list_list_DefMethT (KRSimplify_list_list_DefMethT f) (KRSimplify_list_list_DefMethT r)
                                    | KRMap_list_Mod_list_list_DefMethT f l => KRMap_list_Mod_list_list_DefMethT (KRSimplify_Mod_list_DefMethT_Func f) (KRSimplify_list_Mod l)
                                    | KRMap_list_RegFileBase_list_list_DefMethT f l => KRMap_list_RegFileBase_list_list_DefMethT (KRSimplify_RegFileBase_list_DefMethT_Func f) (KRSimplify_list_RegFileBase l)
                                    | e => e
                                    end)

with KRSimplify_Mod_list_DefMethT_Func(f: KRExpr_Mod_list_DefMethT_Func) := f

with KRSimplify_RegFileBase_list_DefMethT_Func(f: KRExpr_RegFileBase_list_DefMethT_Func) := f

with KRSimplify_CallWithSign(c: KRExpr_CallWithSign) := c

with KRSimplify_list_CallWithSign(e: KRExpr_list_CallWithSign) :=
       KRSimplifyTop_list_CallWithSign (match e with
                                        | KRCons_list_CallWithSign f r =>
                                          KRCons_list_CallWithSign (KRSimplify_CallWithSign f) (KRSimplify_list_CallWithSign r)
                                        | KRApp_list_CallWithSign f r =>
                                          KRApp_list_CallWithSign (KRSimplify_list_CallWithSign f) (KRSimplify_list_CallWithSign r)
                                        | KRConcat_CallWithSign l => KRConcat_CallWithSign (KRSimplify_list_list_CallWithSign l)
                                        | e => e
                                        end)

with KRSimplify_list_list_CallWithSign(e: KRExpr_list_list_CallWithSign) :=
       KRSimplifyTop_list_list_CallWithSign (match e with
                                             | KRCons_list_list_CallWithSign f r =>
                                               KRCons_list_list_CallWithSign (KRSimplify_list_CallWithSign f) (KRSimplify_list_list_CallWithSign r)
                                             | KRApp_list_list_CallWithSign f r =>
                                               KRApp_list_list_CallWithSign (KRSimplify_list_list_CallWithSign f) (KRSimplify_list_list_CallWithSign r)
                                             | e => e
                                             end)

with KRSimplify_Mod_list_string_Func(f: KRExpr_Mod_list_string_Func) := f

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
          | KRBaseRegFile b => KRBaseRegFile (KRSimplify_RegFileBase b)
          | e => e
          end)

with KRSimplify_RegFileBase(m: KRExpr_RegFileBase) := m
    
with KRSimplify_list_RegFileBase(e: KRExpr_list_RegFileBase) :=
       KRSimplifyTop_list_RegFileBase (match e with
                                      | KRCons_list_RegFileBase f r =>
                                        KRCons_list_RegFileBase (KRSimplify_RegFileBase f) (KRSimplify_list_RegFileBase r)
                                      | KRApp_list_RegFileBase f r =>
                                        KRApp_list_RegFileBase (KRSimplify_list_RegFileBase f) (KRSimplify_list_RegFileBase r)
                                      | e => e
                                     end)
 
with KRSimplify_Mod (e : KRExpr_Mod) : KRExpr_Mod :=
       KRSimplifyTop_Mod
         (match e with
          | KRBase b => KRBase (KRSimplify_BaseModule b)
          | KRConcatMod a b => KRConcatMod (KRSimplify_Mod a) (KRSimplify_Mod b)
          | KRFold_right_Mod f a b => KRFold_right_Mod (KRSimplify_Mod_Mod_PairFunc f) (KRSimplify_Mod a) (KRSimplify_list_Mod b)
          | e => e
          end)
         
with KRSimplify_Mod_Mod_PairFunc(f: KRExpr_Mod_Mod_PairFunc) := f

with KRSimplify_list_Mod(e: KRExpr_list_Mod) :=
       KRSimplifyTop_list_Mod (match e with
                               | KRCons_list_Mod f r =>
                                 KRCons_list_Mod (KRSimplify_Mod f) (KRSimplify_list_Mod r)
                               | KRApp_list_Mod f r =>
                                 KRApp_list_Mod (KRSimplify_list_Mod f) (KRSimplify_list_Mod r)
                               | e => e
                               end)

with KRSimplify_RegFileBase_Mod_Func(f: KRExpr_RegFileBase_Mod_Func) := f

with KRSimplify_RegInitT_string_Func(f: KRExpr_RegInitT_string_Func) := f

with KRSimplify_DefMethT_string_Func(f: KRExpr_DefMethT_string_Func) := f

with KRSimplify_Rule_string_Func(f: KRExpr_Rule_string_Func) := f

with KRSimplify_string(s:KRExpr_string) :=
       KRSimplifyTop_string (match s with
                             | KRstring_append a b => KRstring_append (KRSimplify_string a) (KRSimplify_string b)
                             | KRfst_RegInitT_string r => KRfst_RegInitT_string (KRSimplify_RegInitT r)
                             | KRfst_DefMethT_string r => KRfst_DefMethT_string (KRSimplify_DefMethT r)
                             | KRfst_Rule_string r => KRfst_Rule_string (KRSimplify_Rule r)
                             | s => s
                             end)

with KRSimplify_list_string(e: KRExpr_list_string) :=
       KRSimplifyTop_list_string (match e with
                               | KRCons_list_string f r =>
                                 KRCons_list_string (KRSimplify_string f) (KRSimplify_list_string r)
                               | KRApp_list_string f r =>
                                 KRApp_list_string (KRSimplify_list_string f) (KRSimplify_list_string r)
                               | KRgetCallsPerMod m => KRgetCallsPerMod (KRSimplify_Mod m)
                               | KRConcat_string l => KRConcat_string (KRSimplify_list_list_string l)
                               | KRmap_RegInitT_string f l => KRmap_RegInitT_string (KRSimplify_RegInitT_string_Func f) (KRSimplify_list_RegInitT l)
                               | KRmap_DefMethT_string f l => KRmap_DefMethT_string (KRSimplify_DefMethT_string_Func f) (KRSimplify_list_DefMethT l)
                               | KRmap_Rule_string f l => KRmap_Rule_string (KRSimplify_Rule_string_Func f) (KRSimplify_list_Rule l)
                               | e => e
                               end)

with KRSimplify_list_list_string(e: KRExpr_list_list_string) :=
       KRSimplifyTop_list_list_string (match e with
                                       | KRCons_list_list_string f r =>
                                         KRCons_list_list_string (KRSimplify_list_string f) (KRSimplify_list_list_string r)
                                       | KRApp_list_list_string f r =>
                                         KRApp_list_list_string (KRSimplify_list_list_string f) (KRSimplify_list_list_string r)
                                       | e => e
                                       end)

with KRSimplify_Prop(p:KRExpr_Prop) :=
       KRSimplifyTop_Prop (match p with
                           | KRAnd_Prop a b => KRAnd_Prop (KRSimplify_Prop a) (KRSimplify_Prop b)
                           | KROr_Prop a b => KROr_Prop (KRSimplify_Prop a) (KRSimplify_Prop b)
                           | KRNot_Prop a => KRNot_Prop (KRSimplify_Prop a)
                           | KRIn_string_Prop a b => KRIn_string_Prop (KRSimplify_string a) (KRSimplify_list_string b)
                           | KRIn_RegInitT_Prop a b => KRIn_RegInitT_Prop (KRSimplify_RegInitT a) (KRSimplify_list_RegInitT b)
                           | KRIn_DefMethT_Prop a b => KRIn_DefMethT_Prop (KRSimplify_DefMethT a) (KRSimplify_list_DefMethT b)
                           | KRIn_Rule_Prop a b => KRIn_Rule_Prop (KRSimplify_Rule a) (KRSimplify_list_Rule b)
                           | KRDisjKey_RegInitT a b => KRDisjKey_RegInitT (KRSimplify_list_RegInitT a) (KRSimplify_list_RegInitT b)
                           | KRDisjKey_DefMethT a b => KRDisjKey_DefMethT (KRSimplify_list_DefMethT a) (KRSimplify_list_DefMethT b)
                           | KRDisjKey_Rule a b => KRDisjKey_Rule (KRSimplify_list_Rule a) (KRSimplify_list_Rule b)
                           | KREq_string_Prop a b => KREq_string_Prop (KRSimplify_string a) (KRSimplify_string b)
                           | KREq_RegInitT_Prop a b => KREq_RegInitT_Prop (KRSimplify_RegInitT a) (KRSimplify_RegInitT b)
                           | KREq_Rule_Prop a b => KREq_Rule_Prop (KRSimplify_Rule a) (KRSimplify_Rule b)
                           | KREq_DefMethT_Prop a b => KREq_DefMethT_Prop (KRSimplify_DefMethT a) (KRSimplify_DefMethT b)
                           | p => p
                           end).


Ltac match_KRExprType t :=
  match t with
  | KRExpr_RegInitT => idtac
  | KRExpr_list_RegInitT => idtac
  | KRExpr_list_list_RegInitT => idtac
  | KRExpr_RegInitValT => idtac
  | KRExpr_Rule => idtac
  | KRExpr_list_Rule => idtac
  | KRExpr_list_list_Rule => idtac
  | KRExpr_DefMethT => idtac
  | KRExpr_list_DefMethT => idtac
  | KRExpr_list_list_DefMethT => idtac
  | KRExpr_ModuleElt => idtac
  | KRExpr_list_ModuleElt => idtac
  | KRExpr_list_list_ModuleElt => idtac
  | KRExpr_string => idtac
  | KRExpr_Prop => idtac
  | KRExpr_list_string => idtac
  | KRExpr_list_list_string => idtac
  | KRExpr_Mod => idtac
  | KRExpr_list_Mod => idtac
  | KRExpr_RegFileBase => idtac
  | KRExpr_list_RegFileBase => idtac
  end.

Ltac match_KRExprDenote d :=
  match d with
  | KRExprDenote_RegInitT => idtac
  | KRExprDenote_RegInitValT => idtac
  | KRExprDenote_list_RegInitT => idtac
  | KRExprDenote_list_list_RegInitT => idtac
  | KRExprDenote_Rule => idtac
  | KRExprDenote_list_Rule => idtac
  | KRExprDenote_list_list_Rule => idtac
  | KRExprDenote_DefMethT => idtac
  | KRExprDenote_list_DefMethT => idtac
  | KRExprDenote_list_list_DefMethT => idtac
  | KRExprDenote_ModuleElt => idtac
  | KRExprDenote_list_ModuleElt => idtac
  | KRExprDenote_list_list_ModuleElt => idtac
  | KRExprDenote_Prop => idtac
  | KRExprDenote_string => idtac
  | KRExprDenote_list_string => idtac
  | KRExprDenote_list_list_string => idtac
  | KRExprDenote_Mod => idtac
  | KRExprDenote_list_Mod => idtac
  | KRExprDenote_RegFileBase => idtac
  | KRExprDenote_list_RegFileBase => idtac
  end.

Ltac isVar x :=
  match x with
  | ?A ?B => fail 1
  | _ => idtac
  end.

Ltac step_KRSimplifyTopSound :=
  match goal with
  | _ => progress intros
  | _ => progress simpl
  | _ => progress (autorewrite with kami_rewrite_db)
  | _ => progress reflexivity
  end.

Ltac solve_contKRSimplifyTopSound :=
  try (intros;reflexivity);
  match goal with
  | _ => progress (repeat step_KRSimplifyTopSound)
  | |- context [ (?D (match ?E with _ => _ end)) ] => match_KRExprDenote D;isVar E;induction E;try reflexivity
  | |- {?A = ?B}+{?A <> ?B} => repeat (decide equality)
  end.


Ltac solve_KRSimplifyTopSound :=
  try (intros;reflexivity);
  match goal with
  | _ => progress (repeat step_KRSimplifyTopSound)
  | V: ?T |- _ => match_KRExprType T;induction V;try reflexivity
  end.

Theorem my_in_app_iff: forall A (a:A) (l1:list A) (l2:list A), (@In A a (l1++l2)) = (@In A a l1 \/ @In A a l2).
Admitted.

Hint Rewrite my_in_app_iff : kami_rewrite_db.

Theorem my_DisjKey_Append1:
  forall T Q (x:list (T*Q)) y z,
  (DisjKey (x++y) z)=(DisjKey x z /\ DisjKey y z).
Admitted.

Hint Rewrite my_DisjKey_Append1 : kami_rewrite_db.

Theorem my_DisjKey_Append2:
    forall T Q (x:list (T*Q)) y z,
           (DisjKey x (y++z))=(DisjKey x y /\ DisjKey x z).
Admitted.

Hint Rewrite my_DisjKey_Append2 : kami_rewrite_db.

Theorem my_DisjKey_In_map2:
  forall A B a (k:A) r l, @DisjKey A B a ((k,r)::l)=(~List.In k (List.map fst a) /\ (DisjKey a l)).
Admitted.

Hint Rewrite my_DisjKey_In_map2 : kami_rewrite_db.

Theorem my_DisjKey_In_map1: forall A B b (k:A) r l,
    (@DisjKey A B ((k,r)::l) b)=(~List.In k (List.map fst b) /\ (DisjKey l b)).
Admitted.

Hint Rewrite my_DisjKey_In_map1 : kami_rewrite_db.

Theorem my_DisjKey_In_map_fst2: forall A B a (f:(A*B)) l,
    @DisjKey A B a (f::l)=(~List.In (fst f) (List.map fst a) /\ (DisjKey a l)).
Admitted.

Hint Rewrite my_DisjKey_In_map_fst2 : kami_rewrite_db.

Theorem my_DisjKey_In_map_fst1: forall A B b (f:(A*B)) l (W:forall (a1:A) (a2:A), {a1=a2}+{a1<>a2}),
    @DisjKey A B (f::l) b=(~List.In (fst f) (List.map fst b) /\ (DisjKey l b)).
Admitted.
    
Hint Rewrite my_DisjKey_In_map_fst1 : kami_rewrite_db.

Theorem my_and_true1: forall p, (p /\ True)=p.
Admitted.

Hint Rewrite my_and_true1 : kami_rewrite_db.

Theorem my_and_false1: forall p, (p /\ False)=False.
Admitted.

Hint Rewrite my_and_false1 : kami_rewrite_db.

Theorem my_and_true2: forall p, (True /\ p )=p.
Admitted.

Hint Rewrite my_and_true2 : kami_rewrite_db.

Theorem my_and_false2: forall p, (False /\ p)=False.
Admitted.

Hint Rewrite my_and_false2 : kami_rewrite_db.

Theorem my_or_true1: forall p, (p \/ True)=True.
Admitted.

Hint Rewrite my_or_true1 : kami_rewrite_db.

Theorem my_or_false1: forall p, (p \/ False)=p.
Admitted.

Hint Rewrite my_or_false1 : kami_rewrite_db.

Theorem my_or_true2: forall p, (True \/ p )=True.
Admitted.

Hint Rewrite my_or_true2 : kami_rewrite_db.

Theorem my_or_false2: forall p, (False \/ p)=p.
Admitted.

Hint Rewrite my_or_false2 : kami_rewrite_db.

Theorem my_not_not: forall p, (~ (~ p))=p.
Admitted.

Hint Rewrite my_not_not : kami_rewrite_db.

Theorem my_not_and_or: forall p q, (~ (p /\ q)) = ((~p) \/ (~q)).
Admitted.

Hint Rewrite my_not_and_or : kami_rewrite_db.

Theorem my_not_or_and: forall p q, (~ (p \/ q)) = ((~p) /\ (~q)).
Admitted.

Hint Rewrite my_not_or_and : kami_rewrite_db.

Theorem my_DisjKey_nil1 : forall A B (x:list (A*B)), DisjKey [] x=True.
Admitted.

Hint Rewrite my_DisjKey_nil1 : kami_rewrite_db.

Theorem my_DisjKey_nil2 : forall A B (x:list (A*B)), DisjKey x []=True.
Admitted.

Hint Rewrite my_DisjKey_nil2 : kami_rewrite_db.

Theorem my_not_true_false : (~ True) = False.
Admitted.

Hint Rewrite my_not_true_false : kami_rewrite_db.

Theorem my_not_false_true : (~ False) = True.
Admitted.

Hint Rewrite my_not_false_true : kami_rewrite_db.

Theorem my_eq_refl : forall A (a:A) (b:A), (a=b)=(b=a).
Admitted.

Scheme KRExpr_RegInitT_mut := Induction for KRExpr_RegInitT Sort Prop
  with KRExpr_Rule_mut := Induction for KRExpr_Rule Sort Prop
  with KRExpr_DefMethT_mut := Induction for KRExpr_DefMethT Sort Prop
  with KRExpr_ModuleElt_mut := Induction for KRExpr_ModuleElt Sort Prop
  with KRExpr_list_RegInitT_mut := Induction for KRExpr_list_RegInitT Sort Prop
  with KRExpr_list_Rule_mut := Induction for KRExpr_list_Rule Sort Prop
  with KRExpr_list_DefMethT_mut := Induction for KRExpr_list_DefMethT Sort Prop
  with KRExpr_list_ModuleElt_mut := Induction for KRExpr_list_ModuleElt Sort Prop
  with KRExpr_list_list_RegInitT_mut := Induction for KRExpr_list_list_RegInitT Sort Prop
  with KRExpr_list_list_Rule_mut := Induction for KRExpr_list_list_Rule Sort Prop
  with KRExpr_list_list_DefMethT_mut := Induction for KRExpr_list_list_DefMethT Sort Prop
  with KRExpr_list_list_ModuleElt_mut := Induction for KRExpr_list_list_ModuleElt Sort Prop
  with KRExpr_RegFileBase_mut := Induction for KRExpr_RegFileBase Sort Prop
  with KRExpr_list_RegFileBase_mut := Induction for KRExpr_list_RegFileBase Sort Prop
  with KRExpr_BaseModule_mut := Induction for KRExpr_BaseModule Sort Prop
  with KRExpr_Mod_mut := Induction for KRExpr_Mod Sort Prop
  with KRExpr_list_Mod_mut := Induction for KRExpr_list_Mod Sort Prop
  with KRExpr_CallWithSign_mut := Induction for KRExpr_CallWithSign Sort Prop
  with KRExpr_list_CallWithSign_mut := Induction for KRExpr_list_CallWithSign Sort Prop
  with KRExpr_list_list_CallWithSign_mut := Induction for KRExpr_list_list_CallWithSign Sort Prop
  with KRExpr_string_mut := Induction for KRExpr_string Sort Prop
  with KRExpr_list_string_mut := Induction for KRExpr_list_string Sort Prop
  with KRExpr_list_list_string_mut := Induction for KRExpr_list_list_string Sort Prop
  with KRExpr_Prop_mut := Induction for KRExpr_Prop Sort Prop.

(*Combined Scheme KRExpr_mutind from KRExpr_RegInitT_mut, KRExpr_Rule_mut, KRExpr_DefMethT_mut,
KRExpr_ModuleElt_mut, KRExpr_list_RegInitT_mut, KRExpr_list_Rule_mut, KRExpr_list_DefMethT_mut,
KRExpr_list_ModuleElt_mut, KRExpr_list_list_ModuleElt_mut, KRExpr_BaseModule_mut, KRExpr_Mod_mut.*)

Ltac noDenote x :=
  match x with
  | context [ ?D _ ] => match_KRExprDenote ?D;fail 1
  | _ => idtac
  end.

Ltac KRSimplifySound_unit :=
  match goal with
  | _ => reflexivity
  | _ => progress simpl
  (*| |- _ = KRExprDenote_Mod (match KRSimplify_Mod ?V with
                            _ => _
                             end) => let Q := fresh in remember V as Q;destruct Q
  | |- _ = KRExprDenote_list_DefMethT (match KRSimplify_Mod ?V with
                                       _ => _
                                       end) => let Q := fresh in remember V as Q;destruct Q*)
  | H: _ = _ |- _ => progress (simpl in H)
  | H: Base _ = Base _ |- _ => inversion H;subst;clear H
  | H: KRVar_RegInitT_string_Func _ =  KRVar_RegInitT_string_Func _ |- _ => inversion H;subst;clear H
  | _ => progress subst
  | _ => progress (autorewrite with kami_rewrite_db)
  | H: KRExprDenote_BaseModule _ = ?R |- _ => noDenote R;rewrite H
  | H: KRExprDenote_string _ = _ |- ?R => noDenote R;rewrite H
  | H: KRExprDenote_list_string _ = _ |- ?R => noDenote R;rewrite H
  | H: KRExprDenote_list_list_string _ = _ |- ?R => noDenote R;rewrite H
  | H: KRExprDenote_Mod _ = _ |- ?R => noDenote R;rewrite H
  | H: KRExprDenote_list_Mod _ = ?R |- _ => noDenote R;rewrite H
  | H: KRExprDenote_RegInitT _ = ?R |- _ => noDenote R;rewrite H
  | H: KRExprDenote_RegInitValT _ = ?R |- _ => noDenote R;rewrite H
  | H: KRExprDenote_list_RegInitT _ = ?R |- _ => noDenote R;rewrite H
  | H: KRExprDenote_list_list_RegInitT _ = ?R |- _ => noDenote R;rewrite H
  | H: KRExprDenote_Rule _ = _ |- ?R => noDenote R;rewrite H
  | H: KRExprDenote_list_Rule _ = _ |- ?R => noDenote R;rewrite H
  | H: KRExprDenote_list_list_Rule _ = _ |- ?R => noDenote R;rewrite H
  | H: KRExprDenote_DefMethT _ = _ |- ?R => noDenote R;rewrite H
  | H: KRExprDenote_list_DefMethT _ = _ |- ?R => noDenote R;rewrite H
  | H: KRExprDenote_list_list_DefMethT _ = ?R |- _ => noDenote R;rewrite H
  | H: KRExprDenote_RegFileBase _ = _ |- ?R => noDenote R;rewrite H
  | H: KRExprDenote_list_RegFileBase _ = _ |- ?R => noDenote R;rewrite H
  | H: KRExprDenote_CallWithSign _ = _ |- ?R => noDenote R;rewrite H
  | H: KRExprDenote_list_CallWithSign _ = _ |- ?R => noDenote R;rewrite H
  | H: KRExprDenote_list_list_CallWithSign _ = ?R |- _ => noDenote R;rewrite H
  | H: KRExprDenote_Prop _ = _ |- ?R => noDenote R;rewrite H
  | H: _ = True |- _ => rewrite H
  | H: _ = False |- _ => rewrite H
  | H: True = _ |- _ => rewrite <- H
  | H: False = _ |- _ => rewrite <- H
  (*| H: ?A = (?A /\ ?B) |- _ => rewrite <- H
  | H: ?B = (?A /\ ?B) |- _ => rewrite <- H
  | H: ?A = ?B |- (?Q /\ ?A)= (?Q /\ ?B) => rewrite H
  | H: ?A = ?B |- (?A /\ ?Q)= (?B /\ ?Q) => rewrite H
  | H1: ?A = ?B, H2: ?C = ?D |- (?A /\ ?C)= (?B /\ ?D) => rewrite H1;rewrite H2
  | H: ?A = ?B |- (?Q \/ ?A)= (?Q \/ ?B) => rewrite H
  | H: ?A = ?B |- (?A \/ ?Q)= (?B \/ ?Q) => rewrite H
  | H1: ?A = ?B, H2: ?C = ?D |- (?A \/ ?C)= (?B \/ ?D) => rewrite H1;rewrite H2
  | H: ?A |- ?A => apply H*)
  (*| |- context [match ?Q with _ => _ end ] => let R := fresh in (remember Q as R;destruct R; try reflexivity)*)
  end.

Ltac KRSimplifySound_setup mut H H0 H1 :=
  intros;
  eapply (mut
            (fun e : KRExpr_RegInitT => KRExprDenote_RegInitT e = KRExprDenote_RegInitT (KRSimplify_RegInitT e))
            (fun e : KRExpr_Rule => KRExprDenote_Rule e = KRExprDenote_Rule (KRSimplify_Rule e))
            (fun e : KRExpr_DefMethT => KRExprDenote_DefMethT e = KRExprDenote_DefMethT (KRSimplify_DefMethT e))
            (fun e : KRExpr_ModuleElt => KRExprDenote_ModuleElt e = KRExprDenote_ModuleElt (KRSimplify_ModuleElt e))
            (fun e : KRExpr_list_RegInitT => KRExprDenote_list_RegInitT e = KRExprDenote_list_RegInitT (KRSimplify_list_RegInitT e))
            (fun e : KRExpr_list_Rule => KRExprDenote_list_Rule e = KRExprDenote_list_Rule (KRSimplify_list_Rule e))
            (fun e : KRExpr_list_DefMethT => KRExprDenote_list_DefMethT e = KRExprDenote_list_DefMethT (KRSimplify_list_DefMethT e))
            (fun e : KRExpr_list_ModuleElt => KRExprDenote_list_ModuleElt e = KRExprDenote_list_ModuleElt (KRSimplify_list_ModuleElt e))
            (fun e : KRExpr_list_list_RegInitT => KRExprDenote_list_list_RegInitT e = KRExprDenote_list_list_RegInitT (KRSimplify_list_list_RegInitT e))
            (fun e : KRExpr_list_list_Rule => KRExprDenote_list_list_Rule e = KRExprDenote_list_list_Rule (KRSimplify_list_list_Rule e))
            (fun e : KRExpr_list_list_DefMethT => KRExprDenote_list_list_DefMethT e = KRExprDenote_list_list_DefMethT (KRSimplify_list_list_DefMethT e))
            (fun e : KRExpr_list_list_ModuleElt => KRExprDenote_list_list_ModuleElt e = KRExprDenote_list_list_ModuleElt (KRSimplify_list_list_ModuleElt e))
            (fun e : KRExpr_RegFileBase => KRExprDenote_RegFileBase e = KRExprDenote_RegFileBase (KRSimplify_RegFileBase e))
            (fun e : KRExpr_list_RegFileBase => KRExprDenote_list_RegFileBase e = KRExprDenote_list_RegFileBase (KRSimplify_list_RegFileBase e))
            (fun e : KRExpr_BaseModule => KRExprDenote_BaseModule e = KRExprDenote_BaseModule (KRSimplify_BaseModule e))
            (fun e : KRExpr_Mod => KRExprDenote_Mod e = KRExprDenote_Mod (KRSimplify_Mod e))
            (fun e : KRExpr_list_Mod => KRExprDenote_list_Mod e = KRExprDenote_list_Mod (KRSimplify_list_Mod e))
            (fun e : KRExpr_CallWithSign => KRExprDenote_CallWithSign e = KRExprDenote_CallWithSign (KRSimplify_CallWithSign e))
            (fun e : KRExpr_list_CallWithSign => KRExprDenote_list_CallWithSign e = KRExprDenote_list_CallWithSign (KRSimplify_list_CallWithSign e))
            (fun e : KRExpr_list_list_CallWithSign => KRExprDenote_list_list_CallWithSign e = KRExprDenote_list_list_CallWithSign (KRSimplify_list_list_CallWithSign e))
            (fun e : KRExpr_string => KRExprDenote_string e = KRExprDenote_string (KRSimplify_string e))
            (fun e : KRExpr_list_string => KRExprDenote_list_string e = KRExprDenote_list_string (KRSimplify_list_string e))
            (fun e : KRExpr_list_list_string => KRExprDenote_list_list_string e = KRExprDenote_list_list_string (KRSimplify_list_list_string e))
            (fun e : KRExpr_Prop => KRExprDenote_Prop e = KRExprDenote_Prop (KRSimplify_Prop e))
         );
  try (intros;autorewrite with KRSimplify; autorewrite with KRSimplifyTopSound; simpl; try (rewrite <- H); try  (rewrite <- H0); try (rewrite <- H1); reflexivity);intros.

Ltac KRSimplifySound_crunch :=
  match goal with
  | |- context [ KRExprDenote_Mod (match ?Q with _ => _ end) ] => let R := fresh in (remember Q as R;destruct R;repeat KRSimplifySound_unit)
  | |- context [ KRExprDenote_string (match ?Q with _ => _ end) ] => let R := fresh in (remember Q as R;destruct R;repeat KRSimplifySound_unit)
  | |- context [ KRExprDenote_RegInitT (match ?Q with _ => _ end) ] => let R := fresh in (remember Q as R;destruct R;repeat KRSimplifySound_unit)
  | |- context [ KRExprDenote_Rule (match ?Q with _ => _ end) ] => let R := fresh in (remember Q as R;destruct R;repeat KRSimplifySound_unit)
  | |- context [ KRExprDenote_DefMethT (match ?Q with _ => _ end) ] => let R := fresh in (remember Q as R;destruct R;repeat KRSimplifySound_unit)
  | |- context [ KRExprDenote_list_string (match ?Q with _ => _ end) ] => let R := fresh in (remember Q as R;destruct R;repeat KRSimplifySound_unit)
  | |- context [ KRExprDenote_list_list_string (match ?Q with _ => _ end) ] => let R := fresh in (remember Q as R;destruct R;repeat KRSimplifySound_unit)
  | |- context [ KRExprDenote_list_Mod (match ?Q with _ => _ end) ] => let R := fresh in (remember Q as R;destruct R;repeat KRSimplifySound_unit)
  | |- context [ KRExprDenote_BaseModule (match ?Q with _ => _ end) ] => let R := fresh in (remember Q as R;destruct R;repeat KRSimplifySound_unit)
  | |- context [ KRExprDenote_list_RegInitT (match ?Q with _ => _ end) ] => let R := fresh in (remember Q as R;destruct R;repeat KRSimplifySound_unit)
  | |- context [ KRExprDenote_list_list_RegInitT (match ?Q with _ => _ end) ] => let R := fresh in (remember Q as R;destruct R;repeat KRSimplifySound_unit)
  | |- context [ KRExprDenote_list_DefMethT (match ?Q with _ => _ end) ] => let R := fresh in (remember Q as R;destruct R;repeat KRSimplifySound_unit)
  | |- context [ KRExprDenote_list_list_DefMethT (match ?Q with _ => _ end) ] => let R := fresh in (remember Q as R;destruct R;repeat KRSimplifySound_unit)
  | |- context [ KRExprDenote_list_Rule (match ?Q with _ => _ end) ] => let R := fresh in (remember Q as R;destruct R;repeat KRSimplifySound_unit)
  | |- context [ KRExprDenote_list_list_Rule (match ?Q with _ => _ end) ] => let R := fresh in (remember Q as R;destruct R;repeat KRSimplifySound_unit)
  | |- context [ KRExprDenote_list_CallWithSign (match ?Q with _ => _ end) ] => let R := fresh in (remember Q as R;destruct R;repeat KRSimplifySound_unit)
  | |- context [ KRExprDenote_list_list_CallWithSign (match ?Q with _ => _ end) ] => let R := fresh in (remember Q as R;destruct R;repeat KRSimplifySound_unit)
  | |- context [ KRExprDenote_list_ModuleElt (match ?Q with _ => _ end) ] => let R := fresh in (remember Q as R;destruct R;repeat KRSimplifySound_unit)
  | |- context [ KRExprDenote_list_RegFileBase (match ?Q with _ => _ end) ] => let R := fresh in (remember Q as R;destruct R;repeat KRSimplifySound_unit)
  | |- context [ KRExprDenote_Prop (match ?Q with _ => _ end) ] => let R := fresh in (remember Q as R;destruct R;repeat KRSimplifySound_unit)
  | |- context [ KRExprDenote_Mod_list_RegInitT_Func ?Q ] => let R := fresh in (remember Q as R;destruct R;repeat KRSimplifySound_unit)
  | |- context [ KRExprDenote_Mod_list_DefMethT_Func ?Q ] => let R := fresh in (remember Q as R;destruct R;repeat KRSimplifySound_unit)
  | |- context [ KRExprDenote_Mod_list_Rule_Func ?Q ] => let R := fresh in (remember Q as R;destruct R;repeat KRSimplifySound_unit)
  | |- context [ KRExprDenote_RegFileBase_list_RegInitT_Func ?Q ] => let R := fresh in (remember Q as R;destruct R;repeat KRSimplifySound_unit)
  | |- context [ KRExprDenote_RegFileBase_list_DefMethT_Func ?Q ] => let R := fresh in (remember Q as R;destruct R;repeat KRSimplifySound_unit)
  | |- context [ KRExprDenote_RegInitT_string_Func ?Q ] => let R := fresh in (remember Q as R;destruct R;repeat KRSimplifySound_unit)
  | |- context [ KRExprDenote_DefMethT_string_Func ?Q ] => let R := fresh in (remember Q as R;destruct R;repeat KRSimplifySound_unit)
  | |- context [ KRExprDenote_Rule_string_Func ?Q ] => let R := fresh in (remember Q as R;destruct R;repeat KRSimplifySound_unit)
  | |- context [ KRExprDenote_Mod_Mod_PairFunc ?Q ] => let R := fresh in (remember Q as R;destruct R;repeat KRSimplifySound_unit)
  | _ => KRSimplifySound_unit;repeat KRSimplifySound_unit
  | |- { ?A = ?B } + { ?A <> ?B } => intros;repeat (decide equality)
  | |- forall _, _ => intros
  | H: KRVar_RegInitT_string_Func _ = KRfst_RegInitT_string_Func |- _ => inversion H
  | H: KRfst_RegInitT_string_Func = KRVar_RegInitT_string_Func _ |- _ => inversion H
  | H: KRVar_RegInitT_string_Func _ = KRVar_RegInitT_string_Func _ |- _ => inversion H
  | H: KRVar_DefMethT_string_Func _ = KRfst_DefMethT_string_Func |- _ => inversion H
  | H: KRfst_DefMethT_string_Func = KRVar_DefMethT_string_Func _ |- _ => inversion H
  | H: KRVar_DefMethT_string_Func _ = KRVar_DefMethT_string_Func _ |- _ => inversion H
  | H: KRVar_Rule_string_Func _ = KRfst_Rule_string_Func |- _ => inversion H
  | H: KRfst_Rule_string_Func = KRVar_Rule_string_Func _ |- _ => inversion H
  | H: KRVar_Rule_string_Func _ = KRVar_Rule_string_Func _ |- _ => inversion H
  end.

Theorem KRSimplify_RegInitValT_trivial:
  forall x, (KRSimplify_RegInitValT x)=x.
Admitted.

Hint Rewrite KRSimplify_RegInitValT_trivial : kami_rewrite_db.

Theorem KRSimplify_list_RegInitT_KRApp_list_RegInitT : forall k k0,
    KRSimplify_list_RegInitT (KRApp_list_RegInitT k k0)=KRSimplifyTop_list_RegInitT (KRApp_list_RegInitT (KRSimplify_list_RegInitT k) (KRSimplify_list_RegInitT k0)).
Proof.
  reflexivity.
Qed.

(*Theorem KRSimplify_list_RegInitT_KRgetAllRegisters:
  forall k, KRSimplify_list_RegInitT (KRgetAllRegisters k)=KRgetAllRegisters (KRSimplify_Mod k).
Proof.
  intros.
  simpl. destruct k;simpl;try reflexivity.
  destruct k;try reflexivity.
  simpl.
  destruct k;try reflexivity;simpl.
  destruct k;
  reflexivity.
Qed.*)


Hint Rewrite KRSimplify_list_RegInitT_KRApp_list_RegInitT : KRSimplify.

Theorem KRSimplify_list_RegInitT_KRMakeModule_regs:
  forall k, KRSimplify_list_RegInitT (KRMakeModule_regs k)=KRSimplifyTop_list_RegInitT (KRMakeModule_regs (KRSimplify_list_ModuleElt k)).
Proof.
  reflexivity.
Qed.

Hint Rewrite KRSimplify_list_RegInitT_KRMakeModule_regs : KRSimplify.

Theorem KRSimplify_list_Rule_KRApp_list_Rule : forall k k0,
    KRSimplify_list_Rule (KRApp_list_Rule k k0)=KRSimplifyTop_list_Rule (KRApp_list_Rule (KRSimplify_list_Rule k) (KRSimplify_list_Rule k0)).
Proof.
  reflexivity.
Qed.

Hint Rewrite KRSimplify_list_Rule_KRApp_list_Rule : KRSimplify.

Theorem KRSimplify_list_Rule_KRMakeModule_rules:
  forall k, KRSimplify_list_Rule (KRMakeModule_rules k)=KRSimplifyTop_list_Rule (KRMakeModule_rules (KRSimplify_list_ModuleElt k)).
Proof.
  reflexivity.
Qed.

Hint Rewrite KRSimplify_list_Rule_KRMakeModule_rules : KRSimplify.

Theorem KRSimplify_list_DefMethT_KRApp_list_DefMethT : forall k k0,
    KRSimplify_list_DefMethT (KRApp_list_DefMethT k k0)=KRSimplifyTop_list_DefMethT (KRApp_list_DefMethT (KRSimplify_list_DefMethT k) (KRSimplify_list_DefMethT k0)).
Proof.
  reflexivity.
Qed.

Hint Rewrite KRSimplify_list_DefMethT_KRApp_list_DefMethT : KRSimplify.

Theorem KRSimplify_list_DefMethT_KRMakeModule_meths:
  forall k, KRSimplify_list_DefMethT (KRMakeModule_meths k)=KRSimplifyTop_list_DefMethT (KRMakeModule_meths (KRSimplify_list_ModuleElt k)).
Proof.
  reflexivity.
Qed.

Hint Rewrite KRSimplify_list_DefMethT_KRMakeModule_meths : KRSimplify.

Theorem KRSimplify_list_ModuleElt_KRApp_list_ModuleElt:
  forall k k0, KRSimplify_list_ModuleElt (KRApp_list_ModuleElt k k0)=KRSimplifyTop_list_ModuleElt (KRApp_list_ModuleElt (KRSimplify_list_ModuleElt k) (KRSimplify_list_ModuleElt k0)).
Proof.
  reflexivity.
Qed.

Hint Rewrite  KRSimplify_list_ModuleElt_KRApp_list_ModuleElt : KRSimplify.

Theorem KRSimplify_list_list_ModuleElt_KRApp_list_list_ModuleElt:
  forall k k0, KRSimplify_list_list_ModuleElt (KRApp_list_list_ModuleElt k k0)=KRSimplifyTop_list_list_ModuleElt (KRApp_list_list_ModuleElt (KRSimplify_list_list_ModuleElt k) (KRSimplify_list_list_ModuleElt k0)).
Proof.
  reflexivity.
Qed.

Hint Rewrite  KRSimplify_list_list_ModuleElt_KRApp_list_list_ModuleElt : KRSimplify.

Theorem KRSimplify_BaseModule_KRBaseMod:
  forall k k0 k1, KRSimplify_BaseModule (KRBaseMod k k0 k1)=KRSimplifyTop_BaseModule (KRBaseMod (KRSimplify_list_RegInitT k) (KRSimplify_list_Rule k0) (KRSimplify_list_DefMethT k1)).
Proof.
  reflexivity.
Qed.

Hint Rewrite KRSimplify_BaseModule_KRBaseMod: KRSimplify.

