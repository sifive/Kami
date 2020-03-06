Require Import Kami.Notations.
Require Import Kami.Syntax.
Require Import List.
Require Import Kami.Notations_rewrites.
Require Import Program.Equality.
Require Import Kami.Rewrites.ReflectionPre.
Require Import Kami.Rewrites.ReflectionSoundTopTheorems.
Require Import Kami.Rewrites.ReflectionSoundTheorems1.
Require Import Kami.Rewrites.ReflectionSoundTheorems2.

(*Goal forall (a:ModuleElt) (b:list ModuleElt) c, app (cons a b) c=cons a (app b c).
  intros.
  match goal with
  | |- ?A = ?B => let x := (ltac:(KRExprReify A (KRTypeList (KRTypeElem KRElemModuleElt)))) in
                  change A with (KRExprDenote_list_ModuleElt x);
                    rewrite KRSimplifySound_list_ModuleElt;
                    cbv [KRSimplify_list_ModuleElt KRSimplifyTop_list_ModuleElt KRExprDenote_list_ModuleElt KRExprDenote_ModuleElt KRSimplifyTop_ModuleElt KRSimplify_ModuleElt]
  end.
Abort.*)

Ltac KRSimplifyTac e tp :=
  let x := (ltac:(KRExprReify e tp)) in
  let denote := match tp with
                | (KRTypeElem KRElemRegInitT) => KRExprDenote_RegInitT
                | (KRTypeElem KRElemRule) => KRExprDenote_Rule
                | (KRTypeElem KRElemDefMethT) => KRExprDenote_DefMethT
                | (KRTypeElem KRElemModuleElt) => KRExprDenote_ModuleElt
                | (KRTypeList (KRTypeElem KRElemRegInitT)) => KRExprDenote_list_RegInitT
                | (KRTypeList (KRTypeElem KRElemRule)) => KRExprDenote_list_Rule
                | (KRTypeList (KRTypeElem KRElemDefMethT)) => KRExprDenote_list_DefMethT
                | (KRTypeList (KRTypeElem KRElemModuleElt)) => KRExprDenote_list_ModuleElt
                | (KRTypeList (KRTypeList (KRTypeElem KRElemRegInitT))) => KRExprDenote_list_list_RegInitT
                | (KRTypeList (KRTypeList (KRTypeElem KRElemRule))) => KRExprDenote_list_list_Rule
                | (KRTypeList (KRTypeList (KRTypeElem KRElemDefMethT))) => KRExprDenote_list_list_DefMethT
                | (KRTypeList (KRTypeList (KRTypeElem KRElemModuleElt))) => KRExprDenote_list_list_ModuleElt
                | (KRTypeElem KRElemBaseModule) => KRExprDenote_BaseModule
                | (KRTypeElem KRElemMod) => KRExprDenote_Mod
                | (KRTypeList (KRTypeElem KRElemMod)) => KRExprDenote_list_Mod
                | (KRTypeElem KRElemString) => KRExprDenote_string
                | (KRTypeList (KRTypeElem KRElemString)) => KRExprDenote_list_string
                | (KRTypeList (KRTypeList (KRTypeElem KRElemString))) => KRExprDenote_list_list_string
                | (KRTypeElem KRElemRegFileBase) => KRExprDenote_RegFileBase
                | (KRTypeList (KRTypeElem KRElemRegFileBase)) => KRExprDenote_list_RegFileBase
                | (KRTypeElem KRElemCallWithSign) => KRExprDenote_CallWithSign
                | (KRTypeList (KRTypeElem KRElemCallWithSign)) => KRExprDenote_list_CallWithSign
                | (KRTypeList (KRTypeList (KRTypeElem KRElemCallWithSign))) => KRExprDenote_list_list_CallWithSign
                | (KRTypeElem KRElemProp) => KRExprDenote_Prop
                end in
  let simplifySound := match tp with
                | (KRTypeElem KRElemRegInitT) => KRSimplifySound_RegInitT
                | (KRTypeElem KRElemRule) => KRSimplifySound_Rule
                | (KRTypeElem KRElemDefMethT) => KRSimplifySound_DefMethT
                | (KRTypeElem KRElemModuleElt) => KRSimplifySound_ModuleElt
                | (KRTypeList (KRTypeElem KRElemRegInitT)) => KRSimplifySound_list_RegInitT
                | (KRTypeList (KRTypeElem KRElemRule)) => KRSimplifySound_list_Rule
                | (KRTypeList (KRTypeElem KRElemDefMethT)) => KRSimplifySound_list_DefMethT
                | (KRTypeList (KRTypeElem KRElemModuleElt)) => KRSimplifySound_list_ModuleElt
                | (KRTypeList (KRTypeList (KRTypeElem KRElemRegInitT))) => KRSimplifySound_list_RegInitT
                | (KRTypeList (KRTypeList (KRTypeElem KRElemRule))) => KRSimplifySound_list_Rule
                | (KRTypeList (KRTypeList (KRTypeElem KRElemDefMethT))) => KRSimplifySound_list_DefMethT
                | (KRTypeList (KRTypeList (KRTypeElem KRElemModuleElt))) => KRSimplifySound_list_list_ModuleElt
                | (KRTypeElem KRElemString) => KRSimplifySound_string
                | (KRTypeList (KRTypeElem KRElemString)) => KRSimplifySound_list_string
                | (KRTypeList (KRTypeList (KRTypeElem KRElemString))) => KRSimplifySound_list_list_string
                | (KRTypeElem KRElemRegFileBase) => KRSimplifySound_RegFileBase
                | (KRTypeList (KRTypeElem KRElemRegFileBase)) => KRSimplify_list_RegFileBase
                | (KRTypeElem KRElemCallWithSign) => KRSimplifySound_CallWithSign
                | (KRTypeList (KRTypeElem KRElemCallWithSign)) => KRSimplify_list_CallWithSign
                | (KRTypeElem KRElemBaseModule) => KRSimplifySound_BaseModule
                | (KRTypeElem KRElemMod) => KRSimplifySound_Mod
                | (KRTypeList (KRTypeElem KRElemMod)) => KRSimplifySound_list_Mod
                | (KRTypeElem KRElemProp) => KRSimplifySound_Prop
                end in
  change e with (denote x);repeat (rewrite <- simplifySound;cbv [
                sappend srev sdisjPrefix String.eqb Ascii.eqb Bool.eqb
                KRSimplify_RegInitT KRSimplifyTop_RegInitT
                KRSimplify_RegInitValT KRSimplifyTop_RegInitValT
                KRSimplify_Rule KRSimplifyTop_Rule
                KRSimplify_DefMethT KRSimplifyTop_DefMethT
                KRSimplify_ModuleElt KRSimplifyTop_ModuleElt
                KRSimplify_list_RegInitT KRSimplifyTop_list_RegInitT
                KRSimplify_list_Rule KRSimplifyTop_list_Rule
                KRSimplify_list_DefMethT KRSimplifyTop_list_DefMethT
                KRSimplify_list_ModuleElt KRSimplifyTop_list_ModuleElt
                KRSimplify_list_list_RegInitT KRSimplifyTop_list_list_RegInitT
                KRSimplify_list_list_Rule KRSimplifyTop_list_list_Rule
                KRSimplify_list_list_DefMethT KRSimplifyTop_list_list_DefMethT
                KRSimplify_list_list_ModuleElt KRSimplifyTop_list_list_ModuleElt
                KRSimplify_BaseModule KRSimplifyTop_BaseModule
                KRSimplify_RegFileBase KRSimplifyTop_RegFileBase
                KRSimplify_list_RegFileBase KRSimplifyTop_list_RegFileBase
                KRSimplify_string KRSimplifyTop_string
                KRSimplify_list_string KRSimplifyTop_list_string
                KRSimplify_list_list_string KRSimplifyTop_list_list_string
                KRSimplify_Mod KRSimplifyTop_Mod
                KRSimplify_Mod KRSimplifyTop_list_Mod
                KRSimplify_Prop KRSimplifyTop_Prop
                                  ]);
  cbv [
      sappend srev sdisjPrefix String.eqb Ascii.eqb Bool.eqb
                KRExprDenote_RegInitT
                KRExprDenote_RegInitValT
                KRExprDenote_Rule
                KRExprDenote_DefMethT
                KRExprDenote_ModuleElt
                KRExprDenote_list_RegInitT
                KRExprDenote_list_Rule
                KRExprDenote_list_DefMethT
                KRExprDenote_ActionVoid
                KRExprDenote_MethodT
                KRExprDenote_list_ModuleElt
                KRExprDenote_list_list_RegInitT
                KRExprDenote_list_list_Rule
                KRExprDenote_list_list_DefMethT
                KRExprDenote_list_list_ModuleElt
                KRExprDenote_BaseModule
                KRExprDenote_Mod
                KRExprDenote_list_Mod
                KRExprDenote_RegFileBase
                KRExprDenote_list_RegFileBase
                KRExprDenote_string
                KRExprDenote_list_string
                KRExprDenote_list_list_string
                KRExprDenote_Prop].


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
Definition KRSimplifyTop_list_Rule2 (e : KRExpr_list_Rule) : KRExpr_list_Rule :=
  match e with
  | KRApp_list_Rule f c => match f with
                    | KRCons_list_Rule ff rr => KRCons_list_Rule ff (KRApp_list_Rule rr c)
                    | KRNil_list_Rule => c
                    | x => match c with
                           | KRNil_list_Rule => f
                           | y => KRVar_list_Rule []
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
       | KRMEMeth a => KRVar_list_Rule [] (*KRMakeModule_rules b*)
       | KRMERule a => KRVar_list_Rule [] (*KRCons_list_Rule a (KRMakeModule_rules b)*)
       | _ => KRVar_list_Rule []
       end
     | KRRegisters r => KRNil_list_Rule
     | KRNil_list_ModuleElt => KRNil_list_Rule
     | _ => KRVar_list_Rule []
     end
   | e => KRVar_list_Rule []
   end.

Theorem KRSimplifyTopSound_list_Rule2:
  forall x, KRExprDenote_list_Rule (KRSimplifyTop_list_Rule2 x)=KRExprDenote_list_Rule x.
Admitted.

Goal forall a b c d e, makeModule_regs [MERegister a;MERule b;MEMeth c;MERegister d]=e.
  intros.
  match goal with
  | |- ?A = ?B => 
    (*let x := (ltac:(KRExprReify A (KRTypeList (KRTypeElem KRElemRegInitT)))) in
    idtac x*)
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
Goal forall a b c d e, makeModule_meths [MEMeth a;MERule b;MERegister c;MERegister d]=e.
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
Abort.
Goal forall proc_name, ~(( proc_name ++ "_" ++ "a")%string = (proc_name ++ "_" ++  "b")%string).
  intros.
  match goal with
  | |- ~ ?A => 
    let x := (ltac:(KRExprReify (~A) (KRTypeElem KRElemProp))) in change (~A) with (KRExprDenote_Prop x)
  end.
  rewrite <- KRSimplifySound_Prop.
  cbv [
                KRSimplify_RegInitT KRSimplifyTop_RegInitT
                KRSimplify_RegInitValT KRSimplifyTop_RegInitValT
                KRSimplify_Rule KRSimplifyTop_Rule
                KRSimplify_DefMethT KRSimplifyTop_DefMethT
                KRSimplify_ModuleElt KRSimplifyTop_ModuleElt
                KRSimplify_list_RegInitT KRSimplifyTop_list_RegInitT
                KRSimplify_list_Rule KRSimplifyTop_list_Rule
                KRSimplify_list_DefMethT KRSimplifyTop_list_DefMethT
                KRSimplify_list_ModuleElt KRSimplifyTop_list_ModuleElt
                KRSimplify_list_list_RegInitT KRSimplifyTop_list_list_RegInitT
                KRSimplify_list_list_Rule KRSimplifyTop_list_list_Rule
                KRSimplify_list_list_DefMethT KRSimplifyTop_list_list_DefMethT
                KRSimplify_list_list_ModuleElt KRSimplifyTop_list_list_ModuleElt
                KRSimplify_BaseModule KRSimplifyTop_BaseModule
                KRSimplify_RegFileBase KRSimplifyTop_RegFileBase
                KRSimplify_list_RegFileBase KRSimplifyTop_list_RegFileBase
                KRSimplify_string KRSimplifyTop_string
                KRSimplify_list_string KRSimplifyTop_list_string
                KRSimplify_list_list_string KRSimplifyTop_list_list_string
                KRSimplify_Mod KRSimplifyTop_Mod
                KRSimplify_Mod KRSimplifyTop_list_Mod
                KRSimplify_Prop KRSimplifyTop_Prop
    ].
  cbv [         sappend srev sdisjPrefix
                KRExprDenote_RegInitT
                KRExprDenote_Rule
                KRExprDenote_DefMethT
                KRExprDenote_ModuleElt
                KRExprDenote_list_RegInitT
                KRExprDenote_list_Rule
                KRExprDenote_list_DefMethT
                KRExprDenote_list_ModuleElt
                KRExprDenote_list_list_RegInitT
                KRExprDenote_list_list_Rule
                KRExprDenote_list_list_DefMethT
                KRExprDenote_list_list_ModuleElt
                KRExprDenote_BaseModule
                KRExprDenote_Mod
                KRExprDenote_list_Mod
                KRExprDenote_RegFileBase
                KRExprDenote_list_RegFileBase
                KRExprDenote_string
                KRExprDenote_list_string
                KRExprDenote_list_list_string
                KRExprDenote_Prop].
Abort.

