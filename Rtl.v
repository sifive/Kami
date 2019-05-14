Require Import Syntax String.

Set Implicit Arguments.
Set Asymmetric Patterns.

Local Notation VarType := nat.
Local Notation NoneVal := (0: VarType).
Local Notation InitVal := (1: VarType).

Inductive RtlExpr: Kind -> Type :=
| RtlReadReg k: string -> RtlExpr k
| RtlReadWire k: (string * VarType) -> RtlExpr k
| RtlConst k: ConstT k -> RtlExpr k
| RtlUniBool: UniBoolOp -> RtlExpr Bool -> RtlExpr Bool
| RtlCABool: CABoolOp -> list (RtlExpr Bool) -> RtlExpr Bool
| RtlUniBit n1 n2: UniBitOp n1 n2 -> RtlExpr (Bit n1) -> RtlExpr (Bit n2)
| RtlCABit n: CABitOp -> list (RtlExpr (Bit n)) -> RtlExpr (Bit n)
| RtlBinBit n1 n2 n3: BinBitOp n1 n2 n3 ->
                      RtlExpr (Bit n1) -> RtlExpr (Bit n2) ->
                      RtlExpr (Bit n3)
| RtlBinBitBool n1 n2: BinBitBoolOp n1 n2 ->
                       RtlExpr (Bit n1) -> RtlExpr (Bit n2) ->
                       RtlExpr Bool
| RtlITE k: RtlExpr Bool -> RtlExpr k -> RtlExpr k -> RtlExpr k
| RtlEq k: RtlExpr (k) -> RtlExpr (k) -> RtlExpr (Bool)
| RtlReadStruct n (fk: Fin.t n -> Kind) (fs: Fin.t n -> string)
                (e: RtlExpr (Struct fk fs)) i:
    RtlExpr (fk i)
| RtlBuildStruct n (fk: Fin.t n -> Kind) (fs: Fin.t n -> string)
                 (fv: forall i, RtlExpr (fk i)):
    RtlExpr (Struct fk fs)
| RtlReadArray n k: RtlExpr (Array n k) ->
                    RtlExpr (Bit (Nat.log2_up n)) ->
                    RtlExpr k
| RtlReadArrayConst n k: RtlExpr (Array n k) ->
                         Fin.t n ->
                         RtlExpr k
| RtlBuildArray n k: (Fin.t n -> RtlExpr k) -> RtlExpr (Array n k).

Inductive RtlSysT: Type :=
| RtlDispString (s: string): RtlSysT
| RtlDispExpr k (e: RtlExpr k) (ff: FullFormat k): RtlSysT
| RtlFinish: RtlSysT.

Record RtlSyncRead :=
  { readSync : SyncRead ;
    bypassRqRs: bool ;
    bypassWrRd: bool }.

Inductive RtlRegFileReaders :=
| RtlAsync (reads: list (string * bool))
| RtlSync (isAddr: bool) (reads: list RtlSyncRead).

Record RtlRegFileBase := { rtlIsWrMask : bool ;
                           rtlNum: nat ;
                           rtlDataArray: string ;
                           rtlReads: RtlRegFileReaders ;
                           rtlWrite: string ;
                           rtlIdxNum: nat ;
                           rtlData: Kind ;
                           rtlInit: RegFileInitT rtlIdxNum rtlData }.

Record RtlModule :=
  { hiddenWires: list (string * VarType);
    regFiles: list RtlRegFileBase;
    inputs: list (string * VarType * Kind);
    outputs: list (string * VarType * Kind);
    regInits: list (string * sigT RegInitValT);
    regWrites: list (string * sigT RtlExpr);
    wires: list (string * VarType * sigT RtlExpr);
    sys: list (RtlExpr Bool * list RtlSysT)
  }.

Delimit Scope rtl_expr_scope with rtl_expr.

Notation "e1 && e2" := (RtlCABool And (e1 :: e2 :: nil)) : rtl_expr_scope.
Notation "e1 || e2" := (RtlCABool Or (e1 :: e2 :: nil)) : rtl_expr_scope.


(* Section BitOps. *)

(*   Local Fixpoint concatStructExpr n {struct n}: *)
(*     forall (sizes: Fin.t n -> nat) *)
(*            (f: forall i, RtlExpr (Bit (sizes i))), *)
(*       RtlExpr (Bit (sumSizes sizes)) := *)
(*     match n return forall *)
(*         (sizes: Fin.t n -> nat) *)
(*         (f: forall i, RtlExpr (Bit (sizes i))), *)
(*         RtlExpr (Bit (sumSizes sizes)) with *)
(*     | 0 => fun _ _ => RtlConst WO *)
(*     | S m => fun sizes f => *)
(*                RtlBinBit *)
(*                  (Concat _ _) (f Fin.F1) *)
(*                  (@concatStructExpr m (fun x => (sizes (Fin.FS x))) (fun x => f (Fin.FS x))) *)
(*     end. *)

(*   Local Definition castBits ni no (pf: ni = no) (e: RtlExpr (Bit ni)) := *)
(*     nat_cast (fun n => RtlExpr (Bit n)) pf e. *)

(*   Fixpoint rtlPack (k: Kind): RtlExpr k -> RtlExpr (Bit (size k)). *)
(*     refine *)
(*       match k return RtlExpr k -> RtlExpr (Bit (size k)) with *)
(*       | Bool => fun e => (RtlITE e (RtlConst (WO~1)%word) (RtlConst (WO~0)%word)) *)
(*       | Bit n => fun e => e *)
(*       | Struct n fk fs => *)
(*         fun e => *)
(*           concatStructExpr (fun i => size (fk i)) *)
(*                            (fun i => @rtlPack (fk i) (RtlReadStruct e i)) *)
(*       | Array n k => *)
(*         fun e => *)
(*           (fix help i := *)
(*              match i return RtlExpr (Bit (i * size k)) with *)
(*              | 0 => RtlConst WO *)
(*              | S m => *)
(*                castBits _ (RtlBinBit *)
(*                              (Concat (size k) (m * size k)) *)
(*                              (@rtlPack k (RtlReadArray e (RtlConst (natToWord (Nat.log2_up n) m)))) *)
(*                              (help m)) *)
(*              end) n *)
(*       end; abstract lia. *)
(*   Defined. *)

(*   Local Definition ConstExtract lsb n msb (e: RtlExpr (Bit (lsb + n + msb))): RtlExpr (Bit n) := *)
(*       RtlUniBit (TruncMsb lsb n) (RtlUniBit (TruncLsb (lsb + n) msb) e). *)

(*   Fixpoint rtlUnpack (k: Kind): RtlExpr (Bit (size k)) -> RtlExpr k := *)
(*     match k return RtlExpr (Bit (size k)) -> RtlExpr k with *)
(*     | Bool => fun e => RtlEq e (RtlConst (WO~1)%word) *)
(*     | Bit _ => fun e => e *)
(*     | Struct n fk fs => *)
(*       fun e => RtlBuildStruct *)
(*                  _ _ *)
(*                  (fun i => *)
(*                     rtlUnpack *)
(*                       _ *)
(*                       (ConstExtract *)
(*                          _ _ (sumSizesMsbs i (fun j => size (fk j))) *)
(*                          (@castBits _ _ (helper_sumSizes i (fun j => size (fk j))) e))) *)
(*     | Array n k => *)
(*       fun e => *)
(*         RtlBuildArray *)
(*           (fun i => rtlUnpack _ (ConstExtract (proj1_sig (Fin.to_nat i) * size k) _ _ *)
(*                                               (@castBits _ _ (helper_array _ _) e) )) *)
(*     end. *)
(* End BitOps. *)

(* Notation "name ::= value" := *)
(*   (existT (fun a : Attribute Kind => RtlExpr (snd a)) *)
(*           (name%string, _) value) (at level 50, only parsing) : rtl_struct_init_scope. *)
(* Delimit Scope rtl_struct_init_scope with rtl_init. *)

(* Notation getStructVal ls := *)
(*   (RtlBuildStruct (fun i => snd (Vector.nth (Vector.map (@projT1 _ _) ls) i)) *)
(*                   (fun j => fst (Vector.nth (Vector.map (@projT1 _ _) ls) j)) *)
(*                   (fun k => Vector_nth_map2_r (@projT1 _ _) (fun x => RtlExpr (snd x)) ls k (projT2 (Vector.nth ls k)))). *)

(* Notation "'STRUCT' { s1 ; .. ; sN }" := *)
(*   (getStructVal (Vector.cons _ s1%rtl_init _ .. *)
(*                              (Vector.cons _ sN%rtl_init _ (Vector.nil _)) ..)) *)
(*   : rtl_expr_scope. *)

(* Local Ltac findStructIdx v f := *)
(*   let idx := eval cbv in (Vector_find (fun x => getBool (string_dec (fst x) f%string)) v) in *)
(*       exact idx. *)

(* Local Ltac getStructList fs f := match fs with *)
(*                                  | (fun i: Fin.t _ => *)
(*                                       fst (Vector.nth ?v i)) => *)
(*                                    findStructIdx v f *)
(*                                  | _ => let y := eval hnf in fs in *)
(*                                             getStructList y f *)
(*                                  end. *)

(* Local Ltac getStructStringFn v f := match v with *)
(*                                     | Struct ?fk ?fs => getStructList fs f *)
(*                                     | _ => let y := eval hnf in v in *)
(*                                                getStructStringFn y f *)
(*                                     end. *)

(* Local Ltac getStructFull v f := match v with *)
(*                                 | RtlExpr ?y => getStructStringFn y f *)
(*                                 | _ => let y := eval hnf in v in *)
(*                                            getStructFull y f *)
(*                                 end. *)



(* Notation "s @% f" := (RtlReadStruct s ltac:(let typeS := type of s in *)
(*                                             getStructFull typeS f)) (only parsing) *)
(*                      : rtl_expr_scope. *)

(* Local Definition testStruct := *)
(*   (STRUCT_TYPE { *)
(*        "hello" :: Bit 10 ; *)
(*        "a" :: Bit 3 ; *)
(*        "b" :: Bit 5 ; *)
(*        "test" :: Bool }). *)

(* Local Definition testStructVal: RtlExpr testStruct := *)
(*   (STRUCT { *)
(*        "hello" ::= RtlConst (natToWord _ 4) ; *)
(*        "a" ::= RtlConst (natToWord _ 23) ; *)
(*        "b" ::= RtlConst (natToWord _ 5) ; *)
(*        "test" ::= RtlConst true })%rtl_expr. *)

(* Local Definition testFieldAccess :=  *)
(*   (testStructVal @% "hello")%rtl_expr. *)
