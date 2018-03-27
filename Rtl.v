Require Import Syntax String.

Set Implicit Arguments.
Set Asymmetric Patterns.

(* TODO
 * System Calls
 * Dealing with Register Files
 *)

Inductive RtlExpr: Kind -> Type :=
| RtlReadReg k: string -> RtlExpr k
| RtlReadWire k: (string * list nat) -> RtlExpr k
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

Inductive RtlSysT : Type :=
| RtlDispString : string -> RtlSysT
| RtlDispBool : RtlExpr Bool -> FullBitFormat -> RtlSysT
| RtlDispBit : forall n, RtlExpr (Bit n) -> FullBitFormat -> RtlSysT
| RtlDispStruct : forall n (fk : Fin.t n -> Kind) (fs : Fin.t n -> string),
    RtlExpr (Struct fk fs) -> (Fin.t n -> FullBitFormat) -> RtlSysT
| RtlDispArray : forall n k,
    RtlExpr (Array n k) -> FullBitFormat -> RtlSysT.


Record RtlModule :=
  { regFiles: list (string * list (string * bool) * string * sigT (fun x: (nat * Kind) => ConstT (Array (fst x) (snd x))));
    (* asyncRegFiles: list (string * list (string * bool) * string * sigT (fun x: (nat * Kind) => ConstT (Array (fst x) (snd x)))); *)
    (* syncRegFilesData: list (string * list (string * bool) * string * sigT (fun x: (nat * Kind) => ConstT (Array (fst x) (snd x)))); *)
    (* syncRegFilesAddr: list (string * list (string * bool) * string * sigT (fun x: (nat * Kind) => ConstT (Array (fst x) (snd x)))); *)
    inputs: list (string * list nat * Kind);
    outputs: list (string * list nat * Kind);
    regInits: list (string * sigT (fun x => ConstT x));
    regWrites: list (string * sigT RtlExpr);
    wires: list (string * list nat * sigT RtlExpr);
    sys: list (RtlExpr Bool * list RtlSysT)
  }.
