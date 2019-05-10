{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Syntax where

import qualified Prelude
import qualified Datatypes
import qualified DepEqNat
import qualified Fin
import qualified Nat
import qualified PeanoNat
import qualified Specif
import qualified Word

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
type Any = GHC.Base.Any
#else
-- HUGS
type Any = ()
#endif

data Kind =
   Bool
 | Bit Prelude.Int
 | Struct Prelude.Int (Fin.Coq_t -> Kind) (Fin.Coq_t -> Prelude.String)
 | Array Prelude.Int Kind

data FullKind =
   SyntaxKind Kind
 | NativeKind

data ConstT =
   ConstBool Prelude.Bool
 | ConstBit Prelude.Int Word.Coq_word
 | ConstStruct Prelude.Int (Fin.Coq_t -> Kind) (Fin.Coq_t -> Prelude.String) 
 (Fin.Coq_t -> ConstT)
 | ConstArray Prelude.Int Kind (Fin.Coq_t -> ConstT)

data ConstFullT =
   SyntaxConst Kind ConstT
 | NativeConst Any

getDefaultConst :: Kind -> ConstT
getDefaultConst k =
  case k of {
   Bool -> ConstBool Prelude.False;
   Bit n -> ConstBit n (Word.wzero n);
   Struct n fk fs -> ConstStruct n fk fs (\i -> getDefaultConst (fk i));
   Array n k0 -> ConstArray n k0 (\_ -> getDefaultConst k0)}

data UniBoolOp =
   Neg

data CABoolOp =
   And
 | Or
 | Xor

data UniBitOp =
   Inv Prelude.Int
 | TruncLsb Prelude.Int Prelude.Int
 | TruncMsb Prelude.Int Prelude.Int
 | UAnd Prelude.Int
 | UOr Prelude.Int
 | UXor Prelude.Int

data BinBitOp =
   Sub Prelude.Int
 | Div Prelude.Int
 | Rem Prelude.Int
 | Sll Prelude.Int Prelude.Int
 | Srl Prelude.Int Prelude.Int
 | Sra Prelude.Int Prelude.Int
 | Concat Prelude.Int Prelude.Int

data CABitOp =
   Add
 | Mul
 | Band
 | Bor
 | Bxor

type BinBitBoolOp =
  Prelude.Int
  -- singleton inductive, whose constructor was LessThan
  
type Coq_fullType ty = Any

data Expr ty =
   Var FullKind (Coq_fullType ty)
 | Const Kind ConstT
 | UniBool UniBoolOp (Expr ty)
 | CABool CABoolOp (([]) (Expr ty))
 | UniBit Prelude.Int Prelude.Int UniBitOp (Expr ty)
 | CABit Prelude.Int CABitOp (([]) (Expr ty))
 | BinBit Prelude.Int Prelude.Int Prelude.Int BinBitOp (Expr ty) (Expr ty)
 | BinBitBool Prelude.Int Prelude.Int BinBitBoolOp (Expr ty) (Expr ty)
 | ITE FullKind (Expr ty) (Expr ty) (Expr ty)
 | Eq Kind (Expr ty) (Expr ty)
 | ReadStruct Prelude.Int (Fin.Coq_t -> Kind) (Fin.Coq_t -> Prelude.String) 
 (Expr ty) Fin.Coq_t
 | BuildStruct Prelude.Int (Fin.Coq_t -> Kind) (Fin.Coq_t -> Prelude.String) 
 (Fin.Coq_t -> Expr ty)
 | ReadArray Prelude.Int Kind (Expr ty) (Expr ty)
 | ReadArrayConst Prelude.Int Kind (Expr ty) Fin.Coq_t
 | BuildArray Prelude.Int Kind (Fin.Coq_t -> Expr ty)

castBits :: Prelude.Int -> Prelude.Int -> (Expr a1) -> Expr a1
castBits =
  DepEqNat.nat_cast

coq_ConstExtract :: Prelude.Int -> Prelude.Int -> Prelude.Int -> (Expr 
                    a1) -> Expr a1
coq_ConstExtract lsb n msb e =
  UniBit ((Prelude.+) lsb n) n (TruncMsb lsb n) (UniBit
    ((Prelude.+) ((Prelude.+) lsb n) msb) ((Prelude.+) lsb n) (TruncLsb
    ((Prelude.+) lsb n) msb) e)

sumSizes :: Prelude.Int -> (Fin.Coq_t -> Prelude.Int) -> Prelude.Int
sumSizes n x =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> 0)
    (\m -> (Prelude.+) (sumSizes m (\x0 -> x (Fin.FS m x0))) (x (Fin.F1 m)))
    n

size :: Kind -> Prelude.Int
size k =
  case k of {
   Bool -> Prelude.succ 0;
   Bit n -> n;
   Struct n fk _ -> sumSizes n (\i -> size (fk i));
   Array n k0 -> (Prelude.*) n (size k0)}

concatStructExpr :: Prelude.Int -> (Fin.Coq_t -> Prelude.Int) -> (Fin.Coq_t
                    -> Expr a1) -> Expr a1
concatStructExpr n sizes f =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> Const (Bit 0) (ConstBit 0 Word.WO))
    (\m -> BinBit (sizes (Fin.F1 m)) (sumSizes m (\x -> sizes (Fin.FS m x)))
    ((Prelude.+) (sumSizes m (\x -> sizes (Fin.FS m x))) (sizes (Fin.F1 m)))
    (Concat (sizes (Fin.F1 m)) (sumSizes m (\x -> sizes (Fin.FS m x))))
    (f (Fin.F1 m))
    (concatStructExpr m (\x -> sizes (Fin.FS m x)) (\x -> f (Fin.FS m x))))
    n

pack :: Kind -> (Expr a1) -> Expr a1
pack k e =
  case k of {
   Bool -> ITE (SyntaxKind (Bit (Prelude.succ 0))) e (Const (Bit
    (Prelude.succ 0)) (ConstBit (Prelude.succ 0) (Word.WS Prelude.True 0
    Word.WO))) (Const (Bit (Prelude.succ 0)) (ConstBit (Prelude.succ 0)
    (Word.WS Prelude.False 0 Word.WO)));
   Bit _ -> e;
   Struct n fk fs ->
    concatStructExpr n (\i -> size (fk i)) (\i ->
      pack (fk i) (ReadStruct n fk fs e i));
   Array n k0 ->
    let {
     help i =
       (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
         (\_ -> Const (Bit 0) (ConstBit 0 Word.WO))
         (\m ->
         castBits ((Prelude.+) ((Prelude.*) m (size k0)) (size k0))
           ((Prelude.*) (Prelude.succ m) (size k0)) (BinBit (size k0)
           ((Prelude.*) m (size k0))
           ((Prelude.+) ((Prelude.*) m (size k0)) (size k0)) (Concat
           (size k0) ((Prelude.*) m (size k0)))
           (pack k0 (ReadArray n k0 e (Const (Bit (PeanoNat._Nat__log2_up n))
             (ConstBit (PeanoNat._Nat__log2_up n)
             (Word.natToWord (PeanoNat._Nat__log2_up n) m))))) (help m)))
         i}
    in help n}

sumSizesMsbs :: Prelude.Int -> Fin.Coq_t -> (Fin.Coq_t -> Prelude.Int) ->
                Prelude.Int
sumSizesMsbs _ i x =
  case i of {
   Fin.F1 _ -> 0;
   Fin.FS m f ->
    (Prelude.+) (sumSizesMsbs m f (\j -> x (Fin.FS m j))) (x (Fin.F1 m))}

unpack :: Kind -> (Expr a1) -> Expr a1
unpack k e =
  case k of {
   Bool -> Eq (Bit (size Bool)) e (Const (Bit (Prelude.succ 0)) (ConstBit
    (Prelude.succ 0) (Word.WS Prelude.True 0 Word.WO)));
   Bit _ -> e;
   Struct n fk fs -> BuildStruct n fk fs (\i ->
    unpack (fk i)
      (coq_ConstExtract
        (Nat.sub (sumSizes n (\j -> size (fk j)))
          ((Prelude.+) (sumSizesMsbs n i (\j -> size (fk j))) (size (fk i))))
        (size (fk i)) (sumSizesMsbs n i (\j -> size (fk j)))
        (castBits (sumSizes n (\j -> size (fk j)))
          ((Prelude.+)
            ((Prelude.+)
              (Nat.sub (sumSizes n (\j -> size (fk j)))
                ((Prelude.+) (sumSizesMsbs n i (\j -> size (fk j)))
                  (size (fk i)))) (size (fk i)))
            (sumSizesMsbs n i (\j -> size (fk j)))) e)));
   Array n k0 -> BuildArray n k0 (\i ->
    unpack k0
      (coq_ConstExtract
        ((Prelude.*) (Specif.proj1_sig (Fin.to_nat n i)) (size k0))
        (let {
          size0 k1 =
            case k1 of {
             Bool -> Prelude.succ 0;
             Bit n0 -> n0;
             Struct n0 fk _ -> sumSizes n0 (\i0 -> size0 (fk i0));
             Array n0 k2 -> (Prelude.*) n0 (size0 k2)}}
         in size0 k0)
        (Nat.sub
          ((Prelude.*) n
            (let {
              size0 k1 =
                case k1 of {
                 Bool -> Prelude.succ 0;
                 Bit n0 -> n0;
                 Struct n0 fk _ -> sumSizes n0 (\i0 -> size0 (fk i0));
                 Array n0 k2 -> (Prelude.*) n0 (size0 k2)}}
             in size0 k0))
          ((Prelude.+)
            ((Prelude.*) (Specif.proj1_sig (Fin.to_nat n i))
              (let {
                size0 k1 =
                  case k1 of {
                   Bool -> Prelude.succ 0;
                   Bit n0 -> n0;
                   Struct n0 fk _ -> sumSizes n0 (\i0 -> size0 (fk i0));
                   Array n0 k2 -> (Prelude.*) n0 (size0 k2)}}
               in size0 k0))
            (let {
              size0 k1 =
                case k1 of {
                 Bool -> Prelude.succ 0;
                 Bit n0 -> n0;
                 Struct n0 fk _ -> sumSizes n0 (\i0 -> size0 (fk i0));
                 Array n0 k2 -> (Prelude.*) n0 (size0 k2)}}
             in size0 k0)))
        (castBits
          ((Prelude.*) n
            (let {
              size0 k1 =
                case k1 of {
                 Bool -> Prelude.succ 0;
                 Bit n0 -> n0;
                 Struct n0 fk _ -> sumSizes n0 (\i0 -> size0 (fk i0));
                 Array n0 k2 -> (Prelude.*) n0 (size0 k2)}}
             in size0 k0))
          ((Prelude.+)
            ((Prelude.+)
              ((Prelude.*) (Specif.proj1_sig (Fin.to_nat n i))
                (let {
                  size0 k1 =
                    case k1 of {
                     Bool -> Prelude.succ 0;
                     Bit n0 -> n0;
                     Struct n0 fk _ -> sumSizes n0 (\i0 -> size0 (fk i0));
                     Array n0 k2 -> (Prelude.*) n0 (size0 k2)}}
                 in size0 k0))
              (let {
                size0 k1 =
                  case k1 of {
                   Bool -> Prelude.succ 0;
                   Bit n0 -> n0;
                   Struct n0 fk _ -> sumSizes n0 (\i0 -> size0 (fk i0));
                   Array n0 k2 -> (Prelude.*) n0 (size0 k2)}}
               in size0 k0))
            (Nat.sub
              ((Prelude.*) n
                (let {
                  size0 k1 =
                    case k1 of {
                     Bool -> Prelude.succ 0;
                     Bit n0 -> n0;
                     Struct n0 fk _ -> sumSizes n0 (\i0 -> size0 (fk i0));
                     Array n0 k2 -> (Prelude.*) n0 (size0 k2)}}
                 in size0 k0))
              ((Prelude.+)
                ((Prelude.*) (Specif.proj1_sig (Fin.to_nat n i))
                  (let {
                    size0 k1 =
                      case k1 of {
                       Bool -> Prelude.succ 0;
                       Bit n0 -> n0;
                       Struct n0 fk _ -> sumSizes n0 (\i0 -> size0 (fk i0));
                       Array n0 k2 -> (Prelude.*) n0 (size0 k2)}}
                   in size0 k0))
                (let {
                  size0 k1 =
                    case k1 of {
                     Bool -> Prelude.succ 0;
                     Bit n0 -> n0;
                     Struct n0 fk _ -> sumSizes n0 (\i0 -> size0 (fk i0));
                     Array n0 k2 -> (Prelude.*) n0 (size0 k2)}}
                 in size0 k0)))) e)))}

data BitFormat =
   Binary
 | Decimal
 | Hex

data FullFormat =
   FBool Prelude.Int BitFormat
 | FBit Prelude.Int Prelude.Int BitFormat
 | FStruct Prelude.Int (Fin.Coq_t -> Kind) (Fin.Coq_t -> Prelude.String) 
 (Fin.Coq_t -> FullFormat)
 | FArray Prelude.Int Kind FullFormat

fullFormatHex :: Kind -> FullFormat
fullFormatHex k =
  case k of {
   Bool -> FBool (Prelude.succ 0) Hex;
   Bit n -> FBit n
    (PeanoNat._Nat__div n (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ 0))))) Hex;
   Struct n fk fs -> FStruct n fk fs (\i -> fullFormatHex (fk i));
   Array n k0 -> FArray n k0 (fullFormatHex k0)}

fullFormatBinary :: Kind -> FullFormat
fullFormatBinary k =
  case k of {
   Bool -> FBool (Prelude.succ 0) Binary;
   Bit n -> FBit n n Binary;
   Struct n fk fs -> FStruct n fk fs (\i -> fullFormatBinary (fk i));
   Array n k0 -> FArray n k0 (fullFormatBinary k0)}

fullFormatDecimal :: Kind -> FullFormat
fullFormatDecimal k =
  case k of {
   Bool -> FBool (Prelude.succ 0) Decimal;
   Bit n -> FBit n 0 Decimal;
   Struct n fk fs -> FStruct n fk fs (\i -> fullFormatDecimal (fk i));
   Array n k0 -> FArray n k0 (fullFormatDecimal k0)}

data SysT ty =
   DispString Prelude.String
 | DispExpr Kind (Expr ty) FullFormat
 | Finish

data ActionT ty =
   MCall Prelude.String ((,) Kind Kind) (Expr ty) (ty -> ActionT ty)
 | LetExpr FullKind (Expr ty) ((Coq_fullType ty) -> ActionT ty)
 | LetAction Kind (ActionT ty) (ty -> ActionT ty)
 | ReadNondet FullKind ((Coq_fullType ty) -> ActionT ty)
 | ReadReg Prelude.String FullKind ((Coq_fullType ty) -> ActionT ty)
 | WriteReg Prelude.String FullKind (Expr ty) (ActionT ty)
 | IfElse (Expr ty) Kind (ActionT ty) (ActionT ty) (ty -> ActionT ty)
 | Assertion (Expr ty) (ActionT ty)
 | Sys (([]) (SysT ty)) (ActionT ty)
 | Return (Expr ty)

type Action = () -> ActionT Any

type Signature = (,) Kind Kind

type MethodT = () -> Any -> ActionT Any

type RegInitValT = Prelude.Maybe ConstFullT

type RegInitT = (,) Prelude.String ((,) FullKind RegInitValT)

type DefMethT = (,) Prelude.String ((,) Signature MethodT)

type RuleT = (,) Prelude.String Action

data RegFileInitT =
   RFNonFile (Prelude.Maybe ConstT)
 | RFFile Prelude.Bool Prelude.Bool Prelude.String (Fin.Coq_t -> ConstT)

data SyncRead =
   Build_SyncRead Prelude.String Prelude.String Prelude.String

readReqName :: SyncRead -> Prelude.String
readReqName s =
  case s of {
   Build_SyncRead readReqName0 _ _ -> readReqName0}

readResName :: SyncRead -> Prelude.String
readResName s =
  case s of {
   Build_SyncRead _ readResName0 _ -> readResName0}

readRegName :: SyncRead -> Prelude.String
readRegName s =
  case s of {
   Build_SyncRead _ _ readRegName0 -> readRegName0}

data RegFileReaders =
   Async (([]) Prelude.String)
 | Sync Prelude.Bool (([]) SyncRead)

data RegFileBase =
   Build_RegFileBase Prelude.Bool Prelude.Int Prelude.String RegFileReaders 
 Prelude.String Prelude.Int Kind RegFileInitT

rfIsWrMask :: RegFileBase -> Prelude.Bool
rfIsWrMask r =
  case r of {
   Build_RegFileBase rfIsWrMask0 _ _ _ _ _ _ _ -> rfIsWrMask0}

rfNum :: RegFileBase -> Prelude.Int
rfNum r =
  case r of {
   Build_RegFileBase _ rfNum0 _ _ _ _ _ _ -> rfNum0}

rfDataArray :: RegFileBase -> Prelude.String
rfDataArray r =
  case r of {
   Build_RegFileBase _ _ rfDataArray0 _ _ _ _ _ -> rfDataArray0}

rfRead :: RegFileBase -> RegFileReaders
rfRead r =
  case r of {
   Build_RegFileBase _ _ _ rfRead0 _ _ _ _ -> rfRead0}

rfWrite :: RegFileBase -> Prelude.String
rfWrite r =
  case r of {
   Build_RegFileBase _ _ _ _ rfWrite0 _ _ _ -> rfWrite0}

rfIdxNum :: RegFileBase -> Prelude.Int
rfIdxNum r =
  case r of {
   Build_RegFileBase _ _ _ _ _ rfIdxNum0 _ _ -> rfIdxNum0}

rfData :: RegFileBase -> Kind
rfData r =
  case r of {
   Build_RegFileBase _ _ _ _ _ _ rfData0 _ -> rfData0}

rfInit :: RegFileBase -> RegFileInitT
rfInit r =
  case r of {
   Build_RegFileBase _ _ _ _ _ _ _ rfInit0 -> rfInit0}

data BaseModule =
   BaseRegFile RegFileBase
 | BaseMod (([]) RegInitT) (([]) RuleT) (([]) DefMethT)

data ModuleElt =
   MERegister RegInitT
 | MERegAry (([]) RegInitT)
 | MERule ((,) Prelude.String Action)
 | MEMeth DefMethT

data InModule =
   NilInModule
 | ConsInModule ModuleElt InModule

makeModule' :: InModule -> (,)
               ((,) (([]) RegInitT) (([]) ((,) Prelude.String Action)))
               (([]) DefMethT)
makeModule' im =
  case im of {
   NilInModule -> (,) ((,) ([]) ([])) ([]);
   ConsInModule e i ->
    case makeModule' i of {
     (,) p imeths ->
      case p of {
       (,) iregs irules ->
        case e of {
         MERegister mreg -> (,) ((,) ((:) mreg iregs) irules) imeths;
         MERegAry mregs -> (,) ((,) (Datatypes.app mregs iregs) irules)
          imeths;
         MERule mrule -> (,) ((,) iregs ((:) mrule irules)) imeths;
         MEMeth mmeth -> (,) ((,) iregs irules) ((:) mmeth imeths)}}}}

makeModule :: InModule -> BaseModule
makeModule im =
  case makeModule' im of {
   (,) p meths -> case p of {
                   (,) regs rules -> BaseMod regs rules meths}}

makeConst :: Kind -> ConstT -> ConstFullT
makeConst k c =
  SyntaxConst k c

