module PeanoNat where

import qualified Prelude
import qualified Datatypes

_Nat__pred :: Prelude.Int -> Prelude.Int
_Nat__pred = (\n -> Prelude.max 0 (Prelude.pred n))

_Nat__compare :: Prelude.Int -> Prelude.Int -> Datatypes.Coq_comparison
_Nat__compare n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Datatypes.Eq)
      (\_ -> Datatypes.Lt)
      m)
    (\n' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Datatypes.Gt)
      (\m' -> _Nat__compare n' m')
      m)
    n

_Nat__divmod :: Prelude.Int -> Prelude.Int -> Prelude.Int -> Prelude.Int ->
                (,) Prelude.Int Prelude.Int
_Nat__divmod x y q u =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> (,) q u)
    (\x' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> _Nat__divmod x' y (Prelude.succ q) y)
      (\u' -> _Nat__divmod x' y q u')
      u)
    x

_Nat__div :: Prelude.Int -> Prelude.Int -> Prelude.Int
_Nat__div = (\n m -> if m Prelude.== 0 then 0 else Prelude.div n m)

_Nat__log2_iter :: Prelude.Int -> Prelude.Int -> Prelude.Int -> Prelude.Int
                   -> Prelude.Int
_Nat__log2_iter k p q r =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> p)
    (\k' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> _Nat__log2_iter k' (Prelude.succ p) (Prelude.succ q) q)
      (\r' -> _Nat__log2_iter k' p (Prelude.succ q) r')
      r)
    k

_Nat__log2 :: Prelude.Int -> Prelude.Int
_Nat__log2 n =
  _Nat__log2_iter (_Nat__pred n) 0 (Prelude.succ 0) 0

_Nat__div2 :: Prelude.Int -> Prelude.Int
_Nat__div2 n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> 0)
    (\n0 ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> 0)
      (\n' -> Prelude.succ (_Nat__div2 n'))
      n0)
    n

_Nat__log2_up :: Prelude.Int -> Prelude.Int
_Nat__log2_up a =
  case _Nat__compare (Prelude.succ 0) a of {
   Datatypes.Lt -> Prelude.succ (_Nat__log2 (_Nat__pred a));
   _ -> 0}

