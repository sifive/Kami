module DepEqNat where

import qualified Prelude
import qualified Datatypes

nat_cast :: Prelude.Int -> Prelude.Int -> a1 -> a1
nat_cast n m x =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Datatypes.id x)
      (\_ -> Prelude.error "absurd case")
      m)
    (\n0 ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Prelude.error "absurd case")
      (\m0 -> nat_cast n0 m0 x)
      m)
    n

