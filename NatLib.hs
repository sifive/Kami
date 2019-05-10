module NatLib where

import qualified Prelude

mod2 :: Prelude.Int -> Prelude.Bool
mod2 n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> Prelude.False)
    (\n0 ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Prelude.True)
      (\n' -> mod2 n')
      n0)
    n

