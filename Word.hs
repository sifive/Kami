module Word where

import qualified Prelude
import qualified NatLib
import qualified PeanoNat

data Coq_word =
   WO
 | WS Prelude.Bool Prelude.Int Coq_word

natToWord :: Prelude.Int -> Prelude.Int -> Coq_word
natToWord sz n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> WO)
    (\sz' -> WS (NatLib.mod2 n) sz'
    (natToWord sz' (PeanoNat._Nat__div2 n)))
    sz

wzero :: Prelude.Int -> Coq_word
wzero sz =
  natToWord sz 0

