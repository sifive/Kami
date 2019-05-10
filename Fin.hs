module Fin where

import qualified Prelude

data Coq_t =
   F1 Prelude.Int
 | FS Prelude.Int Coq_t

to_nat :: Prelude.Int -> Coq_t -> Prelude.Int
to_nat _ n =
  case n of {
   F1 _ -> 0;
   FS n0 p -> Prelude.succ (to_nat n0 p)}

