module Nat where

import qualified Prelude

sub :: Prelude.Int -> Prelude.Int -> Prelude.Int
sub = (\n m -> Prelude.max 0 (n Prelude.- m))

