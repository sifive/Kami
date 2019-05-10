module Datatypes where

import qualified Prelude

app :: (([]) a1) -> (([]) a1) -> ([]) a1
app l m =
  case l of {
   ([]) -> m;
   (:) a l1 -> (:) a (app l1 m)}

data Coq_comparison =
   Eq
 | Lt
 | Gt

id :: a1 -> a1
id x =
  x

