module Specif where

import qualified Prelude

type Coq_sig a = a
  -- singleton inductive, whose constructor was exist
  
proj1_sig :: a1 -> a1
proj1_sig e =
  e

