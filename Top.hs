module Top where

import qualified Prelude
import qualified Syntax
import qualified Tutorial

coq_IncrMod :: Syntax.BaseModule
coq_IncrMod =
  Tutorial.coq_IncrementerImpl ((:) 't' ((:) 'e' ((:) 's' ((:) 't' ([])))))

