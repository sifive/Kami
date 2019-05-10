module HaskellTarget (module Syntax, module Word, module Fin, module EclecticLib, module PeanoNat, kami_model) where

import EclecticLib
import PeanoNat
import Fin
import Instance
import Syntax hiding (unsafeCoerce)
import Word

kami_model :: (([Syntax.RegFileBase] , Syntax.BaseModule) , Int)
kami_model = (kami_model32, 32)
