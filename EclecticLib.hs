module EclecticLib where

import qualified Prelude
import qualified Fin

getFins :: Prelude.Int -> ([]) Fin.Coq_t
getFins n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> ([]))
    (\m -> (:) (Fin.F1 m) (Prelude.map (\x -> Fin.FS m x) (getFins m)))
    n

