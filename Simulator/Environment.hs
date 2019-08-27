module Simulator.Environment where

import System.IO
import qualified Data.HashMap as M
import Simulator.RegisterFile
import Simulator.Print
import Simulator.Util
import Simulator.Value

class AbstractEnvironment a where
  envStep :: a -> FileState -> M.Map String Val -> IO a
