{-# LANGUAGE ConstrainedClassMethods #-}

module Simulator.Environment where

import System.IO
import Simulator.RegisterFile
import Simulator.Print
import Simulator.Util
import Simulator.Value
import Simulator.Classes

class AbstractEnvironment e where
  envPre  :: (StringMap m, Array a, Vec v) => e -> FileState m a v -> m (Val v) -> String -> IO e
  envPost :: (StringMap m, Array a, Vec v) => e -> FileState m a v -> m (Val v) -> String -> IO e
