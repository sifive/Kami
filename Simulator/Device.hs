{-# LANGUAGE ExistentialQuantification #-}
module Simulator.Device where

import qualified Data.List

import qualified Data.HashMap as M
import qualified Data.Vector as V
import qualified Data.BitVector as BV

import Data.String
import Data.List (find)
import Data.Maybe (isJust, catMaybes)
import Control.Monad
import Data.IORef
import System.Exit
import System.IO
import System.Random (randomIO)
import System.Environment (getArgs)
import Text.Read
import Control.Exception
import System.IO
import Data.IORef
import Simulator.Value

class AbstractDevice a where
  device_name :: a -> String;
  device_step :: a -> IO ()
  device_read :: a -> Val -> IO Val
  device_write :: a -> Val -> IO Val
  device_has_interrupt :: a -> IO Bool

data Device = forall device. AbstractDevice device => Device device

instance AbstractDevice Device where
  device_name (Device device) = device_name device;
  device_step (Device device) = device_step device
  device_read (Device device) = device_read device
  device_write (Device device) = device_write device
  device_has_interrupt (Device device) = device_has_interrupt device
