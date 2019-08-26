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
import Simulator.UART

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

data ConsoleDevice = ConsoleDevice {
  console_uart :: IORef UART_NS16550A
}

mkConsoleDevice :: IO ConsoleDevice
mkConsoleDevice = do
  uart <- newIORef mkUART
  return $ ConsoleDevice uart   

console_read :: IO String
console_read = do
  putStrLn "[console_read]"
  console_has_input <- try (hReady stdin) :: IO (Either IOError Bool)
  case console_has_input of
    Left isEOFError -> return ""
    Right has_input
      -> if has_input
              then do
                putStrLn "[console_read] read input."
                b <- getChar
                bs <- console_read
                return (b : bs)
              else do
                putStrLn "[console_read] did not read any input."
                return ""

console_write :: IO ()
console_write = do
  putStrLn "[console_write]"
  

instance AbstractDevice ConsoleDevice where
  device_name console = "console"

  device_step console = do
    console_input <- console_read
    uart_state_init <- readIORef $ console_uart console
    let (console_output, uart_state_final) =
          uart_deq_output $ uart_enq_input uart_state_init console_input in do
      putStr console_output
      writeIORef (console_uart console) uart_state_final

  device_read console addr = do
    curr_console_uart <- readIORef $ console_uart console
    (result, next_console_uart) <- return $ uart_read curr_console_uart $ BV.nat $ bvCoerce addr
    writeIORef (console_uart console) next_console_uart
    return $ BVVal $ BV.bitVec 8 result -- every register is 1 byte wide.

  device_write console pkt = do
    curr_console_uart <- readIORef $ console_uart console
    writeIORef (console_uart console) $
      uart_write curr_console_uart
        (fromIntegral $ BV.nat $ bvCoerce $ struct_field_access "addr" pkt)
        (fromIntegral $ BV.nat $ bvCoerce $ struct_field_access "data" pkt) -- writes are single bytes
    return $ BVVal BV.nil 

  device_has_interrupt console = do
    console_uart <- readIORef $ console_uart console
    return $ uart_has_interrupt console_uart
