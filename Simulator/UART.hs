-- Copyright (c) 2018-2019 Rishiyur S. Nikhil
-- See LICENSE for license details

module Simulator.UART where

-- ================================================================
-- This is (partial) model of the classic National Semiconductor NS16550A UART.
-- We model the main features: send/receive byte, send/receive interrupts, etc.
-- We do not modem control stuff (baud rates, parity, stop bits, line break, ...)
-- We do not model the 16-deep FIFO; instead we have unbounded fifos.

-- ================================================================
-- Standard Haskell imports

import qualified Data.Bits
import qualified Data.Char
import Data.Bits
import Data.Char

-- Project imports

-- none

-- ================================================================
-- UART registers and their relative addresses (8-byte stride)

addr_UART_rbr  = 0x00 :: Integer    -- receiver buffer register (read only)
addr_UART_thr  = 0x00 :: Integer    -- transmitter holding register (write only)
addr_UART_ier  = 0x08 :: Integer    -- interrupt enable register
addr_UART_iir  = 0x10 :: Integer    -- interrupt id register    (read-only)
addr_UART_lcr  = 0x18 :: Integer    -- line control reg
addr_UART_mcr  = 0x20 :: Integer    -- modem control reg
addr_UART_lsr  = 0x28 :: Integer    -- line status reg     (read-only)
addr_UART_msr  = 0x30 :: Integer    -- modem status reg    (read-only)
addr_UART_scr  = 0x38 :: Integer    -- scratch pad reg

-- Aliased registers, depending on control bits
addr_UART_dll  = 0x00 :: Integer    -- divisor latch low
addr_UART_dlm  = 0x08 :: Integer    -- divisor latch high
addr_UART_fcr  = 0x10 :: Integer    -- fifo control reg    (write-only)

-- Bit fields of ier (Interrupt Enable Register)
uart_ier_erbfi = 0x01 :: Integer     -- Enable Received Data Available Interrupt
uart_ier_etbei = 0x02 :: Integer     -- Enable Transmitter Holding Register Empty Interrupt
uart_ier_elsi  = 0x04 :: Integer     -- Enable Receiver Line Status Interrupt
uart_ier_edssi = 0x08 :: Integer     -- Enable Modem Status Interrupt

-- iir values (Interrupt Identification Register) in decreasing priority of interrupts
uart_iir_none  = 0x01 :: Integer     -- None (no interrupts pending)
uart_iir_rls   = 0x06 :: Integer     -- Receiver Line Status
uart_iir_rda   = 0x04 :: Integer     -- Received Data Available
uart_iir_cti   = 0x0C :: Integer     -- Character Timeout Indication
uart_iir_thre  = 0x02 :: Integer     -- Transmitter Holding Register Empty
uart_iir_ms    = 0x00 :: Integer     -- Modem Status

-- Bit fields of LCR
uart_lcr_dlab  = 0x80 :: Integer     -- Divisor latch access bit
uart_lcr_bc    = 0x40 :: Integer     -- Break control
uart_lcr_sp    = 0x20 :: Integer     -- Stick parity
uart_lcr_eps   = 0x10 :: Integer     -- Even parity
uart_lcr_pen   = 0x08 :: Integer     -- Parity enable
uart_lcr_stb   = 0x04 :: Integer     -- # of stop bits (0=1b,1=2b)
uart_lcr_wls   = 0x03 :: Integer     -- word len (0:5b,1:6b,2:7b,3:8b)

-- Bit fields of LSR
uart_lsr_rxfe  = 0x80 :: Integer    -- Receiver FIFO error
uart_lsr_temt  = 0x40 :: Integer    -- Transmitter empty
uart_lsr_thre  = 0x20 :: Integer    -- THR empty
uart_lsr_bi    = 0x10 :: Integer    -- Break interrupt
uart_lsr_fe    = 0x08 :: Integer    -- Framing Error
uart_lsr_pe    = 0x04 :: Integer    -- Parity Error
uart_lsr_oe    = 0x02 :: Integer    -- Overrun Error
uart_lsr_dr    = 0x01 :: Integer    -- Data Ready

-- ================================================================
-- UART representation
-- This is a private internal representation that can be changed at
-- will; only the exported API can be used by clients.

-- Note: for received data, for debugging we keep a log of everything received
--    rbr_a: characters received from tty and already read by the CPU.
--    rbr_b: characters received from tty but not yet consumed by the CPU.
--    The 16550's RBR register is logically the first char in rdr_b.
--    All input = rdr_a ++ rdr_b.

-- Note: for transmitted data, for debugging we keep a log of everything transmitted
--    thd_a: characters received from CPU and already sent to the tty.
--    thd_b: characters received from CPU but not yet sent to the tty.
--    The 16550's THD register is logically the first char in thd_b.
--    All output = thd_a ++ thd_b.

-- We represent each 8-bit UART registers with 'I'teger'
                                                                -- \begin_latex{UART_NS16550A}
data UART_NS16550A = UART_NS16550A {
  f_rbr_a :: String,
  f_rbr_b :: String,    -- 0    Read-only

  f_thr_a :: String,
  f_thr_b :: String,    -- 0    Write-only

  f_ier   :: Integer,     -- 1
                                                                -- \end_latex{...UART_NS16550A}

  -- f_iir   :: Integer,  -- 2    Virtual read-only field; computed from other fields on each read

  f_lcr   :: Integer,     -- 3
  f_mcr   :: Integer,     -- 4
  f_lsr   :: Integer,     -- 5    Read-only
  f_msr   :: Integer,     -- 6    Read-only
  f_scr   :: Integer,     -- 7


  -- Aliased registers, depending on control bits
  f_dll   :: Integer,    -- 0    if LCR.DLAB=1
  f_dlm   :: Integer,    -- 1    if LCR.DLAB=1

  f_fcr   :: Integer     -- 2    Write-only
  }

-- ================================================================
-- Create a UART
                                                                -- \begin_latex{mkUART}
mkUART :: UART_NS16550A
mkUART =  UART_NS16550A { f_rbr_a = "",
                          f_rbr_b = "",
                                                                -- \end_latex{...mkUART}
                          f_thr_a = "",
                          f_thr_b = "",

                          f_ier = 0,                   -- no interrupts enabled
                          -- f_iir = uart_iir_none,    -- virtual field, computed from other field on each read
                          f_lcr = 0,
                          f_mcr = 0,
                          f_lsr = (uart_lsr_temt .|. uart_lsr_thre),    -- transmitter empty
                          f_msr = 0,
                          f_scr = 0,

                          -- Aliased regs
                          f_dll = 0,
                          f_dlm = 0,
                          f_fcr = 0
                          }

-- ================================================================
-- Computing the virtual field 'i'r'

uart_read_iir :: UART_NS16550A -> Integer
uart_read_iir  uart =
  let
    ier  = f_ier  uart
    lsr  = f_lsr  uart
    iir  = if (   ((ier .&. uart_ier_erbfi) /= 0)    -- Enabled Rx buffer interrupt
               && ((lsr .&. uart_lsr_dr) /= 0)) then        -- Data ready
             uart_iir_rda    -- Receive Data Interrupt

           else if ((ier .&. uart_ier_etbei) /= 0) then    -- Enabled Tx Holding Register Empty interrupt
                  uart_iir_thre    -- THR empty interrupt

                else
                  0
  in
    iir

-- ================================================================
-- Check for interrupts

uart_has_interrupt :: UART_NS16550A -> Bool
uart_has_interrupt  uart =
  let
    iir = uart_read_iir  uart
    eip = ((iir .&. uart_iir_none) == 0)
  in
    eip

-- ================================================================
-- Read UART register (from CPU)
                                                                        -- \begin_latex{uart_read}
uart_read :: UART_NS16550A -> Integer -> (Integer, UART_NS16550A)
uart_read  uart  addr_offset =
                                                                        -- \end_latex{...uart_read}
  -- RBR (read-only)
  if ((addr_offset == addr_UART_rbr) && (((f_lcr  uart) .&. uart_lcr_dlab) == 0)) then
    let
      rbr_a = f_rbr_a  uart
      rbr_b = f_rbr_b  uart
      lsr   = f_lsr    uart
    in
      case (rbr_b) of
        []     -> (0, uart)    -- no input available; arbitrary 0
        (c:cs) -> (let
                      v      = fromIntegral (ord  c)
                      rbr_a' = rbr_a ++ [c]
                      rbr_b' = cs
                      lsr'   = if (rbr_b' == "") then
                                 (lsr .&. complement  uart_lsr_dr)    -- Reset data-ready to 0
                               else
                                 (lsr .|. uart_lsr_dr)                -- Ensure data-ready is 1
                      uart' = uart {f_rbr_a = rbr_a',
                                    f_rbr_b = rbr_b',
                                    f_lsr   = lsr'}
                   in
                     (v, uart'))

  -- IER
  else if ((addr_offset == addr_UART_ier) && (((f_lcr  uart) .&. uart_lcr_dlab) == 0)) then
    (f_ier  uart,  uart)


  else if (addr_offset == addr_UART_iir) then (uart_read_iir  uart,  uart)
  else if (addr_offset == addr_UART_lcr) then (f_lcr  uart,  uart)
  else if (addr_offset == addr_UART_mcr) then (f_mcr  uart,  uart)
  else if (addr_offset == addr_UART_lsr) then (f_lsr  uart,  uart)
  else if (addr_offset == addr_UART_msr) then (f_msr  uart,  uart)
  else if (addr_offset == addr_UART_scr) then (f_scr  uart,  uart)

  -- DLL (alias of RBR)
  else if ((addr_offset == addr_UART_dll) && (((f_lcr  uart) .&. uart_lcr_dlab) /= 0)) then
    (f_dll uart, uart)

  -- DLM (alias of IER)
  else if ((addr_offset == addr_UART_dlm) && (((f_lcr  uart) .&. uart_lcr_dlab) /= 0)) then
    (f_dlm uart, uart)

  else (0xFF,  uart)    -- Arbitrary 0xFF; TODO: raise an access fault

-- ================================================================
-- Write UART register (from CPU)

                                                                        -- \begin_latex{uart_write}
uart_write :: UART_NS16550A -> Integer -> Integer -> UART_NS16550A
uart_write  uart  addr_offset  val =
                                                                        -- \end_latex{...uart_write}
  -- THR (write-only)
  if ((addr_offset == addr_UART_thr) && (((f_lcr  uart) .&. uart_lcr_dlab) == 0)) then
    let
      char  = chr (fromIntegral val)
      thr_b = f_thr_b  uart
      uart' = uart { f_thr_b = thr_b ++ [char] }
    in
      uart'

  -- IER
  else if ((addr_offset == addr_UART_ier) && (((f_lcr  uart) .&. uart_lcr_dlab) == 0)) then
    uart { f_ier = (val .&. 0xFF) }

  -- FCR (write-only)
  else if (addr_offset == addr_UART_fcr) then uart { f_fcr = (val .&. 0xFF) }

  else if (addr_offset == addr_UART_lcr) then uart { f_lcr = (val .&. 0xFF) }
  else if (addr_offset == addr_UART_mcr) then uart { f_mcr = (val .&. 0xFF) }
  else if (addr_offset == addr_UART_lsr) then uart    -- LSR is read-only
  else if (addr_offset == addr_UART_msr) then uart    -- MSR is read-only
  else if (addr_offset == addr_UART_scr) then uart { f_scr = (val .&. 0xFF) }


  -- DLL ((alias of THR)
  else if ((addr_offset == addr_UART_dll) && (((f_lcr  uart) .&. uart_lcr_dlab) /= 0)) then
      uart { f_dll = (val .&. 0xFF) }
  -- DLL (alias of IER)
  else if ((addr_offset == addr_UART_dlm) && (((f_lcr  uart) .&. uart_lcr_dlab) /= 0)) then
      uart { f_dlm = (val .&. 0xFF) }

  else uart

-- ================================================================
-- System append input from console into UART,
-- set LSR.DR bit (line_status_reg.data_ready)


uart_enq_input :: UART_NS16550A -> String -> UART_NS16550A
uart_enq_input  uart  [] = uart
uart_enq_input  uart  s  =
  let
    rbr_b = f_rbr_b  uart
    lsr   = f_lsr    uart

    rbr_b' = rbr_b ++ s
    lsr'   = (lsr .|. uart_lsr_dr)    -- Data Ready bit in Line Status Reg

    uart'  = uart { f_rbr_b = rbr_b', f_lsr = lsr' }
  in
    uart'

-- ================================================================
-- System consume output from UART for output to console
-- We have "infinite" buffering, so THR is always "empty" and ready for the next char.

uart_deq_output :: UART_NS16550A -> (String, UART_NS16550A)
uart_deq_output  uart =
  let
    thr_b = f_thr_b  uart
  in
    case  thr_b  of
      [] -> ("", uart)
      cs -> (thr_b, uart {f_thr_a = (f_thr_a  uart) ++ thr_b,
                          f_thr_b = ""})

-- ================================================================
-- Read all UART input and output

uart_all_input :: UART_NS16550A -> (String, String)
uart_all_input  uart = ((f_rbr_a  uart),  (f_rbr_b  uart))

uart_all_output :: UART_NS16550A -> (String, String)
uart_all_output  uart = ((f_thr_a  uart), (f_thr_b  uart))

-- ================================================================
