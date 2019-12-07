{-# LANGUAGE Strict #-}

module Simulator.Parse where

import qualified HaskellTarget as H

import qualified Data.BitVector as BV
import qualified Data.Array.MArray as M
import qualified Data.Array.IO as A
import qualified Data.Text as T
import qualified Data.Text.IO as T

import Control.Monad
import Data.Text.Read (hexadecimal)

import Simulator.Util
import Simulator.Value

import Data.Char (isSpace)

data Tok = Addr Integer | Value BV.BV deriving (Show)

readTok :: Int -> T.Text -> Tok
readTok n txt = let txt' = T.filter (/= '_') txt in
    case T.uncons txt' of
        Just ('@',addr) -> Addr $ hex_to_integer addr
        Just _ -> Value $ hex_to_bv n txt'
        Nothing -> error "Empty text chunk encountered."

getToks :: Int -> T.Text -> [(Integer, BV.BV)]
getToks n text = toks_to_addr_vals $ concat $ map ((map $ readTok n) . (filter (not . T.null)) . (T.split isSpace)) $ T.lines text

word_of_bv :: BV.BV -> (Int,Integer)
word_of_bv v = (BV.size v, BV.nat v)

expr_of_bv :: BV.BV -> H.Expr Val
expr_of_bv v = H.Const (H.Bit $ BV.size v) $ H.ConstBit (BV.size v) $ word_of_bv v

toks_to_addr_vals :: [Tok] -> [(Integer, BV.BV)]
toks_to_addr_vals = go 0 where
    go _ [] = []
    go n ((Addr k):toks) = go k toks
    go n ((Value bs):toks) = (n,bs) : go (n+1) toks

val_unpack :: H.Kind -> BV.BV -> IO Val
val_unpack H.Bool v = return $ BoolVal $ v BV.@. 0
val_unpack (H.Bit _) v = return $ BVVal v
val_unpack (H.Array n k) v = do
    vs <- mapM (val_unpack k) $ BV.split n v
    liftM ArrayVal $ M.newListArray (0,n-1) vs
val_unpack (H.Struct n kinds names) v =
    let names' = map names $ H.getFins n in
    let kinds' = map kinds $ H.getFins n in
    let bvs = partition (map H.size kinds') v in do
        ps <- pair_sequence $ zip names' (zipWith val_unpack kinds' bvs)
        return $ StructVal ps

parseHex :: Bool -> H.Kind -> Int -> FilePath -> IO (A.IOArray Int Val)
parseHex isAscii k arrSize filepath
    | isAscii = do
        text <- T.readFile filepath
        let pairs = getToks (H.size k) text
        v <- defVal k
        v_init <- M.newArray (0,arrSize-1) v
        val_pairs <- pair_sequence $ map (\(i,v) -> (fromIntegral i, val_unpack k v)) pairs
        do_writes v_init val_pairs
        return v_init
    | otherwise = error "Binary not yet supported."
