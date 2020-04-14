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

import Simulator.Classes
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

word_of_bv :: BV.BV -> Integer
word_of_bv = BV.nat

toks_to_addr_vals :: [Tok] -> [(Integer, BV.BV)]
toks_to_addr_vals = go 0 where
    go _ [] = []
    go n ((Addr k):toks) = go k toks
    go n ((Value bs):toks) = (n,bs) : go (n+1) toks

getToks :: Int -> T.Text -> [(Integer, BV.BV)]
getToks n text = toks_to_addr_vals $ concat $ map ((map $ readTok n) . (filter (not . T.null)) . (T.split isSpace)) $ T.lines text

-- expr_of_bv :: Vec v => BV.BV -> H.Expr (Val v)
-- expr_of_bv v = H.Const (H.Bit $ BV.size v) $ H.ConstBit (BV.size v) $ word_of_bv v

val_unpack :: Vec v => H.Kind -> BV.BV -> Val v 
val_unpack H.Bool v = BoolVal $ v BV.@. 0
val_unpack (H.Bit _) v = BVVal v
val_unpack (H.Array n k) v =
    ArrayVal $ vector_of_list $ map (val_unpack k) $ BV.split n v
val_unpack (H.Struct n kinds names) v =
    let names' = map names $ H.getFins n in
    let kinds' = map kinds $ H.getFins n in
    let bvs = partition (map H.size kinds') v in
    StructVal $ zip names' $ zipWith val_unpack kinds' bvs

parseHex :: (Array a, Vec v) => Bool -> H.Kind -> Int -> FilePath -> IO (a (Val v))
parseHex isAscii k arrSize filepath
    | isAscii = do
        text <- T.readFile filepath
        let pairs = getToks (H.size k) text
        let v = defVal k
        v_init <- array_replicate arrSize v
        let val_pairs = map (\(i,v) -> (fromIntegral i, val_unpack k v)) pairs
        array_writes val_pairs v_init
        return v_init
    | otherwise = error "Binary not yet supported."
