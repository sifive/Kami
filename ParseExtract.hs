
module ParseExtract where

import qualified Data.BitVector as BV
import qualified Data.Array.MArray as M
import qualified Data.Array.IO as A
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Data.Vector as V
import qualified Data.Char as C

import Simulator.Util
import Unsafe.Coerce


data Tok = Addr Integer | Value BV.BV deriving (Show)

readTok :: Int -> T.Text -> Tok
readTok n txt = let txt' = T.filter (/= '_') txt in
    case T.uncons txt' of
        Just ('@',addr) -> Addr $ hex_to_integer addr
        Just _ -> Value $ hex_to_bv n txt'
        Nothing -> error "Empty text chunk encountered."

toks_to_addr_vals :: [Tok] -> [(Integer, BV.BV)]
toks_to_addr_vals = go 0 where
    go _ [] = []
    go n ((Addr k):toks) = go k toks
    go n ((Value bs):toks) = (n,bs) : go (n+1) toks

getToks :: Int -> T.Text -> [(Integer, BV.BV)]
getToks n text = toks_to_addr_vals $ concat $ map ((map $ readTok n) . (filter (not . T.null)) . (T.split C.isSpace)) $ T.lines text

parseFile :: Int -> Int -> String -> a
parseFile size idxNum path = unsafeCoerce $ do
    text <- T.readFile path
    let pairs = getToks size text
    return $ (V.replicate idxNum 0) V.// (map (\(i,v) -> (fromIntegral i, v)) pairs)