{-# LANGUAGE OverloadedStrings #-}

import qualified Data.Text as T
import qualified Data.Text.IO as T

import Data.Char (isSpace)
import System.Environment (getArgs)

data Tok = White T.Text | Txt T.Text | LParen | RParen | Zero | Succ | Nil | Cons | Chr Char | NatLit Int | StringLit T.Text
    deriving (Show)

assert :: Bool -> Maybe ()
assert b = if b then Just () else Nothing

stripChar :: T.Text -> Maybe (Char,T.Text)
stripChar txt = do
    (c,rest) <- T.uncons txt
    assert (c == '\'')
    let (chr,rest') = T.breakOn "'" rest
    return $ if T.head chr == '\\' then case T.index chr 1 of
    --    'n' -> ('\n', T.tail rest')
    --    't' -> ('\t', T.tail rest')
        '\\' -> ('\\', T.tail rest')
        '\'' -> ('\'', T.tail rest')

        else (T.head chr, T.tail rest')

toks :: T.Text -> [Tok]
toks txt
    | T.null txt = []
    | otherwise = case T.stripPrefix "(:)" txt of
        Just rest -> Cons : toks rest
        Nothing -> case T.stripPrefix "(" txt of
            Just rest -> LParen : toks rest
            Nothing -> case T.stripPrefix ")" txt of
                Just rest -> RParen : toks rest
                Nothing -> case T.stripPrefix "0" txt of
                    Just rest -> Zero : toks rest
                    Nothing -> case T.stripPrefix "Prelude.succ" txt of
                        Just rest -> Succ : toks rest
                        Nothing -> case T.stripPrefix "[]" txt of
                            Just rest -> Nil : toks rest
                            Nothing -> case stripChar txt of
                                Just (c,rest) -> (Chr c) : (toks rest)
                                Nothing -> case isSpace $ T.head txt of
                                    True -> let (white,rest) = T.span isSpace txt in (White white) : toks rest
                                    False -> let (txt',rest) = T.span (\c -> not $ isSpace c && c /= '(' && c /= ')') txt in (Txt txt') : toks rest

drop_rps :: Int -> [Tok] -> [Tok]
drop_rps n ts 
    | n <= 0 = ts
    | otherwise = case ts of
        (White _:us) -> drop_rps n us
        (RParen:us) -> drop_rps (n-1) us

parse_nat :: [Tok] -> Maybe (Int, [Tok])
parse_nat ts = go 0 ts where
    go n (Succ:rest) = go (n+1) rest
    go n (Zero:rest) = Just (n, drop_rps (n-1) rest)
    go n ((White _):rest) = go n rest
    go n (LParen:rest) = go n rest
    go _ _ = Nothing

parse_string :: [Tok] -> Maybe (T.Text, [Tok])
parse_string ts = go T.empty ts where
    go acc (Cons:_:(Chr c):rest) = go (T.snoc acc c) rest
    go acc (Nil:rest) = Just (acc, drop_rps (T.length acc) rest)
    go acc ((White _):rest) = go acc rest
    go acc (LParen:rest) = go acc rest
    go _ _ = Nothing

fix_lits :: [Tok] -> [Tok]
fix_lits ts = case ts of
    [] -> []
    (Succ:rest) -> case parse_nat ts of
        Just (n,rest') -> (NatLit n) : fix_lits rest'
        Nothing -> Succ : fix_lits rest
    (Cons:rest) -> case parse_string ts of
        Just (txt,rest') -> (StringLit txt) : fix_lits rest'
        Nothing -> Cons : fix_lits rest
    (t:rest) -> t : fix_lits rest

single_quotes :: Char -> T.Text
single_quotes c = T.cons '\'' $ T.cons c $ T.cons '\'' T.empty

double_quotes :: T.Text -> T.Text
double_quotes txt = T.cons '"' (T.snoc txt '"')

print_tok :: Tok -> T.Text
print_tok (White w) = w
print_tok (Txt t) = t
print_tok LParen = "("
print_tok RParen = ")"
print_tok Zero = "0"
print_tok Succ = "Prelude.succ"
print_tok Nil = "[]"
print_tok Cons = "(:)"
print_tok (Chr c) = single_quotes c
print_tok (NatLit n) = T.pack $ show n
print_tok (StringLit str) = double_quotes str

-- foomain :: IO()
-- foomain = do
--     string <- T.readFile "foo.hs"
--     putStrLn $ show $ toks string

main :: IO()
main = do
    (fileIn:_) <- getArgs
    txt <- T.readFile fileIn
    T.writeFile fileIn $ T.concat $ map print_tok $ fix_lits $ toks txt
    --T.writeFile fileOut T.empty



