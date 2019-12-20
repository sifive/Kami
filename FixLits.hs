{-# LANGUAGE OverloadedStrings #-}

import qualified Data.Text as T
import qualified Data.Text.IO as T

import Data.Char (isSpace)
import System.Environment (getArgs)

import CustomExtract

data Tok =

    --text
      White T.Text
    | Txt T.Text
    | LParen
    | RParen

    --nats
    | Zero
    | Succ
    | NatLit Int

    --strings
    | Nil
    | Cons
    | Chr Char
    | CodeChr Int
    | StringLit T.Text

    --words
    | WNil
    | WCons
    | BoolLit Bool
    | WordLit EWord

    --fins
    | FZero
    | FSucc
    | FLit EFin

    --vectors
    | VNil
    | VCons
    | VecLit [T.Text]

    deriving (Show)

assert :: Bool -> Maybe ()
assert b = if b then Just () else Nothing

stripChar :: T.Text -> Maybe (Tok,T.Text)
stripChar txt = do
    (c,rest) <- T.uncons txt
    assert (c == '\'')
    (c',rest') <- T.uncons rest
    case c' of
        -- escape char
        '\\' -> do
            (c'',rest'') <- T.uncons rest'
            case c'' of
                -- tail removes the final single quote char
                '\'' -> return (Chr '\'', T.tail rest'')
                '\\' -> return (Chr '\\', T.tail rest'')
                --add more escape chars here as needed
                --at this point we know the character is '\xyz'
                _ -> let (x,y) = T.breakOn "\'" rest' in
                        return (CodeChr $ read $ T.unpack x, T.tail y)

                --add more escape chars here as needed
        _ -> return (Chr c', T.tail rest')

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
                        Nothing -> case T.stripPrefix "CustomExtract.wordNil" txt of
                            Just rest -> WNil : toks rest
                            Nothing -> case T.stripPrefix "CustomExtract.wordCons" txt of
                                Just rest -> WCons : toks rest
                                Nothing -> case T.stripPrefix "Prelude.True" txt of
                                    Just rest -> BoolLit True : toks rest
                                    Nothing -> case T.stripPrefix "Prelude.False" txt of
                                        Just rest -> BoolLit False : toks rest
                                        Nothing -> case T.stripPrefix "CustomExtract.fin0" txt of
                                            Just rest -> FZero : toks rest
                                            Nothing -> case T.stripPrefix "CustomExtract.finS" txt of
                                                Just rest -> FSucc : toks rest
                                                Nothing -> case T.stripPrefix "[]" txt of
                                                    Just rest -> Nil : toks rest
                                                    Nothing -> case stripChar txt of
                                                        Just (t,rest) -> t : (toks rest)
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

parse_word :: [Tok] -> Maybe ([Bool], [Tok])
parse_word ts = go [] ts where
    go bs (WCons:_:BoolLit b:rest) = do
        (n,rest') <- parse_nat rest
        go (b:bs) rest'
    go bs (WNil:rest) = Just (bs, drop_rps (length bs-1) rest)
    go bs ((White _):rest) = go bs rest
    go bs (LParen:rest) = go bs rest
    go bs (RParen:rest) = go bs rest
    go _ _ = Nothing

parse_fin :: [Tok] -> Maybe (EFin, [Tok])
parse_fin ts = go (0,0) ts where
    go x (FSucc:rest) = do
        (n,rest') <- parse_nat rest
        go (finS n x) rest'
    go x (FZero:_:LParen:rest) = do
        (n,rest') <- parse_nat rest
        let (k,i) = x
        return ((k+n,i), drop_rps (k+1) rest')
    go x (FZero:rest) = do
        (n,rest') <- parse_nat rest
        let (k,i) = x
        return ((k+n,i), drop_rps (k) rest')
    go x ((White _):rest) = go x rest
    go x (LParen:rest) = go x rest
    go x (RParen:rest) = go x rest
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
    (WCons:rest) -> case parse_word ts of
        Just (bs,rest') -> (WordLit $ foldr (\b (n,v) -> wordCons b n (n,v)) wordNil $ reverse bs) : fix_lits rest' 
        Nothing -> WCons : fix_lits rest
    (FSucc:rest) -> case parse_fin ts of
        Just (x,rest') -> (FLit x) : fix_lits rest'
        Nothing -> FSucc : fix_lits rest
    (t:rest) -> t : fix_lits rest

single_quotes :: Char -> T.Text
single_quotes c = T.cons '\'' $ T.cons c $ T.cons '\'' T.empty

single_quotes_txt :: T.Text -> T.Text
single_quotes_txt txt = T.cons '\'' $ T.append txt $ T.cons '\'' T.empty

double_quotes :: T.Text -> T.Text
double_quotes txt = T.cons '"' (T.snoc txt '"')

print_tok :: Tok -> T.Text
print_tok (White w) = w
print_tok (Txt t) = t
print_tok LParen = "("
print_tok RParen = ")"
print_tok Zero = "0"
print_tok Succ = "(Prelude.succ :: Prelude.Int -> Prelude.Int)"
print_tok Nil = "[]"
print_tok Cons = "(:)"
--print_tok (Chr '\000') = single_quotes_txt "\\000"
--print_tok (Chr '\001') = single_quotes_txt "\\001"
print_tok (CodeChr n) = single_quotes_txt (T.append "\\" $ T.pack $ show n)
print_tok (Chr c) = single_quotes c
print_tok (NatLit n) = T.pack $ show n
print_tok (StringLit str) = double_quotes str
print_tok WNil = "CustomExtract.wordNil"
print_tok WCons = "CustomExtract.wordCons"
print_tok (BoolLit b) = if b then "Prelude.True" else "Prelude.False"
print_tok (WordLit w) = T.pack $ show w
print_tok FZero = "CustomExtract.fin0"
print_tok FSucc = "CustomExtract.finS"
print_tok (FLit x) = T.pack $ show x

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



