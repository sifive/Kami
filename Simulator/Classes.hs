{-# LANGUAGE FlexibleInstances #-}

module Simulator.Classes where

import Control.Monad
import Data.Vector as V (Vector, (!), zipWith, fromList, toList, slice, (//), length)
import Data.Vector.Mutable as MV 
import Data.Array.IO
import Data.Array.MArray as MA
import qualified Data.Map.Strict as Map


{- classes -}

class StringMap m where
    empty_map :: m v
    map_lookup :: String -> m v -> Maybe v
    map_insert :: String -> v -> m v -> m v
    map_of_list :: [(String,v)] -> m v

map_inserts :: StringMap m => [(String,v)] -> m v -> m v
map_inserts ps m = foldr (\(k,v) m' -> map_insert k v m') m ps

class Functor v => Vec v where
    vector_index :: Int -> v a -> a
    vector_eq :: (a -> a -> Bool) -> v a -> v a -> Bool
    vector_of_list :: [a] -> v a
    list_of_vector :: v a -> [a]
    vector_slice :: Int {- starting index -} -> Int {- length -} -> v a -> v a
    vector_write :: v a -> Int -> a -> v a
    vector_length :: v a -> Int

vector_writes :: Vec v => [(Int,a)] -> v a -> v a
vector_writes ps v = foldr (\(i,x) v' -> vector_write v' i x) v ps

class Array arr where
    array_replicate :: Int -> a -> IO (arr a)
    array_slice :: Vec v => Int {- starting index -} -> Int {- length -} -> arr a -> IO (v a)
    array_write :: arr a -> Int -> a -> IO ()
    array_read :: Int -> arr a -> IO a
    array_length :: arr a -> IO Int

array_writes :: Array arr => [(Int,a)] -> arr a -> IO ()
array_writes ps v = forM_ ps (\(i,a) -> array_write v i a)

{- instances -}

newtype AssocList v = AssocList [(String,v)]

assoc_insert :: Eq a => a -> b -> [(a,b)] -> [(a,b)]
assoc_insert = go []

    where

        go acc x y [] = (x,y):acc
        go acc x y ((x',y'):rest) = if x == x' then ((x,y):acc) ++ rest else go ((x',y'):acc) x y rest

instance StringMap AssocList where
    empty_map = AssocList []
    map_lookup = \str (AssocList ps) -> lookup str ps
    map_insert = \str x (AssocList ps) -> AssocList (assoc_insert str x ps)
    map_of_list = AssocList

instance StringMap (Map.Map String) where
    empty_map = Map.empty
    map_lookup = Map.lookup
    map_insert = Map.insert
    map_of_list = Map.fromList


instance Vec Vector where
    vector_index = flip (!)
    vector_eq = \f a1 a2 -> foldr (&&) True $ V.zipWith f a1 a2
    vector_of_list = fromList
    list_of_vector = toList
    vector_slice = V.slice
    vector_write = \v i x -> v // [(i,x)]
    vector_length = V.length

ioarray_slice :: Vec v => Int -> Int -> IOArray Int a -> IO (v a)
ioarray_slice i m arr = do
    vals <- mapM (readArray arr) [i..(i+(m-1))]
    return $ vector_of_list vals

instance Array (IOArray Int) where
    array_replicate = \n x -> newArray (0,n-1) x
    array_slice = ioarray_slice
    array_write = writeArray
    array_read = flip readArray
    array_length = \a -> do
        (_,n) <- getBounds a
        return $ n + 1 

iovector_slice :: Vec v => Int -> Int -> IOVector a -> IO (v a)
iovector_slice i m arr = do
    vals <- mapM (MV.read arr) [i..(i+(m-1))]
    return $ vector_of_list vals

instance Array IOVector where
    array_replicate = MV.replicate
    array_slice = iovector_slice
    array_write = MV.write
    array_read = flip MV.read
    array_length = return . MV.length