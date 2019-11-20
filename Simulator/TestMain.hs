
--module TestMain where

import qualified TestTarget as T

import Simulator.All

import Data.IORef
import qualified Data.HashMap as M

test :: ([T.RegFileBase], T.BaseModule)
test = snd (T.separateModRemove T.testNativeMod)

instance AbstractEnvironment () where
    envPre _ _ _ _ = return ()
    envPost _ _ _ _ = return ()

main :: IO()
main = do
    e <- newIORef ()
    simulate_module 0 user_rules e (map fst $ T.getRules (snd test)) [] (fst test) (snd test)
    return ()