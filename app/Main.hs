module Main (main, compSquareH, compSquareV) where

import Common
import Control.Exception
import Control.Monad
import ConversionModuloIsomorphism
import Data.ByteString qualified as BS
import Data.Time.Clock
import Examples
import Heuristic
import Isomorphism
import System.Environment
import Term

--------------------------------------------------------------------------------

main :: IO ()
main =
  getArgs >>= \case
    ["gen"] -> do
      let ts = everyNth 5000 $ map fst $ permute0 compSquareH
      BS.writeFile "bench.bin" (flat ts)
    ["gen-uncurried"] -> do
      let ts = everyNth 5000 $ map fst $ permute0 compSquareHUncurried
      BS.writeFile "bench-uncurried.bin" (flat ts)
    ["bench1"] -> do
      Right ts <- unflat @[Term] <$> BS.readFile "bench.bin"
      ts <- evaluate $ force ts
      (_, t) <- timed do
        let hits = map (not . null . convIso0 compSquareH) ts `using` parListChunk 128 rseq
        unless (and hits) $ error "bug in convIso0"
      print t
    ["bench2"] -> do
      Right ts <- unflat @[Term] <$> BS.readFile "bench.bin"
      ts <- evaluate $ force ts
      (_, t) <- timed do
        let hits = map (not . null . convIso0 compSquareV) ts `using` parListChunk 128 rseq
        when (or hits) $ error "bug in convIso0"
      print t
    ["bench3"] -> do
      Right ts <- unflat @[Term] <$> BS.readFile "bench.bin"
      ts <- evaluate $ force ts
      (_, t) <- timed do
        let match = refineConvIso0 compSquareH
            hits = map (not . null . match) ts `using` parListChunk 128 rseq
        unless (and hits) $ error "bug in refineConvIso0"
      print t
    ["bench4"] -> do
      Right ts <- unflat @[Term] <$> BS.readFile "bench.bin"
      ts <- evaluate $ force ts
      (_, t) <- timed do
        let match = refineConvIso0 compSquareV
            hits = map (not . null . match) ts `using` parListChunk 128 rseq
        when (or hits) $ error "bug in refineConvIso0"
      print t
    _ -> error "invalid argument"

timed :: IO a -> IO (a, NominalDiffTime)
timed a = do
  t1 <- getCurrentTime
  res <- a
  t2 <- getCurrentTime
  let diff = diffUTCTime t2 t1
  pure (res, diff)
{-# INLINE timed #-}
