module Main (main, compSquareH, compSquareV) where

import Common
import Control.Exception
import Control.Monad
import ConversionModuloIsomorphism
import Data.ByteString qualified as BS
import Data.Time.Clock
import Evaluation
import Heuristic
import Isomorphism
import System.Environment
import Term
import Value

--------------------------------------------------------------------------------

main :: IO ()
main =
  getArgs >>= \case
    ["gen"] -> do
      let ts = everyNth 5000 $ map fst $ normalisePermute0 compSquareH
      BS.writeFile "bench.bin" (flat ts)
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

everyNth :: Int -> [a] -> [a]
everyNth n xs
  | n <= 0 = []
  | otherwise = case drop (n - 1) xs of
      y : ys -> y : everyNth n ys
      [] -> []

compSquareH :: Term
compSquareH = quote 0 $
  VPi "A" VU \a ->
    VPi "a00" a \a00 -> VPi "a01" a \a01 -> VPi "a02" a \a02 ->
      VPi "a10" a \a10 -> VPi "a11" a \a11 -> VPi "a12" a \a12 ->
        VPi "a0_" ("Eq" $$ a $$ a00 $$ a01) \a0_ ->
          VPi "b0_" ("Eq" $$ a $$ a01 $$ a02) \b0_ ->
            VPi "a1_" ("Eq" $$ a $$ a10 $$ a11) \a1_ ->
              VPi "b1_" ("Eq" $$ a $$ a11 $$ a12) \b1_ ->
                VPi "a_0" ("Eq" $$ a $$ a00 $$ a10) \a_0 ->
                  VPi "a_1" ("Eq" $$ a $$ a01 $$ a11) \a_1 ->
                    VPi "a_2" ("Eq" $$ a $$ a02 $$ a12) \a_2 ->
                      ("Square" $$ a $$ a0_ $$ a1_ $$ a_0 $$ a_1)
                        --> ("Square" $$ a $$ b0_ $$ b1_ $$ a_1 $$ a_2)
                        --> ( "Square"
                                $$ a
                                $$ ("compPath" $$ a $$ a00 $$ a01 $$ a02 $$ a0_ $$ b0_)
                                $$ ("compPath" $$ a $$ a10 $$ a11 $$ a12 $$ a1_ $$ b1_)
                                $$ a_0
                                $$ a_2
                            )

compSquareV :: Term
compSquareV = quote 0 $
  VPi "A" VU \a ->
    VPi "a00" a \a00 -> VPi "a01" a \a01 ->
      VPi "a10" a \a10 -> VPi "a11" a \a11 ->
        VPi "a20" a \a20 -> VPi "a21" a \a21 ->
          VPi "a0_" ("Eq" $$ a $$ a00 $$ a01) \a0_ ->
            VPi "a1_" ("Eq" $$ a $$ a10 $$ a11) \a1_ ->
              VPi "a2_" ("Eq" $$ a $$ a20 $$ a21) \a2_ ->
                VPi "a_0" ("Eq" $$ a $$ a00 $$ a10) \a_0 ->
                  VPi "a_1" ("Eq" $$ a $$ a01 $$ a11) \a_1 ->
                    VPi "b_0" ("Eq" $$ a $$ a10 $$ a20) \b_0 ->
                      VPi "b_1" ("Eq" $$ a $$ a11 $$ a21) \b_1 ->
                        ("Square" $$ a $$ a0_ $$ a1_ $$ a_0 $$ a_1)
                          --> ("Square" $$ a $$ a1_ $$ a2_ $$ b_0 $$ b_1)
                          --> ( "Square"
                                  $$ a
                                  $$ a0_
                                  $$ a2_
                                  $$ ("compPath" $$ a $$ a00 $$ a10 $$ a20 $$ a_0 $$ b_0)
                                  $$ ("compPath" $$ a $$ a01 $$ a11 $$ a21 $$ a_1 $$ b_1)
                              )
