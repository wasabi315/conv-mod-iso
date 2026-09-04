module Main (main) where

import Common
import ConversionModuloIsomorphism
import Data.ByteString qualified as BS
import Examples
import Heuristic
import Isomorphism
import Term
import Test.Tasty (withResource)
import Test.Tasty.Bench
import Test.Tasty.Patterns.Printer (printAwkExpr)

--------------------------------------------------------------------------------

main :: IO ()
main =
  defaultMain
    [ withResource (readBenchData "bench.bin") (const $ pure ()) \m -> do
        bgroup "bench.bin" [suite "curried" m],
      withResource (readBenchData "bench-uncurried.bin") (const $ pure ()) \m -> do
        bgroup "bench-uncurried.bin" [suite "uncurried" m]
    ]

suite :: String -> IO [Term] -> Benchmark
suite name ts =
  bgroup
    name
    [ bgroup
        "convIso"
        [ bench "match" $ whnfIO (countHits (convIso0 compSquareH) <$> ts),
          bench "no-match" $ whnfIO (countHits (convIso0 compSquareV) <$> ts)
        ],
      bgroup
        "refineConvIso"
        [ versus ["match", "convIso", name] $
            bench "match" $
              whnfIO (countHits (refineConvIso0 compSquareH) <$> ts),
          versus ["no-match", "convIso", name] $
            bench "no-match" $
              whnfIO (countHits (refineConvIso0 compSquareV) <$> ts)
        ]
    ]

versus :: [String] -> Benchmark -> Benchmark
versus names = bcompare (printAwkExpr (locateBenchmark names))

readBenchData :: FilePath -> IO [Term]
readBenchData path = do
  Right ts <- unflat @[Term] <$> BS.readFile path
  pure $ everyNth 20 ts -- take too long so subsample!

countHits :: (Term -> [Iso]) -> [Term] -> Int
countHits f = foldl' (\n t -> if null (f t) then n else n + 1) 0
