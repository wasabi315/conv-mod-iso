module Common
  ( module Common,
    module Control.Parallel.Strategies,
    module Lens.Micro.Platform,
    module GHC.Records,
    coerce,
    force,
    Flat,
    flat,
    unflat,
    Generic,
  )
where

import Control.DeepSeq
import Control.Parallel.Strategies
import Data.Coerce
import Data.Generics.Labels ()
import Data.Ix
import Data.Primitive.SmallArray
import Flat
import GHC.Exts
import GHC.Records
import Lens.Micro.Platform

--------------------------------------------------------------------------------
-- Utils

infix 2 //

-- strict pair construction
(//) :: a -> b -> (a, b)
a // b = (a, b)
{-# INLINE (//) #-}

concatMapParIf :: Bool -> Strategy [b] -> (a -> [b]) -> [a] -> [b]
concatMapParIf par strat =
  if par
    then \f -> concat . parMap strat f
    else concatMap
{-# INLINE concatMapParIf #-}

updateSmallArray :: Int -> a -> SmallArray a -> SmallArray a
updateSmallArray i ~x xs = runSmallArray do
  ys <- thawSmallArray xs 0 (sizeofSmallArray xs)
  writeSmallArray ys i x
  pure ys
{-# INLINE updateSmallArray #-}

ifoldrSmallArray :: (Int -> a -> b -> b) -> b -> SmallArray a -> b
ifoldrSmallArray f z arr = do
  let sz = sizeofSmallArray arr
      go i
        | i == sz = z
        | (# x #) <- indexSmallArray## arr i = f i x (go (i + 1))
  go 0
{-# INLINE ifoldrSmallArray #-}

everyNth :: Int -> [a] -> [a]
everyNth n xs
  | n <= 0 = []
  | otherwise = case drop (n - 1) xs of
      y : ys -> y : everyNth n ys
      [] -> []

-- Prelude's foldMap' doesn't inline
foldMap'' :: (Monoid m, Foldable t) => (a -> m) -> t a -> m
foldMap'' f = foldl' (\acc ~a -> acc <> f a) mempty
{-# INLINE foldMap'' #-}

data Step a b
  = Done
  | Yield ~a b
  | Skip b

unfoldr' :: (b -> Step a b) -> b -> [a]
unfoldr' f b0 = build \ ~c ~n -> do
  let go b = case f b of
        Done -> n
        Yield a b -> a `c` go b
        Skip b -> go b
  go b0
{-# INLINE unfoldr' #-}

--------------------------------------------------------------------------------
-- Names

type Name = String

newtype Index = Index Int
  deriving stock (Generic)
  deriving newtype (Show, Ord, Eq, Num, Ix)
  deriving anyclass (NFData, Flat)

newtype Level = Level Int
  deriving newtype (Eq, Ord, Num, Show, Ix, Enum, Bounded)
