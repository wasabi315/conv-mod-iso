module Common
  ( module Common,
    module Control.Parallel.Strategies,
    module Lens.Micro.Platform,
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

lookupSmallArray :: (Ord k) => k -> SmallArray (k, a) -> Maybe a
lookupSmallArray k xs = go 0
  where
    n = sizeofSmallArray xs
    go i
      | i == n = Nothing
      | (k', x) <- indexSmallArray xs i =
          case compare k k' of
            LT -> Nothing
            EQ -> Just x
            GT -> go (i + 1)
{-# INLINE lookupSmallArray #-}

insertSmallArrayWith ::
  (Ord k) =>
  (a -> a -> a) ->
  k ->
  a ->
  SmallArray (k, a) ->
  SmallArray (k, a)
insertSmallArrayWith f tok ~x xs = runSmallArray do
  let sz = sizeofSmallArray xs
      go i
        | i == sz = do
            ys <- newSmallArray (sz + 1) (tok, x)
            copySmallArray ys 0 xs 0 i
            pure ys
        | (tok', y) <- indexSmallArray xs i =
            case compare tok tok' of
              LT -> do
                ys <- newSmallArray (sz + 1) (tok, x)
                copySmallArray ys 0 xs 0 i
                copySmallArray ys (i + 1) xs i (sz - i)
                pure ys
              EQ -> do
                xs <- thawSmallArray xs 0 sz
                writeSmallArray xs i (tok, f x y)
                pure xs
              GT -> go (i + 1)

  go 0
{-# INLINE insertSmallArrayWith #-}

mergeSmallArrayWith ::
  (Ord k) =>
  (a -> a -> a) ->
  SmallArray (k, a) ->
  SmallArray (k, a) ->
  SmallArray (k, a)
mergeSmallArrayWith f xs ys = runSmallArray do
  let sz = sizeofSmallArray xs
      sz' = sizeofSmallArray ys
  zs <- newSmallArray (sz + sz') undefined

  let go i j k
        | i == sz = do
            copySmallArray zs k ys j (sz' - j)
            shrinkSmallMutableArray zs (k + sz' - j)
        | j == sz' = do
            copySmallArray zs k xs i (sz - i)
            shrinkSmallMutableArray zs (k + sz - i)
        | (# p@(tok, t) #) <- indexSmallArray## xs i,
          (# p'@(tok', t') #) <- indexSmallArray## ys j =
            case compare tok tok' of
              LT -> writeSmallArray zs k p >> go (i + 1) j (k + 1)
              EQ -> writeSmallArray zs k (tok, f t t') >> go (i + 1) (j + 1) (k + 1)
              GT -> writeSmallArray zs k p' >> go i (j + 1) (k + 1)

  go 0 0 0
  pure zs
{-# INLINE mergeSmallArrayWith #-}

-- more efficient than Traversable's mapAccumL
-- lazy in accumulator
mapAccumSmallArrayL_ :: (b -> a -> (b, c)) -> b -> SmallArray a -> SmallArray c
mapAccumSmallArrayL_ f z0 xs = do
  let sz = sizeofSmallArray xs
  createSmallArray sz undefined \ys -> do
    let go i ~z
          | i == sz = pure ()
          | (# x #) <- indexSmallArray## xs i,
            (z', y) <- f z x =
              writeSmallArray ys i y >> go (i + 1) z'
    go 0 z0
{-# INLINE mapAccumSmallArrayL_ #-}

-- Prelude's foldMap' doesn't inline
foldMap'' :: (Monoid m, Foldable t) => (a -> m) -> t a -> m
foldMap'' ~f = foldl' (\ ~acc ~a -> acc <> f a) mempty
{-# INLINE foldMap'' #-}

--------------------------------------------------------------------------------
-- Names

type Name = String

newtype Index = Index Int
  deriving stock (Generic)
  deriving newtype (Show, Ord, Eq, Num, Ix)
  deriving anyclass (NFData, Flat)

newtype Level = Level Int
  deriving newtype (Eq, Ord, Num, Show, Ix)
