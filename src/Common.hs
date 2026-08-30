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
import Data.Monoid
import Data.Primitive.SmallArray
import Flat
import GHC.Exts
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

insertSmallArray :: (Ord k, Semigroup a) => k -> a -> SmallArray (k, a) -> SmallArray (k, a)
insertSmallArray tok ~x xs = runSmallArray do
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
                writeSmallArray xs i (tok, x <> y)
                pure xs
              GT -> go (i + 1)

  go 0
{-# INLINEABLE insertSmallArray #-}

insertSmallArrayR :: forall k a. (Ord k, Semigroup a) => k -> a -> SmallArray (k, a) -> SmallArray (k, a)
insertSmallArrayR = coerce (insertSmallArray @k @(Dual a))
{-# INLINE insertSmallArrayR #-}

mergeSmallArray :: (Ord k, Semigroup a) => SmallArray (k, a) -> SmallArray (k, a) -> SmallArray (k, a)
mergeSmallArray xs ys = runSmallArray do
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
              EQ -> writeSmallArray zs k (tok, t <> t') >> go (i + 1) (j + 1) (k + 1)
              GT -> writeSmallArray zs k p' >> go i (j + 1) (k + 1)

  go 0 0 0
  pure zs
{-# INLINEABLE mergeSmallArray #-}

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
  deriving newtype (Eq, Ord, Num, Show, Ix)
