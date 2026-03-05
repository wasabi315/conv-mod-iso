module Common
  ( module Common,
    module Flat,
    module Control.Parallel.Strategies,
    coerce,
    force,
  )
where

import Control.Applicative
import Control.DeepSeq
import Control.Parallel.Strategies
import Data.Coerce
import Data.Monoid
import Flat

--------------------------------------------------------------------------------
-- Utils

infix 2 //

-- strict pair construction
(//) :: a -> b -> (a, b)
a // b = (a, b)
{-# INLINE (//) #-}

foldMapA :: (Alternative f, Foldable t) => (a -> f b) -> t a -> f b
foldMapA f = getAlt . foldMap (Alt . f)
{-# INLINE foldMapA #-}

foldMapAParIf :: (Alternative f) => Bool -> Strategy (f b) -> (a -> f b) -> [a] -> f b
foldMapAParIf par strat f xs =
  if par
    then asum $ parMap strat f xs
    else foldMapA f xs
{-# INLINE foldMapAParIf #-}

--------------------------------------------------------------------------------
-- Names

type Name = String

newtype Index = Index Int
  deriving stock (Generic)
  deriving newtype (Show, Ord, Eq, Num)
  deriving anyclass (NFData, Flat)

newtype Level = Level Int
  deriving newtype (Eq, Ord, Num, Show)
