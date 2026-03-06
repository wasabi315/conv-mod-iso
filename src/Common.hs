module Common
  ( module Common,
    module Flat,
    module Control.Parallel.Strategies,
    coerce,
    force,
  )
where

import Control.DeepSeq
import Control.Parallel.Strategies
import Data.Coerce
import Flat

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

--------------------------------------------------------------------------------
-- Names

type Name = String

newtype Index = Index Int
  deriving stock (Generic)
  deriving newtype (Show, Ord, Eq, Num)
  deriving anyclass (NFData, Flat)

newtype Level = Level Int
  deriving newtype (Eq, Ord, Num, Show)
