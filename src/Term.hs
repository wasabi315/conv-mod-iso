module Term where

import Common

--------------------------------------------------------------------------------
-- Terms

data Term
  = Var Index
  | Top Name
  | U
  | Pi Name Term Term
  | Lam Name Term
  | Term :$$ Term
  | Sigma Name Term Term
  | Pair Term Term
  | Fst Term
  | Snd Term
  deriving stock (Show, Generic)
  deriving anyclass (NFData, Flat)
