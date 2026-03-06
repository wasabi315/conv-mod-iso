module Term where

import Common

--------------------------------------------------------------------------------
-- Terms

data Term
  = Var Index
  | Top Name
  | U
  | Pi Name Typ Typ
  | Lam Name Term
  | Term :$$ Term
  | Sigma Name Typ Typ
  | Pair Term Term
  | Fst Term
  | Snd Term
  deriving stock (Show, Generic)
  deriving anyclass (NFData, Flat)

type Typ = Term
