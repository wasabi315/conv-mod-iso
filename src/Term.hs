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

data PiArg = PiArg Name Typ Typ

data SigmaArg = SigmaArg Name Typ Typ

instance HasField "_1" Term Term where
  getField = Fst
  {-# INLINE getField #-}

instance HasField "_2" Term Term where
  getField = Snd
  {-# INLINE getField #-}