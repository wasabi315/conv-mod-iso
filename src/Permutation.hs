{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Permutation
  ( PiGen,
    initPiGen,
    domChoices,
    DomChoice (..),
    SigmaGen,
    initSigmaGen,
    projChoices,
    ProjChoice (..),
  )
where

import Common
import Data.Bits
import Data.Primitive.PrimArray
import Data.Primitive.SmallArray
import Isomorphism
import Value

--------------------------------------------------------------------------------

pattern Placeholder :: Value
pattern Placeholder = VVar (-1)

-- | Free levels in @[from, to)@. The value is scoped at @to@.
levelsBetween :: Level -> Level -> Value -> Int
levelsBetween from to = go to
  where
    go l = \case
      VRigid x sp
        | from <= x && x < to -> setBit (goSpine l sp) (coerce (x - from))
        | otherwise -> goSpine l sp
      VTop _ sp -> goSpine l sp
      VU -> 0
      VPi _ a b -> go l a .|. go (l + 1) (b $ VVar l)
      VLam _ t -> go (l + 1) (t $ VVar l)
      VSigma _ a b -> go l a .|. go (l + 1) (b $ VVar l)
      VPair t u -> go l t .|. go l u

    goSpine l = \case
      SNil -> 0
      SApp sp u -> goSpine l sp .|. go l u
      SFst sp -> goSpine l sp
      SSnd sp -> goSpine l sp

--------------------------------------------------------------------------------
-- Generator of all dependency-respecting orders of a Pi telescope's domains

data PiGen = PiGen
  { original :: {-# UNPACK #-} VPiArg,
    -- dependency mask per original position
    depMasks :: {-# UNPACK #-} PrimArray Int,
    -- mask of not-yet-emitted positions
    remaining :: {-# UNPACK #-} Int,
    -- substitution per original position, placeholder elsewhere
    subst :: {-# UNPACK #-} SmallArray Value
  }

data DomChoice = DomChoice
  { name :: Name,
    dom :: VTyp,
    iso :: Iso,
    next :: Either (Value -> VTyp) (Value -> PiGen)
  }

initPiGen :: Level -> VPiArg -> PiGen
initPiGen l (VPiArg x a b) =
  PiGen
    { original = VPiArg x a b,
      depMasks = deps,
      remaining = (1 `unsafeShiftL` sz) - 1,
      subst = runSmallArray (newSmallArray sz Placeholder)
    }
  where
    deps = primArrayFromList $ 0 : depMasks (l + 1) (b $ VVar l)
    sz = sizeofPrimArray deps

    depMasks l' = \case
      VPi _ a b -> levelsBetween l l' a : depMasks (l' + 1) (b $ VVar l')
      _ -> []

domChoices :: PiGen -> [DomChoice]
domChoices PiGen {..} = unfoldr' step (0, orig)
  where
    sz = sizeofPrimArray depMasks
    orig = case original of VPiArg x a b -> VPi x a b

    step (!i, t)
      | i >= sz = Done
      | testBit remaining i,
        (indexPrimArray depMasks i .&. remaining) == 0 = do
          let remaining' = clearBit remaining i
              iso = piSwaps $ popCount (remaining .&. (bit i - 1))
              next
                | remaining' == 0 = Left \ ~w -> do
                    let subst' = updateSmallArray i w subst
                    finalCod original subst'
                | otherwise = Right \ ~w -> do
                    let subst' = updateSmallArray i w subst
                    PiGen {remaining = remaining', subst = subst', ..}
              VPi name dom b = t
              (# v #) = indexSmallArray## subst i
          Yield DomChoice {..} (i + 1, b v)
      | otherwise = do
          let VPi _ _ b = t
              (# v #) = indexSmallArray## subst i
          Skip (i + 1, b v)
{-# INLINE domChoices #-}

finalCod :: VPiArg -> SmallArray Value -> VTyp
finalCod (VPiArg x a b) subst = foldl' step (VPi x a b) subst
  where
    step (VPi _ _ b) v = b v
    step _ _ = error "impossible"
{-# INLINE finalCod #-}

piSwaps :: Int -> Iso
piSwaps = \case
  0 -> Refl
  n -> go (n - 1)
  where
    go = \case
      0 -> PiSwap
      n -> PiCongR (go (n - 1)) `Trans` PiSwap

--------------------------------------------------------------------------------

data SigmaGen = SigmaGen
  { original :: {-# UNPACK #-} VSigmaArg,
    -- dependency mask per original position
    depMasks :: {-# UNPACK #-} PrimArray Int,
    -- mask of not-yet-emitted positions
    remaining :: {-# UNPACK #-} Int,
    -- substitution per original position, placeholder elsewhere
    subst :: {-# UNPACK #-} SmallArray Value
  }

data ProjChoice = ProjChoice
  { name :: Name,
    proj1 :: VTyp,
    iso :: Iso,
    next :: Either (Value -> VTyp) (Value -> SigmaGen)
  }

initSigmaGen :: Level -> VSigmaArg -> SigmaGen
initSigmaGen l (VSigmaArg x a b) = do
  SigmaGen
    { original = VSigmaArg x a b,
      depMasks = deps,
      remaining = (1 `unsafeShiftL` sz) - 1,
      subst = runSmallArray (newSmallArray (sz - 1) Placeholder) -- beware -1!
    }
  where
    deps = primArrayFromList $ 0 : depMasks (l + 1) (b $ VVar l)
    sz = sizeofPrimArray deps

    depMasks l' = \case
      VSigma _ a b -> levelsBetween l l' a : depMasks (l' + 1) (b $ VVar l')
      a -> [levelsBetween l l' a]

projChoices :: SigmaGen -> [ProjChoice]
projChoices SigmaGen {..} = unfoldr' step (0, orig)
  where
    sz = sizeofPrimArray depMasks
    orig = case original of VSigmaArg x a b -> VSigma x a b

    bind i w sub
      | i < sizeofSmallArray sub = updateSmallArray i w sub
      | otherwise = sub
    {-# INLINE bind #-}

    step (!i, t)
      | i >= sz = Done
      | testBit remaining i,
        (indexPrimArray depMasks i .&. remaining) == 0 = do
          let remaining' = clearBit remaining i
              iso =
                sigmaSwaps
                  (if i == sz - 1 then Comm else SigmaSwap)
                  (popCount (remaining .&. (bit i - 1)))
              next
                | popCount remaining' <= 1 = Left \ ~w -> do
                    let subst' = bind i w subst
                    finalProj original subst' (countTrailingZeros remaining')
                | otherwise = Right \ ~w -> do
                    let subst' = bind i w subst
                    SigmaGen {remaining = remaining', subst = subst', ..}
          case t of
            VSigma name proj1 b
              | (# v #) <- indexSmallArray## subst i -> Yield ProjChoice {..} (i + 1, b v)
            proj1 -> Yield ProjChoice {name = "_", ..} (i + 1, error "impossible")
      | otherwise = case t of
          VSigma _ _ b
            | (# v #) <- indexSmallArray## subst i -> Skip (i + 1, b v)
          _ -> Skip (i + 1, error "impossible")
{-# INLINE projChoices #-}

finalProj :: VSigmaArg -> SmallArray Value -> Int -> VTyp
finalProj (VSigmaArg x a b) subst j =
  either id id $ ifoldlSmallArrayM' step (VSigma x a b) subst
  where
    step i t v = case t of
      VSigma _ a b
        | i == j -> Left a
        | otherwise -> Right (b v)
      _ -> error "impossible"
{-# INLINE finalProj #-}

sigmaSwaps :: Iso -> Int -> Iso
sigmaSwaps last = \case
  0 -> Refl
  n -> go (n - 1)
  where
    go = \case
      0 -> last
      n -> SigmaCongR (go (n - 1)) `Trans` SigmaSwap
