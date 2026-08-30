{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module PiGenerator
  ( PiGen,
    initPiGen,
    domChoices,
    DomChoice (..),
  )
where

import Common
import Data.Bits
import Data.IntSet qualified as IS
import Data.Primitive.PrimArray
import Data.Primitive.SmallArray
import Isomorphism
import Value

--------------------------------------------------------------------------------
-- Generator of all dependency-respecting orders of a Pi telescope's domains

data PiGen = PiGen
  { original :: {-# UNPACK #-} VPiArg,
    -- dependency mask per original position
    depMasks :: {-# UNPACK #-} PrimArray Int,
    -- mask of not-yet-emitted positions
    remaining :: Int,
    -- substitution per original position, placeholder elsewhere
    subst :: {-# UNPACK #-} SmallArray Value
  }

data DomChoice = DomChoice
  { name :: Name,
    dom :: VTyp,
    cod :: Value -> VTyp,
    iso :: Iso,
    next :: Maybe (Value -> PiGen)
  }

initPiGen :: Level -> VPiArg -> PiGen
initPiGen l (VPiArg x a b) = do
  let deps = primArrayFromList $ 0 : depMasks (l + 1) (b $ VVar l)
  PiGen
    { original = VPiArg x a b,
      depMasks = deps,
      remaining = (1 `unsafeShiftL` sizeofPrimArray deps) - 1,
      subst = runSmallArray (newSmallArray (sizeofPrimArray deps) Placeholder)
    }
  where
    depMasks l' = \case
      VPi _ a b -> do
        let mask = depMask l' a
        mask : depMasks (l' + 1) (b $ VVar l')
      _ -> []

    depMask l' =
      IS.foldl'
        (\mask x -> setBit mask (x - coerce l))
        (0 :: Int)
        . levelsBetween l l'

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
              iso = swaps $ popCount (remaining .&. (bit i - 1))
              cod ~w = do
                let subst' = updateSmallArray i w subst
                currentCod original subst'
              next
                | remaining' == 0 = Nothing
                | otherwise = Just \ ~w -> do
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

currentCod :: VPiArg -> SmallArray Value -> VTyp
currentCod (VPiArg x a b) subst = foldr step id subst (VPi x a b)
  where
    step v k = \case
      VPi y a b
        | Placeholder <- v -> VPi y a \ ~w -> k (b w)
        | otherwise -> k (b v)
      _ -> error "impossible"
{-# INLINE currentCod #-}

pattern Placeholder :: Value
pattern Placeholder = VVar (-1)

swaps :: Int -> Iso
swaps 0 = Refl
swaps n = go (n - 1)
  where
    go 0 = PiSwap
    go n = PiCongR (go (n - 1)) `Trans` PiSwap

-- | Free levels in @[from, to)@. The value is scoped at @to@.
levelsBetween :: Level -> Level -> Value -> IS.IntSet
levelsBetween from to = go to
  where
    go l = \case
      VRigid x sp ->
        ( if from <= x && x < to
            then IS.singleton (coerce x)
            else mempty
        )
          <> goSpine l sp
      VTop _ sp -> goSpine l sp
      VU -> mempty
      VPi _ a b -> go l a <> go (l + 1) (b $ VVar l)
      VLam _ t -> go (l + 1) (t $ VVar l)
      VSigma _ a b -> go l a <> go (l + 1) (b $ VVar l)
      VPair t u -> go l t <> go l u

    goSpine l = \case
      SNil -> mempty
      SApp sp u -> goSpine l sp <> go l u
      SFst sp -> goSpine l sp
      SSnd sp -> goSpine l sp
