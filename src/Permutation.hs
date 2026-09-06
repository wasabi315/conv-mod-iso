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
import Evaluation
import Isomorphism
import Term
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
  { names :: {-# UNPACK #-} SmallArray Name,
    -- quoted domains weakened to the same context as cod
    doms :: {-# UNPACK #-} SmallArray Term,
    cod :: Term,
    -- constitute closures together with each element of doms and cod
    env :: SmallArray Value,
    level :: Level,
    -- dependency mask per original position
    depMasks :: {-# UNPACK #-} PrimArray Int,
    -- mask of not-yet-emitted positions
    remaining :: {-# UNPACK #-} Int
  }

data DomChoice = DomChoice
  { name :: Name,
    dom :: VTyp,
    iso :: Iso,
    next :: Either (Value -> VTyp) (Value -> PiGen)
  }

initPiGen :: Level -> VPiArg -> PiGen
initPiGen level (VPiArg x a b) = go level id id id (VPi x a b)
  where
    go l nameAcc domAcc depsAcc = \case
      VPi x a b ->
        go
          (l + 1)
          (nameAcc . (x :))
          (domAcc . (a :))
          (depsAcc . (levelsBetween level l a :))
          (b (VVar l))
      a -> do
        let Level n = l - level
            names = smallArrayFromListN n (nameAcc [])
            doms = smallArrayFromListN n (map (quote l) (domAcc []))
            cod = quote l a
            env = runSmallArray (newSmallArray n Placeholder)
            depMasks = primArrayFromListN n (depsAcc [])
            remaining = bit n - 1
        PiGen {..}

domChoices :: PiGen -> [DomChoice]
domChoices PiGen {..} = unfoldr' step 0
  where
    n = sizeofSmallArray doms

    step !i
      | i >= n = Done
      | testBit remaining i,
        (indexPrimArray depMasks i .&. remaining) == 0 = do
          let remaining' = clearBit remaining i
              iso = piSwaps $ popCount (remaining .&. (bit i - 1))
              (# name #) = indexSmallArray## names i
              dom = eval (level :>> env) (indexSmallArray doms i)
              next
                | remaining' == 0 = Left \ ~v -> do
                    let env' = updateSmallArray (n - i - 1) v env
                    eval (level :>> env') cod
                | otherwise = Right \ ~v -> do
                    let env' = updateSmallArray (n - i - 1) v env
                    PiGen {remaining = remaining', env = env', ..}
          Yield DomChoice {..} (i + 1)
      | otherwise = Skip (i + 1)
{-# INLINE domChoices #-}

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
  { names :: {-# UNPACK #-} SmallArray Name,
    -- quoted projections weakened to the same context as the last projection
    projs :: {-# UNPACK #-} SmallArray Term,
    -- constitute closures together with each element of projs
    env :: SmallArray Value,
    level :: Level,
    -- dependency mask per original position
    depMasks :: {-# UNPACK #-} PrimArray Int,
    -- mask of not-yet-emitted positions
    remaining :: {-# UNPACK #-} Int
  }

data ProjChoice = ProjChoice
  { name :: Name,
    proj :: VTyp,
    iso :: Iso,
    next :: Either (Value -> VTyp) (Value -> SigmaGen)
  }

initSigmaGen :: Level -> VSigmaArg -> SigmaGen
initSigmaGen level (VSigmaArg x a b) = go level id id id (VSigma x a b)
  where
    go l nameAcc projAcc depsAcc = \case
      VSigma x a b ->
        go
          (l + 1)
          (nameAcc . (x :))
          (projAcc . (a :))
          (depsAcc . (levelsBetween level l a :))
          (b (VVar l))
      a -> do
        let Level n = l - level
            names = smallArrayFromListN (n + 1) (nameAcc ["_"])
            projs = smallArrayFromListN (n + 1) (map (quote l) (projAcc [a]))
            env = runSmallArray (newSmallArray n Placeholder)
            depMasks = primArrayFromListN (n + 1) (depsAcc [levelsBetween level l a])
            remaining = bit (n + 1) - 1
        SigmaGen {..}

projChoices :: SigmaGen -> [ProjChoice]
projChoices SigmaGen {..} = unfoldr' step 0
  where
    n = sizeofSmallArray projs

    bind i v e
      | i < n - 1 = updateSmallArray (n - 2 - i) v e
      | otherwise = e
    {-# INLINE bind #-}

    step !i
      | i >= n = Done
      | testBit remaining i,
        (indexPrimArray depMasks i .&. remaining) == 0 = do
          let remaining' = clearBit remaining i
              iso =
                sigmaSwaps
                  (if i == n - 1 then Comm else SigmaSwap)
                  (popCount (remaining .&. (bit i - 1)))
              (# name #) = indexSmallArray## names i
              proj = eval (level :>> env) (indexSmallArray projs i)
              next
                | popCount remaining' <= 1 = Left \ ~v -> do
                    let env' = bind i v env
                        (# proj #) = indexSmallArray## projs (countTrailingZeros remaining')
                    eval (level :>> env') proj
                | otherwise = Right \ ~v -> do
                    let env' = bind i v env
                    SigmaGen {remaining = remaining', env = env', ..}
          Yield ProjChoice {..} (i + 1)
      | otherwise = Skip (i + 1)
{-# INLINE projChoices #-}

sigmaSwaps :: Iso -> Int -> Iso
sigmaSwaps last = \case
  0 -> Refl
  n -> go (n - 1)
  where
    go = \case
      0 -> last
      n -> SigmaCongR (go (n - 1)) `Trans` SigmaSwap
