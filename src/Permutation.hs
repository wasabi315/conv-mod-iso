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
import Data.IntSet qualified as IS
import Data.Primitive.PrimArray
import Data.Primitive.SmallArray
import Isomorphism
import Value

--------------------------------------------------------------------------------

pattern Placeholder :: Value
pattern Placeholder = VVar (-1)

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
    cod :: Value -> VTyp,
    iso :: Iso,
    next :: Maybe (Value -> PiGen)
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
              iso = piSwaps $ popCount (remaining .&. (bit i - 1))
              cod ~w = do
                let subst' = updateSmallArray i w subst
                currentCod original subst' remaining'
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

currentCod :: VPiArg -> SmallArray Value -> Int -> VTyp
currentCod (VPiArg x a b) subst rem =
  ifoldrSmallArray step id subst (VPi x a b)
  where
    step i v k = \case
      VPi y c d
        | testBit rem i -> VPi y c \ ~w -> k (d w)
        | otherwise -> k (d v)
      _ -> error "impossible"
{-# INLINE currentCod #-}

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
    proj2 :: Value -> VTyp,
    iso :: Iso,
    next :: Maybe (Value -> SigmaGen)
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
      VSigma _ a b -> do
        let mask = depMask l' a
        mask : depMasks (l' + 1) (b $ VVar l')
      a -> do
        let mask = depMask l' a
        [mask]

    depMask l' =
      IS.foldl'
        (\mask x -> setBit mask (x - coerce l))
        (0 :: Int)
        . levelsBetween l l'

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
              proj2 ~w = do
                let subst' = bind i w subst
                currentProj2 original subst' remaining'
              next
                -- one component left is the second projection itself
                | popCount remaining' <= 1 = Nothing
                | otherwise = Just \ ~w -> do
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

currentProj2 :: VSigmaArg -> SmallArray Value -> Int -> VTyp
currentProj2 (VSigmaArg x a b) subst rem =
  ifoldrSmallArray step id subst (VSigma x a b)
  where
    step i v k = \case
      VSigma y a b
        | not (testBit rem i) -> k (b v)
        -- nothing remains after this one, so it is the projection, not a sigma
        | rem `unsafeShiftR` (i + 1) == 0 -> a
        | otherwise -> VSigma y a \ ~w -> k (b w)
      _ -> error "impossible"
{-# INLINE currentProj2 #-}

sigmaSwaps :: Iso -> Int -> Iso
sigmaSwaps last = \case
  0 -> Refl
  n -> go (n - 1)
  where
    go = \case
      0 -> last
      n -> SigmaCongR (go (n - 1)) `Trans` SigmaSwap
