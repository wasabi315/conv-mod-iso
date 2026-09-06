module Isomorphism where

import Common
import Evaluation
import Term
import Value
import Prelude hiding (curry)

--------------------------------------------------------------------------------
-- Isomorphisms

data Iso
  = --  -------
    --   A ~ A
    Refl
  | --   A ~ B
    --  -------
    --   B ~ A
    Sym Iso
  | --   A ~ B    B ~ C
    --  ----------------
    --       A ~ C
    Trans Iso Iso
  | --  ----------------------------------------------------------------
    --   (x : (y : A) * B[y]) * C[x] ~ (y : A) * (x : B[y]) * C[(x, y)]
    Assoc
  | --  ---------------
    --   A * B ~ B * A
    Comm
  | -- ---------------------------------------------
    --  (x : A) * (y : B) * C ~ (y : B) * (x : A) * C
    --
    -- derivable from comm and assoc
    SigmaSwap
  | --  -------------------------------------------------------------------
    --   (x : (y : A) * B[y]) -> C[x] ~ (y : A) -> (x : B[y]) -> C[(x, y)]
    Curry
  | -- ---------------------------------------------
    --  (x : A) (y : B) -> C ~ (y : B) (x : A) -> C
    --
    -- derivable from comm and curry
    PiSwap
  | --                     i : A ~ A'
    --  ---------------------------------------------------
    --   (x : A) -> B[x] ~ (x : A') -> B[transportInv i x]
    PiCongL Iso
  | --             B[x] ~ B'[x]
    --  ------------------------------------
    --   (x : A) -> B[x] ~ (x : A) -> B'[x]
    PiCongR Iso
  | --                     i : A ~ A'
    --  -------------------------------------------------
    --   (x : A) * B[x] ~ (x : A') * B[transportInv i x]
    SigmaCongL Iso
  | --           B[x] ~ B'[x]
    --  ----------------------------------
    --   (x : A) * B[x] ~ (x : A) * B'[x]
    SigmaCongR Iso
  deriving stock (Eq, Ord, Show, Generic)
  deriving anyclass (NFData)

instance Semigroup Iso where
  (<>) = \cases
    Refl j -> j
    i Refl -> i
    i j -> Trans i j
  {-# INLINE (<>) #-}

instance Monoid Iso where
  mempty = Refl
  {-# INLINE mempty #-}

sym :: Iso -> Iso
sym = \case
  Refl -> Refl
  Sym i -> i
  i -> Sym i
{-# INLINE sym #-}

piCongL :: Iso -> Iso
piCongL = \case
  Refl -> Refl
  i -> PiCongL i
{-# INLINE piCongL #-}

piCongR :: Iso -> Iso
piCongR = \case
  Refl -> Refl
  i -> PiCongR i
{-# INLINE piCongR #-}

sigmaCongL :: Iso -> Iso
sigmaCongL = \case
  Refl -> Refl
  i -> SigmaCongL i
{-# INLINE sigmaCongL #-}

sigmaCongR :: Iso -> Iso
sigmaCongR = \case
  Refl -> Refl
  i -> SigmaCongR i
{-# INLINE sigmaCongR #-}

--------------------------------------------------------------------------------

-- | transport a value @v : A@ along an isomorphism @i : A ~ B@
transport :: Iso -> Value -> Value
transport = \cases
  Refl v -> v
  (Sym i) v -> transportInv i v
  (Trans i j) v -> transport j (transport i v)
  Assoc ((u :* v) :* w) -> u :* v :* w
  Comm (u :* v) -> v :* u
  SigmaSwap (u :* v :* w) -> v :* u :* w
  Curry v -> VLam "x" \x -> VLam "y" \y -> v $$ (x :* y)
  PiSwap v -> VLam "y" \y -> VLam "x" \x -> v $$ x $$ y
  (PiCongL i) v -> VLam "x" \x -> v $$ transportInv i x
  (PiCongR i) v -> VLam "x" \x -> transport i (v $$ x)
  (SigmaCongL i) (u :* v) -> transport i u :* v
  (SigmaCongR i) (u :* v) -> u `VPair` transport i v

-- | transport back a value @v : B@ along an isomorphism @i : A ~ B@
transportInv :: Iso -> Value -> Value
transportInv = \cases
  Refl v -> v
  (Sym i) v -> transport i v
  (Trans i j) v -> transportInv i (transportInv j v)
  Assoc (u :* v :* w) -> (u :* v) :* w
  Comm (u :* v) -> v :* u
  SigmaSwap (u :* v :* w) -> v :* u :* w
  Curry v -> VLam "p" \(x :* y) -> v $$ x $$ y
  PiSwap v -> VLam "x" \x -> VLam "y" \y -> v $$ y $$ x
  (PiCongL i) v -> VLam "x" \x -> v $$ transport i x
  (PiCongR i) v -> VLam "x" \x -> transportInv i (v $$ x)
  (SigmaCongL i) (u :* v) -> transportInv i u `VPair` v
  (SigmaCongR i) (u :* v) -> u `VPair` transportInv i v

--------------------------------------------------------------------------------
-- Rewriting types

-- | curry until the first domain becomes non-sigma
curry :: VPiArg -> (VPiArg, Iso)
curry = go Refl
  where
    go i = \case
      VPiArg x (VSigma y a b) c ->
        go (i <> Curry) $ VPiArg y a \ ~u -> VPi x (b u) \ ~v -> c (VPair u v)
      t -> (t, i)

-- | Curry all top-level pis. Does not curry higher-order arguments.
curryAll :: Level -> VPiArg -> (PiArg, Iso)
curryAll = \l pi -> case goPi Refl l pi of
  (Pi x a b, i) -> (PiArg x a b, i)
  _ -> error "impossible"
  where
    go l = \case
      VPi x a b -> goPi Refl l (VPiArg x a b)
      a -> (quote l a, Refl)

    goPi i l (VPiArg x a b) = case a of
      VSigma y a1 a2 ->
        goPi (i <> Curry) l $ VPiArg y a1 \ ~u -> VPi x (a2 u) \ ~v -> b (VPair u v)
      a -> do
        let a' = quote l a
            (b', j) = go (l + 1) (b $ VVar l)
            pi = Pi x a' b'
            k = i <> piCongR j
        (pi, k)

-- | associate until the first projection becomes non-sigma
assoc :: VSigmaArg -> (VSigmaArg, Iso)
assoc = go Refl
  where
    go i = \case
      VSigmaArg x (VSigma y a b) c ->
        go (i <> Assoc) $ VSigmaArg y a \ ~u -> VSigma x (b u) \ ~v -> c (VPair u v)
      t -> (t, i)

-- | Assoc all top-level sigmas
assocAll :: Level -> VSigmaArg -> (SigmaArg, Iso)
assocAll = \l sig -> case goSigma Refl l sig of
  (Sigma x a b, i) -> (SigmaArg x a b, i)
  _ -> error "impossible"
  where
    go l = \case
      VSigma x a b -> goSigma Refl l (VSigmaArg x a b)
      a -> (quote l a, Refl)

    goSigma i l (VSigmaArg x a b) = case a of
      VSigma y a1 a2 ->
        goSigma (i <> Assoc) l $ VSigmaArg y a1 \ ~u -> VSigma x (a2 u) \ ~v -> b (VPair u v)
      a -> do
        let a' = quote l a
            (b', j) = go (l + 1) (b $ VVar l)
            sigma = Sigma x a' b'
            k = i <> sigmaCongR j
        (sigma, k)

--------------------------------------------------------------------------------
-- Normalisation

normalise0 :: Term -> (Term, Iso)
normalise0 t = normalise 0 (eval emptyEnv t)

normalise :: Level -> Value -> (Term, Iso)
normalise l = \case
  VPi x a b -> normalisePi l (VPiArg x a b)
  VSigma x a b -> normaliseSigma l (VSigmaArg x a b)
  v -> quote l v // mempty

normalisePi :: Level -> VPiArg -> (Term, Iso)
normalisePi l q = do
  let (VPiArg x a b, i) = curry q
      (ta, ia) = normalise l a
      (tb, ib) = normalise (l + 1) (b $ transportInv ia (VVar l))
  Pi x ta tb // i <> piCongL ia <> piCongR ib

normaliseSigma :: Level -> VSigmaArg -> (Term, Iso)
normaliseSigma l q = do
  let (VSigmaArg x a b, i) = assoc q
      (ta, ia) = normalise l a
      (tb, ib) = normalise (l + 1) (b $ transportInv ia (VVar l))
  Sigma x ta tb // i <> sigmaCongL ia <> sigmaCongR ib
