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
  deriving stock (Show, Generic)
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
transport i v = case i of
  Refl -> v
  Sym i -> transportInv i v
  Trans i j -> transport j (transport i v)
  Assoc -> vfst (vfst v) `VPair` (vsnd (vfst v) `VPair` vsnd v)
  Comm -> vsnd v `VPair` vfst v
  SigmaSwap -> vfst (vsnd v) `VPair` (vfst v `VPair` vsnd (vsnd v))
  Curry -> VLam "x" \x -> VLam "y" \y -> v $$ VPair x y
  PiSwap -> VLam "y" \y -> VLam "x" \x -> v $$ x $$ y
  PiCongL i -> VLam "x" \x -> v $$ transportInv i x
  PiCongR i -> VLam "x" \x -> transport i (v $$ x)
  SigmaCongL i -> transport i (vfst v) `VPair` vsnd v
  SigmaCongR i -> vfst v `VPair` transport i (vsnd v)

-- | transport back a value @v : B@ along an isomorphism @i : A ~ B@
transportInv :: Iso -> Value -> Value
transportInv i v = case i of
  Refl -> v
  Sym i -> transport i v
  Trans i j -> transportInv i (transportInv j v)
  Assoc -> (vfst v `VPair` vfst (vsnd v)) `VPair` vsnd (vsnd v)
  Comm -> vsnd v `VPair` vfst v
  SigmaSwap -> vfst (vsnd v) `VPair` (vfst v `VPair` vsnd (vsnd v))
  Curry -> VLam "p" \p -> v $$ vfst p $$ vsnd p
  PiSwap -> VLam "x" \x -> VLam "y" \y -> v $$ y $$ x
  PiCongL i -> VLam "x" \x -> v $$ transport i x
  PiCongR i -> VLam "x" \x -> transportInv i (v $$ x)
  SigmaCongL i -> transportInv i (vfst v) `VPair` vsnd v
  SigmaCongR i -> vfst v `VPair` transportInv i (vsnd v)

--------------------------------------------------------------------------------
-- Rewriting types

-- | curry until the first domain becomes non-sigma
curry :: Quant -> (Quant, Iso)
curry = go Refl
  where
    go i = \case
      Quant x (VSigma y a b) c ->
        go (i <> Curry) $ Quant y a \ ~u -> VPi x (b u) \ ~v -> c (VPair u v)
      t -> (t, i)

-- | associate until the first projection becomes non-sigma
assoc :: Quant -> (Quant, Iso)
assoc = go Refl
  where
    go i = \case
      Quant x (VSigma y a b) c ->
        go (i <> Assoc) $ Quant y a \ ~u -> VSigma x (b u) \ ~v -> c (VPair u v)
      t -> (t, i)

dependsOnLevelsBetween :: Level -> Level -> Value -> Bool
dependsOnLevelsBetween from to = go to
  where
    go l = \case
      VRigid x sp -> (from <= x && x <= to) || goSpine l sp
      VTop _ sp -> goSpine l sp
      VU -> False
      VPi _ a b -> go l a || goBind l b
      VLam _ t -> goBind l t
      VSigma _ a b -> go l a || goBind l b
      VPair t u -> go l t || go l u

    goBind l t = go (l + 1) (t $ VVar l)

    goSpine l = \case
      SNil -> False
      SApp sp t -> goSpine l sp || go l t
      SFst sp -> goSpine l sp
      SSnd sp -> goSpine l sp

-- | Pick a domain without breaking dependencies.
pickDomain :: Level -> Quant -> [(Quant, Iso)]
pickDomain l (Quant x a b) = (Quant x a b, Refl) : go l b
  where
    go l' c = case c (VVar l') of
      VPi y c1 c2 ->
        [ (Quant y c1 rest, s)
        | not $ dependsOnLevelsBetween l l' c1,
          let i = l' - l
              rest ~vc1 = VPi x a (instPiAt i vc1 . b)
              s = swaps i
        ]
          ++ go (l' + 1) c2
      _ -> []

    instPiAt = \cases
      0 ~v (VPi _ _ b) -> b v
      i ~v (VPi x a b) -> VPi x a (instPiAt (i - 1) v . b)
      _ ~_ _ -> error "impossible"

    swaps = \case
      0 -> PiSwap
      n -> piCongR (swaps (n - 1)) <> PiSwap

-- | Pick a projection without breaking dependencies.
pickProjection :: Level -> Quant -> [(Quant, Iso)]
pickProjection l (Quant x a b) = (Quant x a b, Refl) : go l b
  where
    go l' c = case c (VVar l') of
      VSigma y c1 c2 ->
        [ (Quant y c1 rest, s)
        | not $ dependsOnLevelsBetween l l' c1,
          let i = l' - l
              rest ~vc1 = VSigma x a (instSigmaAt i vc1 . b)
              s = swaps SigmaSwap i
        ]
          ++ go (l' + 1) c2
      c ->
        [ (Quant "_" c rest, s)
        | not $ dependsOnLevelsBetween l l' c,
          let rest ~_ = dropLastProj (l + 1) (VSigma x a b)
              s = swaps Comm (l' - l)
        ]

    instSigmaAt = \cases
      0 ~v (VSigma _ _ b) -> b v
      i ~v (VSigma x a b) -> VSigma x a (instSigmaAt (i - 1) v . b)
      _ ~_ _ -> error "impossible"

    dropLastProj l = \case
      VSigma x a b -> case b (VVar l) of
        VSigma {} -> VSigma x a (dropLastProj (l + 1) . b)
        _ -> a
      _ -> error "impossible"

    swaps i = \case
      (0 :: Level) -> i
      n -> sigmaCongR (swaps i (n - 1)) <> SigmaSwap

-- | Pick a **non-sigma** projection without breaking dependencies.
-- This works even in the presence of arbitrarily nested sigmas in the type.
assocSwap :: Level -> Quant -> [(Quant, Iso)]
assocSwap l = go
  where
    go q = do
      -- Pick one projection first.
      r@(q, i) <- pickProjection l q
      case q of
        -- When the selected projection is a sigma type, we invoke
        -- assocSwap recursively to make the first projection of the sigma non-sigma!
        Quant x (VSigma y a b) c -> do
          (Quant y a b, j) <- go (Quant y a b)
          let -- Then associate to make the first projection non-sigma.
              -- Don't forget transporting along @j@, since @assocSwap@ acted on the first projection above.
              q = Quant y a \ ~u -> VSigma x (b u) \ ~v -> c (transportInv j (VPair u v))
              k = i <> sigmaCongL j <> Assoc
          pure (q, k)
        _ -> pure r

-- | Pick a **non-sigma** domain without breaking dependencies.
-- This works even in the presence of arbitrarily nested sigmas in the type.

--   e.g) currySwap (List A → (B × A → A) × B → B) =
--          [ ( List A → (B × A → A) × B → B , Refl                    ),
--            ( (B × A → B) → B → List A → B , ΠSwap · Curry           ),
--            ( B → (B × A → B) → List A → B , ΠSwap · ΠL Comm · Curry )
--          ]
currySwap :: Level -> Quant -> [(Quant, Iso)]
currySwap l q = do
  r@(q, i) <- pickDomain l q
  case q of
    Quant x (VSigma y a b) c -> do
      (Quant y a b, j) <- assocSwap l (Quant y a b)
      let q = Quant y a \ ~u -> VPi x (b u) \ ~v -> c (transportInv j (VPair u v))
          k = i <> piCongL j <> Curry
      pure (q, k)
    _ -> pure r

--------------------------------------------------------------------------------
-- Normalisation

normalise0 :: Term -> (Term, Iso)
normalise0 t = normalise 0 (eval [] t)

normalise :: Level -> Value -> (Term, Iso)
normalise l = \case
  VPi x a b -> normalisePi l (Quant x a b)
  VSigma x a b -> normaliseSigma l (Quant x a b)
  v -> quote l v // mempty

normalisePi :: Level -> Quant -> (Term, Iso)
normalisePi l q = do
  let (Quant x a b, i) = curry q
      (ta, ia) = normalise l a
      (tb, ib) = normalise (l + 1) (b $ transportInv ia (VVar l))
  Pi x ta tb // i <> piCongL ia <> piCongR ib

normaliseSigma :: Level -> Quant -> (Term, Iso)
normaliseSigma l q = do
  let (Quant x a b, i) = assoc q
      (ta, ia) = normalise l a
      (tb, ib) = normalise (l + 1) (b $ transportInv ia (VVar l))
  Sigma x ta tb // i <> sigmaCongL ia <> sigmaCongR ib

--------------------------------------------------------------------------------
-- Normalisation + Permutation

normalisePermute0 :: Term -> [(Term, Iso)]
normalisePermute0 t = normalisePermute 0 (eval [] t)

normalisePermute :: Level -> Value -> [(Term, Iso)]
normalisePermute l = \case
  VPi x a b -> normalisePermutePi l (Quant x a b)
  VSigma x a b -> normalisePermuteSigma l (Quant x a b)
  v -> pure $! quote l v // Refl

normalisePermutePi :: Level -> Quant -> [(Term, Iso)]
normalisePermutePi l q = do
  (Quant x a b, i) <- currySwap l q
  (a, ia) <- normalisePermute l a
  let v = transportInv ia (VVar l)
  (b, ib) <- normalisePermute (l + 1) (b v)
  pure $! Pi x a b // i <> piCongL ia <> piCongR ib

normalisePermuteSigma :: Level -> Quant -> [(Term, Iso)]
normalisePermuteSigma l q = do
  (Quant x a b, i) <- assocSwap l q
  (a, ia) <- normalisePermute l a
  let v = transportInv ia (VVar l)
  (b, ib) <- normalisePermute (l + 1) (b v)
  pure $! Sigma x a b // i <> sigmaCongL ia <> sigmaCongR ib
