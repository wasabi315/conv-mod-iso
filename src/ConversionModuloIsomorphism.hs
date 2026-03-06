module ConversionModuloIsomorphism where

import Common
import Evaluation
import Isomorphism
import Term
import Value
import Prelude hiding (curry)

--------------------------------------------------------------------------------
-- Conversion checking modulo isomorphism

-- | Pick up a domain without breaking dependencies.
pickUpDomain' :: VTypKind -> Level -> VPiArg -> [(VPiArg, Iso)]
pickUpDomain' vk l (VPiArg x a b) = (VPiArg x a b, Refl) : go l b
  where
    go l' c = case c (VVar l') of
      VPi y c1 c2 ->
        [ (VPiArg y c1 rest, s)
        | vtyKind c1 `elem` [vk, VKSigma] && not (dependsOnLevelsBetween l l' c1),
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

-- | Pick up a projection without breaking dependencies.
pickUpProjection' :: VTypKind -> Level -> VSigmaArg -> [(VSigmaArg, Iso)]
pickUpProjection' vk l (VSigmaArg x a b) = (VSigmaArg x a b, Refl) : go l b
  where
    go l' c = case c (VVar l') of
      VSigma y c1 c2 ->
        [ (VSigmaArg y c1 rest, s)
        | vtyKind c1 `elem` [vk, VKSigma] && not (dependsOnLevelsBetween l l' c1),
          let i = l' - l
              rest ~vc1 = VSigma x a (instSigmaAt i vc1 . b)
              s = swaps SigmaSwap i
        ]
          ++ go (l' + 1) c2
      c ->
        [ (VSigmaArg "_" c rest, s)
        | (vtyKind c == vk) && not (dependsOnLevelsBetween l l' c),
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
assocSwap' :: VTypKind -> Level -> VSigmaArg -> [(VSigmaArg, Iso)]
assocSwap' vk l = go
  where
    go q = do
      -- Pick one projection first.
      r@(q, i) <- pickUpProjection' vk l q
      case q of
        -- When the selected projection is a sigma type, we invoke
        -- assocSwap recursively to make the first projection of the sigma non-sigma!
        VSigmaArg x (VSigma y a b) c -> do
          (VSigmaArg y a b, j) <- go (VSigmaArg y a b)
          let -- Then associate to make the first projection non-sigma.
              -- Don't forget transporting along @j@, since @assocSwap@ acted on the first projection above.
              q = VSigmaArg y a \ ~u -> VSigma x (b u) \ ~v -> c (transportInv j (VPair u v))
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
currySwap' :: VTypKind -> Level -> VPiArg -> [(VPiArg, Iso)]
currySwap' vk l q = do
  r@(q, i) <- pickUpDomain' vk l q
  case q of
    VPiArg x (VSigma y a b) c -> do
      (VSigmaArg y a b, j) <- assocSwap' vk l (VSigmaArg y a b)
      let q = VPiArg y a \ ~u -> VPi x (b u) \ ~v -> c (transportInv j (VPair u v))
          k = i <> piCongL j <> Curry
      pure (q, k)
    _ -> pure r

convIso0 :: Term -> Term -> [Iso]
convIso0 t u = do
  (i, j) <- convIso 3 0 (eval [] t) (eval [] u)
  pure $! i <> sym j

convIso :: Int -> Level -> Value -> Value -> [(Iso, Iso)]
convIso par l = \cases
  -- pi is only convertible with pi under the isomorphisms we consider here
  (VPi x a b) (VPi x' a' b') -> convPi par l (VPiArg x a b) (VPiArg x' a' b')
  (VPi {}) _ -> []
  _ (VPi {}) -> []
  -- likewise
  (VSigma x a b) (VSigma x' a' b') -> convSigma par l (VSigmaArg x a b) (VSigmaArg x' a' b')
  (VSigma {}) _ -> []
  _ (VSigma {}) -> []
  t u -> [(Refl, Refl) | conv l t u]

convPi :: Int -> Level -> VPiArg -> VPiArg -> [(Iso, Iso)]
convPi par l q q' = do
  let (VPiArg _ a b, i) = curry q
      vk = vtyKind a
  flip (foldMapAParIf (par > 0) rseq) (currySwap' vk l q') \(VPiArg _ a' b', i') -> do
    (ia, ia') <- convIso (par - 1) l a a'
    let v = transportInv ia (VVar l)
        v' = transportInv ia' (VVar l)
    (ib, ib') <- convIso (par - 1) (l + 1) (b v) (b' v')
    pure $! i <> piCongL ia <> piCongR ib // i' <> piCongL ia' <> piCongR ib'

convSigma :: Int -> Level -> VSigmaArg -> VSigmaArg -> [(Iso, Iso)]
convSigma par l q q' = do
  let (VSigmaArg _ a b, i) = assoc q
      vk = vtyKind a
  flip (foldMapAParIf (par > 0) rseq) (assocSwap' vk l q') \(VSigmaArg _ a' b', i') -> do
    (ia, ia') <- convIso (par - 1) l a a'
    let v = transportInv ia (VVar l)
        v' = transportInv ia' (VVar l)
    (ib, ib') <- convIso (par - 1) (l + 1) (b v) (b' v')
    pure $! i <> sigmaCongL ia <> sigmaCongR ib // i' <> sigmaCongL ia' <> sigmaCongR ib'
