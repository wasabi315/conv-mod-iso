module ConversionModuloIsomorphism where

import Common
import Evaluation
import Isomorphism
import PiGenerator
import Term
import Value
import Prelude hiding (curry)

--------------------------------------------------------------------------------
-- Conversion checking modulo isomorphism

convIso0 :: Term -> Term -> [Iso]
convIso0 t u = do
  (i, j) <- convIso 0 (eval [] t) (eval [] u)
  pure $! i <> sym j

convIso :: Level -> Value -> Value -> [(Iso, Iso)]
convIso l = \cases
  -- pi is only convertible with pi under the isomorphisms we consider here
  (VPi x a b) (VPi x' a' b') -> convPi l (VPiArg x a b) (VPiArg x' a' b')
  (VPi {}) _ -> []
  _ (VPi {}) -> []
  -- likewise
  (VSigma x a b) (VSigma x' a' b') -> convSigma l (VSigmaArg x a b) (VSigmaArg x' a' b')
  (VSigma {}) _ -> []
  _ (VSigma {}) -> []
  t u -> [(Refl, Refl) | conv l t u]

convPi :: Level -> VPiArg -> VPiArg -> [(Iso, Iso)]
convPi l pi pi' = convPiG l pi (initPiGen l pi')

convPiG :: Level -> VPiArg -> PiGen -> [(Iso, Iso)]
convPiG l pi gen = do
  let (VPiArg _ a b, i) = curry pi
  DomChoice {..} <- domChoices gen
  case dom of
    VSigma y a1 a2 -> do
      (VPiArg _ dom cod, j) <- curryDom l name (VSigmaArg y a1 a2) cod
      let iso' = iso <> j
      (ia, ia') <- convIso l a dom
      let v = transportInv ia (VVar l)
          v' = transportInv ia' (VVar l)
      (ib, ib') <- convIso (l + 1) (b v) (cod v')
      pure $! i <> piCongL ia <> piCongR ib // iso' <> piCongL ia' <> piCongR ib'
    dom -> do
      (ia, ia') <- convIso l a dom
      let v = transportInv ia (VVar l)
          v' = transportInv ia' (VVar l)
      (ib, ib') <- case next of
        Nothing -> convIso (l + 1) (b v) (cod v')
        Just gen | VPi y c d <- b v -> convPiG (l + 1) (VPiArg y c d) (gen v')
        _ -> []
      pure $! i <> piCongL ia <> piCongR ib // iso <> piCongL ia' <> piCongR ib'

convSigma :: Level -> VSigmaArg -> VSigmaArg -> [(Iso, Iso)]
convSigma l sig sig' = do
  let (VSigmaArg _ a b, i) = assoc sig
  (VSigmaArg _ a' b', i') <- assocSwap l sig'
  (ia, ia') <- convIso l a a'
  let v = transportInv ia (VVar l)
      v' = transportInv ia' (VVar l)
  (ib, ib') <- convIso (l + 1) (b v) (b' v')
  pure $! i <> sigmaCongL ia <> sigmaCongR ib // i' <> sigmaCongL ia' <> sigmaCongR ib'
