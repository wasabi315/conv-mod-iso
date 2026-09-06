module ConversionModuloIsomorphism where

import Common
import Evaluation
import Isomorphism
import Permutation
import Term
import Value
import Prelude hiding (curry)

--------------------------------------------------------------------------------
-- Conversion checking modulo isomorphism

convIso0 :: Term -> Term -> [Iso]
convIso0 t u = do
  (i, j) <- convIso 0 (eval emptyEnv t) (eval emptyEnv u)
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
convPi l pi pi' = do
  let (pi'', k) = curryAll l pi'
  (i, j) <- convPiG l pi (initPiGen l (evalPi (idEnv l) pi''))
  pure $! i // k <> j

convPiG :: Level -> VPiArg -> PiGen -> [(Iso, Iso)]
convPiG l pi gen = do
  let (VPiArg _ a b, i) = curry pi
  DomChoice {..} <- domChoices gen
  (ia, ia') <- convIso l a dom
  let v = transportInv ia (VVar l)
      v' = transportInv ia' (VVar l)
  (ib, ib') <- case next of
    Left cod -> convIso (l + 1) (b v) (cod v')
    Right gen | VPi y c d <- b v -> convPiG (l + 1) (VPiArg y c d) (gen v')
    _ -> []
  pure $! i <> piCongL ia <> piCongR ib // iso <> piCongL ia' <> piCongR ib'

convSigma :: Level -> VSigmaArg -> VSigmaArg -> [(Iso, Iso)]
convSigma l sig sig' = do
  let (sig'', k) = assocAll l sig'
  (i, j) <- convSigmaG l sig (initSigmaGen l (evalSigma (idEnv l) sig''))
  pure $! i // k <> j

convSigmaG :: Level -> VSigmaArg -> SigmaGen -> [(Iso, Iso)]
convSigmaG l pi gen = do
  let (VSigmaArg _ a b, i) = assoc pi
  ProjChoice {..} <- projChoices gen
  (ia, ia') <- convIso l a proj
  let v = transportInv ia (VVar l)
      v' = transportInv ia' (VVar l)
  (ib, ib') <- case next of
    Left cod -> convIso (l + 1) (b v) (cod v')
    Right gen | VSigma y c d <- b v -> convSigmaG (l + 1) (VSigmaArg y c d) (gen v')
    _ -> []
  pure $! i <> sigmaCongL ia <> sigmaCongR ib // iso <> sigmaCongL ia' <> sigmaCongR ib'
