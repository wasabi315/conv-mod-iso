module ConversionModuloIsomorphism where

import Common
import Evaluation
import Isomorphism
import Term
import Value
import Prelude hiding (curry)

--------------------------------------------------------------------------------
-- Conversion checking modulo isomorphism

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
  flip (foldMapAParIf (par > 0) rseq) (currySwap l q') \(VPiArg _ a' b', i') -> do
    (ia, ia') <- convIso (par - 1) l a a'
    let v = transportInv ia (VVar l)
        v' = transportInv ia' (VVar l)
    (ib, ib') <- convIso (par - 1) (l + 1) (b v) (b' v')
    pure $! i <> piCongL ia <> piCongR ib // i' <> piCongL ia' <> piCongR ib'

convSigma :: Int -> Level -> VSigmaArg -> VSigmaArg -> [(Iso, Iso)]
convSigma par l q q' = do
  let (VSigmaArg _ a b, i) = assoc q
  flip (foldMapAParIf (par > 0) rseq) (assocSwap l q') \(VSigmaArg _ a' b', i') -> do
    (ia, ia') <- convIso (par - 1) l a a'
    let v = transportInv ia (VVar l)
        v' = transportInv ia' (VVar l)
    (ib, ib') <- convIso (par - 1) (l + 1) (b v) (b' v')
    pure $! i <> sigmaCongL ia <> sigmaCongR ib // i' <> sigmaCongL ia' <> sigmaCongR ib'
