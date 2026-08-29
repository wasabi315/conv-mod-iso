module Heuristic where

import Common
import Control.Monad
import ConversionModuloIsomorphism
import Data.List (minimumBy)
import Data.Ord
import Evaluation
import Isomorphism
import PiGenerator
import Term
import Value

--------------------------------------------------------------------------------
-- Reorder top-level pi domains so that more "discriminating" ones come earlier
-- Disclaimer: claude came up with this heuristics

refine0 :: Typ -> (Typ, Iso)
refine0 t = refine 0 (eval [] t)

refineConvIso0 :: Typ -> (Typ -> [Iso])
refineConvIso0 t = do
  let (t', i) = refine0 t
  \u -> (i <>) <$!> convIso0 t' u

refine :: Level -> Value -> (Typ, Iso)
refine l t = case t of
  VPi x a b -> refinePi l (initPiGen l (VPiArg x a b))
  _ -> (quote l t, Refl)

-- greedy
refinePi :: Level -> PiGen -> (Typ, Iso)
refinePi l gen = do
  -- not maximumBy (comparing (sc l)) here!
  -- maximumBy takes the rightmost one on tie but we want the leftmost for smaller Iso
  let DomChoice {..} = minimumBy (comparing \c -> Down (size l c.dom)) (domChoices gen)
  case next of
    Nothing -> do
      let pi = Pi name (quote l dom) (quote (l + 1) (cod (VVar l)))
      (pi, iso)
    Just gen -> do
      let (rest, iso') = refinePi (l + 1) (gen (VVar l))
          pi = Pi name (quote l dom) rest
          iso'' = iso <> piCongR iso'
      (pi, iso'')

size :: Level -> Value -> Int
size l = \case
  VRigid _ sp -> 1 + sizeSp l sp
  VTop _ sp -> 1 + sizeSp l sp
  VU -> 1
  VPi _ a b -> 1 + size l a + size (l + 1) (b (VVar l))
  VLam _ t -> 1 + size (l + 1) (t (VVar l))
  VSigma _ a b -> 1 + size l a + size (l + 1) (b (VVar l))
  VPair t u -> 1 + size l t + size l u

sizeSp :: Level -> Spine -> Int
sizeSp l = \case
  SNil -> 0
  SApp sp u -> 1 + sizeSp l sp + size l u
  SFst sp -> 1 + sizeSp l sp
  SSnd sp -> 1 + sizeSp l sp
