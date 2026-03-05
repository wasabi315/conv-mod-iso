module Evaluation where

import Common
import Term
import Value

--------------------------------------------------------------------------------
-- Evaluation

eval :: Env -> Term -> Value
eval env = \case
  Var (Index x) -> env !! x
  Top x -> VTop x SNil
  U -> VU
  Pi x a b -> VPi x (eval env a) \ ~v -> eval (v : env) b
  Lam x t -> VLam x \v -> eval (v : env) t
  t :$$ u -> eval env t $$ eval env u
  Sigma x a b -> VSigma x (eval env a) \ ~v -> eval (v : env) b
  Pair t u -> VPair (eval env t) (eval env u)
  Fst t -> vfst (eval env t)
  Snd t -> vsnd (eval env t)

($$) :: Value -> Value -> Value
t $$ u = case t of
  VLam _ f -> f u
  VRigid x sp -> VRigid x (SApp sp u)
  VTop x sp -> VTop x (SApp sp u)
  _ -> error "($$): not a lambda"

vfst :: Value -> Value
vfst = \case
  VPair t _ -> t
  VRigid x sp -> VRigid x (SFst sp)
  VTop x sp -> VTop x (SFst sp)
  _ -> error "vfst: not a pair"

vsnd :: Value -> Value
vsnd = \case
  VPair _ t -> t
  VRigid x sp -> VRigid x (SSnd sp)
  VTop x sp -> VTop x (SSnd sp)
  _ -> error "vsnd: not a pair"

--------------------------------------------------------------------------------

quote :: Level -> Value -> Term
quote l = \case
  VRigid x sp -> quoteSpine l (Var $ coerce (l - x - 1)) sp
  VTop x sp -> quoteSpine l (Top x) sp
  VU -> U
  VPi x a b -> Pi x (quote l a) (quote (l + 1) (b $ VVar l))
  VLam x t -> Lam x (quote (l + 1) (t $ VVar l))
  VSigma x a b -> Sigma x (quote l a) (quote (l + 1) (b $ VVar l))
  VPair t u -> Pair (quote l t) (quote l u)

quoteSpine :: Level -> Term -> Spine -> Term
quoteSpine l hd = \case
  SNil -> hd
  SApp sp t -> quoteSpine l hd sp :$$ quote l t
  SFst t -> Fst $ quoteSpine l hd t
  SSnd t -> Snd $ quoteSpine l hd t

--------------------------------------------------------------------------------

conv :: Level -> Value -> Value -> Bool
conv l = \cases
  (VRigid x sp) (VRigid x' sp') ->
    x == x' && convSpine l sp sp'
  (VTop x sp) (VTop x' sp') ->
    x == x' && convSpine l sp sp'
  VU VU -> True
  (VPi _ a b) (VPi _ a' b') ->
    conv l a a' && conv (l + 1) (b $ VVar l) (b' $ VVar l)
  (VLam _ t) (VLam _ t') ->
    conv (l + 1) (t $ VVar l) (t' $ VVar l)
  (VLam _ t) u ->
    conv (l + 1) (t $ VVar l) (u $$ VVar l)
  t (VLam _ u) ->
    conv (l + 1) (t $$ VVar l) (u $ VVar l)
  (VSigma _ a b) (VSigma _ a' b') ->
    conv l a a' && conv (l + 1) (b $ VVar l) (b' $ VVar l)
  (VPair t u) (VPair t' u') ->
    conv l t t' && conv l u u'
  (VPair t u) v ->
    conv l t (vfst v) && conv l u (vsnd v)
  t (VPair u v) ->
    conv l (vfst t) u && conv l (vsnd t) v
  _ _ -> False

convSpine :: Level -> Spine -> Spine -> Bool
convSpine l = \cases
  SNil SNil -> True
  (SApp sp t) (SApp sp' t') -> convSpine l sp sp' && conv l t t'
  (SFst sp) (SFst sp') -> convSpine l sp sp'
  (SSnd sp) (SSnd sp') -> convSpine l sp sp'
  _ _ -> False
