module DiscriminationTree where

import Common
import Data.Map.Strict qualified as M
import Data.Set qualified as S
import Isomorphism
import Value
import Prelude hiding (curry, lookup)

--------------------------------------------------------------------------------
-- Tokens and preorder traversal

data Token
  = TRigid Level Int -- spine length
  | TTop Name Int -- spine length
  | TU
  | TPi
  | TLam
  | TSigma
  | TPair
  | TApp
  | TFst
  | TSnd
  deriving stock (Eq, Ord, Show)

type Path = [Token]

type DPath = Path -> Path

preorder :: Level -> Value -> DPath
preorder l = \case
  VRigid x sp -> preorderSpine l (TRigid x) sp
  VTop x sp -> preorderSpine l (TTop x) sp
  VU -> (TU :)
  VPi _ a b ->
    (TPi :)
      . preorder l a
      . preorder (l + 1) (b $ VVar l)
  VLam _ t ->
    (TLam :)
      . preorder (l + 1) (t $ VVar l)
  VSigma _ a b ->
    (TSigma :)
      . preorder l a
      . preorder (l + 1) (b $ VVar l)
  VPair t u ->
    (TPair :)
      . preorder l t
      . preorder l u

preorderSpine :: Level -> (Int -> Token) -> Spine -> DPath
preorderSpine l hd = \case
  SNil -> (hd 0 :)
  SApp sp t -> preorderSpine l (hd . succ) sp . (TApp :) . preorder l t
  SFst sp -> preorderSpine l (hd . succ) sp . (TFst :)
  SSnd sp -> preorderSpine l (hd . succ) sp . (TSnd :)

--------------------------------------------------------------------------------
-- Discrimination tree

data Trie a
  = Leaf a
  | Node (M.Map Token (Trie a))
  deriving stock (Show, Functor, Foldable, Traversable)

empty :: Trie a
empty = Node mempty

unionWith :: (a -> a -> a) -> Trie a -> Trie a -> Trie a
unionWith f = \cases
  (Leaf x) (Leaf y) -> Leaf $ f x y
  (Node ts) (Node ts') -> Node $ M.unionWith (unionWith f) ts ts'
  _ _ -> error "impossible"

unionsWith :: (Foldable f) => (a -> a -> a) -> f (Trie a) -> Trie a
unionsWith f = foldl' (unionWith f) empty

singleton :: Path -> a -> Trie a
singleton = \cases
  [] v -> Leaf v
  (t : p) v -> Node $ M.singleton t $ singleton p v

--------------------------------------------------------------------------------
-- Saturated discrimination tree

isoTrie :: Level -> Value -> Trie (S.Set Iso)
isoTrie l t = isoTrie' l t (Leaf . S.singleton)

isoTrie' :: Level -> Value -> (Iso -> Trie (S.Set Iso)) -> Trie (S.Set Iso)
isoTrie' l t rest = case t of
  VPi x a b -> isoTriePi l (VPiArg x a b) rest
  VSigma x a b -> isoTrieSigma l (VSigmaArg x a b) rest
  _ -> isoTrieRefl l t (rest Refl)

isoTriePi :: Level -> VPiArg -> (Iso -> Trie (S.Set Iso)) -> Trie (S.Set Iso)
isoTriePi l pi rest =
  Node $ M.singleton TPi $! unionsWith (<>) do
    (VPiArg _ a b, i) <- currySwap l pi
    pure $! isoTrie' l a \ia ->
      isoTrie' (l + 1) (b $ transportInv ia (VVar l)) \ib ->
        rest (i <> piCongL ia <> piCongR ib)

isoTrieSigma :: Level -> VSigmaArg -> (Iso -> Trie (S.Set Iso)) -> Trie (S.Set Iso)
isoTrieSigma l sig rest =
  Node $ M.singleton TSigma $! unionsWith (<>) do
    (VSigmaArg _ a b, i) <- assocSwap l sig
    pure $! isoTrie' l a \ia ->
      isoTrie' (l + 1) (b $ transportInv ia (VVar l)) \ib ->
        rest (i <> sigmaCongL ia <> sigmaCongR ib)

isoTrieRefl :: Level -> Value -> Trie a -> Trie a
isoTrieRefl l = \case
  VRigid x sp -> isoTrieSpine x (TRigid x) sp
  VTop x sp -> isoTrieSpine l (TTop x) sp
  VU -> Node . M.singleton TU
  VPi _ a b ->
    (Node . M.singleton TPi)
      . isoTrieRefl l a
      . isoTrieRefl (l + 1) (b $ VVar l)
  VLam _ t ->
    (Node . M.singleton TLam)
      . isoTrieRefl (l + 1) (t $ VVar l)
  VSigma _ a b ->
    (Node . M.singleton TSigma)
      . isoTrieRefl l a
      . isoTrieRefl (l + 1) (b $ VVar l)
  VPair t u ->
    (Node . M.singleton TPair)
      . isoTrieRefl l t
      . isoTrieRefl l u

isoTrieSpine :: Level -> (Int -> Token) -> Spine -> Trie a -> Trie a
isoTrieSpine l hd = \case
  SNil -> Node . M.singleton (hd 0)
  SApp sp u ->
    isoTrieSpine l (hd . succ) sp
      . (Node . M.singleton TApp)
      . isoTrieRefl l u
  SFst sp ->
    isoTrieSpine l (hd . succ) sp
      . (Node . M.singleton TFst)
  SSnd sp ->
    isoTrieSpine l (hd . succ) sp
      . (Node . M.singleton TSnd)
