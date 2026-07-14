module DiscriminationTree where

import Common
import Control.Applicative
import Control.Monad
import Data.Foldable1
import Data.List.NonEmpty qualified as NE
import Data.Map.Lazy qualified as M
import Evaluation
import Isomorphism
import Value
import Prelude hiding (curry, foldr1, lookup)

--------------------------------------------------------------------------------

-- Tokens
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

-- Discrimination tree
data Trie a
  = Leaf a
  | One Token ~(Trie a)
  | Node (M.Map Token (Trie a)) -- two or more
  deriving stock (Functor, Foldable, Traversable)

unionWith :: (a -> a -> a) -> Trie a -> Trie a -> Trie a
unionWith f = \cases
  (Leaf x) (Leaf y) -> Leaf $ f x y
  (One tok t) (One tok' t')
    | tok == tok' -> One tok $ unionWith f t t'
    | otherwise -> Node $ M.fromList [(tok, t), (tok', t')]
  (One tok t) (Node ts) -> Node $ M.insertWith (unionWith f) tok t ts
  (Node ts) (One tok t) -> Node $ M.insertWith (flip $ unionWith f) tok t ts
  (Node ts) (Node ts') -> Node $ M.unionWith (unionWith f) ts ts'
  _ _ -> error "impossible"

union :: Trie a -> Trie a -> Trie a
union = unionWith const

unions :: (Foldable1 f) => f (Trie a) -> Trie a
unions = foldr1 union

child :: Token -> Trie a -> Maybe (Trie a)
child tok = \case
  Leaf {} -> error "impossible"
  One tok' ch -> ch <$ guard (tok == tok')
  Node ch -> M.lookup tok ch
{-# INLINE child #-}

spineLength :: Spine -> Int
spineLength = \case
  SNil -> 0
  SApp sp _ -> 1 + spineLength sp
  SFst sp -> 1 + spineLength sp
  SSnd sp -> 1 + spineLength sp

findConv' :: Level -> Value -> Trie a -> (Trie a -> Maybe a) -> Maybe a
findConv' l v t k = case v of
  VRigid x sp ->
    asum
      [ do
          let len = spineLength sp
          t <- child (TRigid x len) t
          findConvSpine l sp t k,
        -- eta expand value (function)
        do
          t <- child TLam t
          findConv' (l + 1) (v $$ VVar l) t k,
        -- eta expand value (pair)
        do
          t <- child TPair t
          findConv' l (vfst v) t \t ->
            findConv' l (vsnd v) t k
      ]
  VTop x sp ->
    asum
      [ do
          let len = spineLength sp
          t <- child (TTop x len) t
          findConvSpine l sp t k,
        -- trie side is eta longer (function)
        do
          t <- child TLam t
          findConv' (l + 1) (v $$ VVar l) t k,
        -- trie side is eta longer (pair)
        do
          t <- child TPair t
          findConv' l (vfst v) t \t ->
            findConv' l (vsnd v) t k
      ]
  VU -> do
    t <- child TU t
    k t
  VPi _ a b -> do
    t <- child TPi t
    findConv' l a t \t ->
      findConv' (l + 1) (b $ VVar l) t k
  VLam _ v -> do
    t <- child TLam t
    findConv' (l + 1) (v $ VVar l) t k
  VSigma _ a b -> do
    t <- child TSigma t
    findConv' l a t \t ->
      findConv' (l + 1) (b $ VVar l) t k
  VPair u v -> do
    t <- child TPair t
    findConv' l u t \t ->
      findConv' l v t k

findConvSpine :: Level -> Spine -> Trie a -> (Trie a -> Maybe a) -> Maybe a
findConvSpine l sp t k = case sp of
  SNil -> k t
  SApp sp u -> findConvSpine l sp t \ts -> do
    t <- child TApp ts
    findConv' l u t k
  SFst sp -> findConvSpine l sp t \ts -> do
    t <- child TFst ts
    k t
  SSnd sp -> findConvSpine l sp t \ts -> do
    t <- child TSnd ts
    k t

findConv :: Level -> Value -> Trie a -> Maybe a
findConv l v t = findConv' l v t \case
  Leaf x -> Just x
  One {} -> error "impossible"
  Node {} -> error "impossible"

--------------------------------------------------------------------------------
-- Saturated discrimination tree

isoTrie :: Level -> Value -> Trie Iso
isoTrie l t = isoTrie' l t Leaf

isoTrie' :: Level -> Value -> (Iso -> Trie a) -> Trie a
isoTrie' l t k = case t of
  VPi x a b -> isoTriePi l (VPiArg x a b) k
  VSigma x a b -> isoTrieSigma l (VSigmaArg x a b) k
  _ -> reflTrie l t (k Refl)

isoTriePi :: Level -> VPiArg -> (Iso -> Trie a) -> Trie a
isoTriePi l pi k =
  One TPi $ unions do
    (VPiArg _ a b, i) <- NE.fromList $ currySwap l pi
    pure $ isoTrie' l a \ia ->
      isoTrie' (l + 1) (b $ transportInv ia (VVar l)) \ib ->
        k $! i <> piCongL ia <> piCongR ib

isoTrieSigma :: Level -> VSigmaArg -> (Iso -> Trie a) -> Trie a
isoTrieSigma l sig k =
  One TSigma $ unions do
    (VSigmaArg _ a b, i) <- NE.fromList $ assocSwap l sig
    pure $ isoTrie' l a \ia ->
      isoTrie' (l + 1) (b $ transportInv ia (VVar l)) \ib ->
        k $! i <> sigmaCongL ia <> sigmaCongR ib

reflTrie :: Level -> Value -> Trie a -> Trie a
reflTrie l = \case
  VRigid x sp -> etaTrie l (TRigid x) sp
  VTop x sp -> etaTrie l (TTop x) sp
  VU -> One TU
  VPi _ a b -> One TPi . reflTrie l a . reflTrie (l + 1) (b $ VVar l)
  VLam _ t -> One TLam . reflTrie (l + 1) (t $ VVar l)
  VSigma _ a b -> One TSigma . reflTrie l a . reflTrie (l + 1) (b $ VVar l)
  VPair t u -> One TPair . reflTrie l t . reflTrie l u

-- eta-expand speculatively and infinitely
etaTrie :: Level -> (Int -> Token) -> Spine -> Trie a -> Trie a
etaTrie l hd sp ~t =
  reflTrieSpine l hd sp t
    `union` One TLam (etaTrie (l + 1) hd (SApp sp (VVar l)) t)
    `union` One TPair (etaTrie l hd (SFst sp) $ etaTrie l hd (SSnd sp) t)

reflTrieSpine :: Level -> (Int -> Token) -> Spine -> Trie a -> Trie a
reflTrieSpine l hd = go 0
  where
    go len = \case
      SNil -> One (hd len)
      SApp sp u -> go (len + 1) sp . One TApp . reflTrie l u
      SFst sp -> go (len + 1) sp . One TFst
      SSnd sp -> go (len + 1) sp . One TSnd
