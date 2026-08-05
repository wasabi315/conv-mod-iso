{-# LANGUAGE OrPatterns #-}

module DiscriminationTree where

import Common
import Control.Applicative
import Control.Monad
import Data.Foldable1
import Data.List.NonEmpty qualified as NE
import Data.Map.Lazy qualified as M
import Data.Maybe
import Evaluation
import Isomorphism
import Pretty
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
  | TEtaLam
  | TEtaPair
  deriving stock (Eq, Ord, Show)

isEtaToken :: Token -> Bool
isEtaToken = \case
  TEtaLam -> True
  TEtaPair -> True
  _ -> False

-- Discrimination tree
data Trie a
  = Leaf a
  | One Token ~(Trie a)
  | Node (M.Map Token (Trie a)) -- two or more
  deriving stock (Functor, Foldable, Traversable)

extract :: Trie a -> a
extract = \case
  Leaf x -> x
  One {}; Node {} -> error "extract"

--------------------------------------------------------------------------------
-- "Saturated" discrimination tree costruction

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
etaTrie l hd sp ~dt =
  reflTrieSpine l hd sp dt
    `union` One TEtaLam (etaTrie (l + 1) hd (SApp sp (VVar l)) dt)
    `union` One TEtaPair (etaTrie l hd (SFst sp) $ etaTrie l hd (SSnd sp) dt)

reflTrieSpine :: Level -> (Int -> Token) -> Spine -> Trie a -> Trie a
reflTrieSpine l hd = go 0
  where
    go len = \case
      SNil -> One (hd len)
      SApp sp u -> go (len + 1) sp . One TApp . reflTrie l u
      SFst sp -> go (len + 1) sp . One TFst
      SSnd sp -> go (len + 1) sp . One TSnd

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

--------------------------------------------------------------------------------
-- Lookup

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

findConv :: Level -> Value -> Trie a -> [a]
findConv l v dt = extract <$!> findConv' l v dt

findConv' :: Level -> Value -> Trie a -> [Trie a]
findConv' l v dt = case v of
  VRigid x sp ->
    concat
      [ do
          let len = spineLength sp
          dt <- maybeToList $ child (TRigid x len) dt
          findConvSpine l sp dt,
        -- eta expand value (function)
        do
          dt <- maybeToList $ child TLam dt
          findConv' (l + 1) (v $$ VVar l) dt,
        -- eta expand value (pair)
        do
          dt <- maybeToList $ child TPair dt
          dt <- findConv' l (vfst v) dt
          findConv' l (vsnd v) dt
      ]
  VTop x sp ->
    concat
      [ do
          let len = spineLength sp
          dt <- maybeToList $ child (TTop x len) dt
          findConvSpine l sp dt,
        -- eta expand value (function)
        do
          dt <- maybeToList $ child TLam dt
          findConv' (l + 1) (v $$ VVar l) dt,
        -- eta expand value (pair)
        do
          dt <- maybeToList $ child TPair dt
          dt <- findConv' l (vfst v) dt
          findConv' l (vsnd v) dt
      ]
  VU -> maybeToList $ child TU dt
  VPi _ a b -> do
    dt <- maybeToList $ child TPi dt
    dt <- findConv' l a dt
    findConv' (l + 1) (b $ VVar l) dt
  VLam _ v -> do
    -- eta expand trie-side (function)
    tok <- [TLam, TEtaLam]
    dt <- maybeToList $ child tok dt
    findConv' (l + 1) (v $ VVar l) dt
  VSigma _ a b -> do
    dt <- maybeToList $ child TPi dt
    dt <- findConv' l a dt
    findConv' (l + 1) (b $ VVar l) dt
  VPair t u -> do
    -- eta expand trie-side (pair)
    tok <- [TPair, TEtaPair]
    dt <- maybeToList $ child tok dt
    dt <- findConv' l t dt
    findConv' l u dt

findConvSpine :: Level -> Spine -> Trie a -> [Trie a]
findConvSpine l sp dt = case sp of
  SNil -> [dt]
  SApp sp u -> do
    dt <- findConvSpine l sp dt
    dt <- maybeToList $ child TApp dt
    findConv' l u dt
  SFst sp -> do
    dt <- findConvSpine l sp dt
    maybeToList $ child TFst dt
  SSnd sp -> do
    dt <- findConvSpine l sp dt
    maybeToList $ child TSnd dt

--------------------------------------------------------------------------------
-- Prettyprinting

prettyToken :: Token -> ShowS
prettyToken = \case
  TRigid x n -> showString "rigid " . shows x . showString "/" . shows n
  TTop x n -> showString x . showString "/" . shows n
  TU -> showString "U"
  TPi -> showString "Π"
  TLam -> showString "λ"
  TSigma -> showString "Σ"
  TPair -> showString ","
  TApp -> showString "@"
  TFst -> showString ".1"
  TSnd -> showString ".2"
  TEtaLam -> showString "ηλ"
  TEtaPair -> showString "η,"

prettyToken0 :: Token -> String
prettyToken0 tok = prettyToken tok ""

prettyTrieWith :: (a -> ShowS) -> Trie a -> ShowS
prettyTrieWith prettyLeaf = go ""
  where
    go indent = \case
      Leaf x -> showString indent . showString "• " . prettyLeaf x
      One tok t
        | isEtaToken tok -> showString indent . showString "∅"
        | otherwise -> branch indent "└─ " "   " tok t
      Node ts -> branches indent $ filter (not . isEtaToken . fst) $ M.toAscList ts

    branches indent = \case
      [] -> showString indent . showString "∅"
      [(tok, t)] -> branch indent "└─ " "   " tok t
      (tok, t) : ts ->
        branch indent "├─ " "│  " tok t
          . showChar '\n'
          . branches indent ts

    branch indent fork next tok t =
      showString indent
        . showString fork
        . prettyToken tok
        . case t of
          Leaf x -> showString " → " . prettyLeaf x
          One tok' _
            | isEtaToken tok' -> showChar '\n' . showString (indent ++ next) . showString "∅"
          One {} -> showChar '\n' . go (indent ++ next) t
          Node {} -> showChar '\n' . go (indent ++ next) t

prettyTrie :: (Show a) => Trie a -> ShowS
prettyTrie = prettyTrieWith shows

prettyTrie0 :: (Show a) => Trie a -> String
prettyTrie0 t = prettyTrie t ""

prettyIsoTrie :: Trie Iso -> String
prettyIsoTrie t = prettyTrieWith (prettyIso 0) t ""
