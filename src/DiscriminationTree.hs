{-# LANGUAGE OrPatterns #-}

module DiscriminationTree where

import Common
import Control.Applicative
import Control.Monad
import Data.Foldable
import Data.Foldable1
import Data.List.NonEmpty qualified as NE
import Data.Maybe
import Data.Monoid
import Data.Primitive.SmallArray
import Evaluation
import GHC.IsList
import Isomorphism
import Pretty
import Value
import Prelude hiding (curry, lookup)

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
  TEtaLam; TEtaPair -> True
  _ -> False

-- Discrimination tree
data Trie a
  = Leaf a
  | One Token ~(Trie a)
  | Node (SmallArray (Token, Trie a)) -- sorted unique tokens, two or more
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

unions :: NE.NonEmpty (Trie a) -> Trie a
unions = foldl1' union

union :: Trie a -> Trie a -> Trie a
union = unionWith const

unionWith :: (a -> a -> a) -> Trie a -> Trie a -> Trie a
unionWith f = go
  where
    go = \cases
      (Leaf x) (Leaf y) -> Leaf $ f x y
      (One tok t) (One tok' t') -> case compare tok tok' of
        LT -> Node $ smallArrayFromListN 2 [(tok, t), (tok', t')]
        EQ -> One tok $ go t t'
        GT -> Node $ smallArrayFromListN 2 [(tok', t'), (tok, t)]
      (One tok t) (Node ts) -> Node $ insertWith go tok t ts
      (Node ts) (One tok t) -> Node $ insertWith (flip go) tok t ts
      (Node ts) (Node ts') -> Node $ mergeWith go ts ts'
      _ _ -> error "impossible"

insertWith :: (a -> a -> a) -> Token -> a -> SmallArray (Token, a) -> SmallArray (Token, a)
insertWith f tok ~x xs = go 0
  where
    sz = sizeofSmallArray xs

    go i
      | i == sz = createSmallArray (sz + 1) (tok, x) \ys ->
          copySmallArray ys 0 xs 0 i
      | (tok', y) <- indexSmallArray xs i = case compare tok tok' of
          LT -> createSmallArray (sz + 1) (tok, x) \ys -> do
            copySmallArray ys 0 xs 0 i
            copySmallArray ys (i + 1) xs i (sz - i)
          EQ -> runSmallArray do
            xs <- thawSmallArray xs 0 sz
            writeSmallArray xs i (tok, f x y)
            pure xs
          GT -> go (i + 1)

mergeWith :: (a -> a -> a) -> SmallArray (Token, a) -> SmallArray (Token, a) -> SmallArray (Token, a)
mergeWith f xs ys = runSmallArray do
  zs <- newSmallArray cap undefined
  go zs 0 0 0
  pure zs
  where
    sz = sizeofSmallArray xs
    sz' = sizeofSmallArray ys
    cap = sz + sz'

    go zs i j k
      | i == sz = do
          copySmallArray zs k ys j (sz' - j)
          shrinkSmallMutableArray zs (k + sz' - j)
      | j == sz' = do
          copySmallArray zs k xs i (sz - i)
          shrinkSmallMutableArray zs (k + sz - i)
      | otherwise = do
          let p@(tok, t) = indexSmallArray xs i
              p'@(tok', t') = indexSmallArray ys j
          case compare tok tok' of
            LT -> writeSmallArray zs k p >> go zs (i + 1) j (k + 1)
            EQ -> writeSmallArray zs k (tok, f t t') >> go zs (i + 1) (j + 1) (k + 1)
            GT -> writeSmallArray zs k p' >> go zs i (j + 1) (k + 1)

--------------------------------------------------------------------------------
-- Lookup

child :: Token -> Trie a -> Maybe (Trie a)
child tok = \case
  Leaf {} -> error "impossible"
  One tok' ch -> ch <$ guard (tok == tok')
  Node ch -> coerce $ foldMap (\(tok', x) -> First $ x <$ guard (tok == tok')) ch
{-# INLINE child #-}

spineLength :: Spine -> Int
spineLength = \case
  SNil -> 0
  SApp sp _ -> 1 + spineLength sp
  SFst sp -> 1 + spineLength sp
  SSnd sp -> 1 + spineLength sp

findConv :: Level -> Value -> Trie a -> [a]
findConv l v dt = extract <$> findConv' l v dt

findConvIso :: Level -> Value -> Trie Iso -> [Iso]
findConvIso l v dt =
  findConvIso' l v dt <&> \(dt, j) -> extract dt <> sym j

findConvIso' :: Level -> Value -> Trie a -> [(Trie a, Iso)]
findConvIso' l v dt = case v of
  VPi x a b -> do
    dt <- maybeToList $ child TPi dt
    let (VPiArg _ a' b', i) = curry (VPiArg x a b)
    (dt, ia) <- findConvIso' l a' dt
    let v = transportInv ia (VVar l)
    (dt, ib) <- findConvIso' (l + 1) (b' v) dt
    pure $! dt // i <> piCongL ia <> piCongR ib
  VSigma x a b -> do
    dt <- maybeToList $ child TSigma dt
    let (VSigmaArg _ a' b', i) = assoc (VSigmaArg x a b)
    (dt, ia) <- findConvIso' l a' dt
    let v = transportInv ia (VVar l)
    (dt, ib) <- findConvIso' (l + 1) (b' v) dt
    pure $! dt // i <> sigmaCongL ia <> sigmaCongR ib
  v -> (,Refl) <$> findConv' l v dt

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
    dt <- maybeToList $ child TSigma dt
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
      Node ts -> branches indent $ filter (not . isEtaToken . fst) $ GHC.IsList.toList ts

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
