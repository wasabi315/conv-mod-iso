module DiscriminationTree where

import Common
import Control.Applicative
import Control.Monad
import Data.Foldable
import Data.Maybe
import Data.Monoid
import Data.Primitive.SmallArray
import Evaluation
import Isomorphism
import PiGenerator
import Pretty
import Value
import Prelude hiding (curry, lookup)

--------------------------------------------------------------------------------

-- Tokens
data Token
  = TRigid Level Int -- spine length
  | TTop Int Name -- spine length first: derived Eq/Ord check the cheap Int before the Name
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
  | Empty
  | One Token ~(Trie a)
  | Node (SmallArray (Token, Trie a)) -- sorted unique tokens, two or more
  deriving stock (Functor, Foldable, Traversable)

extract :: Trie a -> a
extract = \case
  Leaf x -> x
  Empty; One {}; Node {} -> error "extract"

instance Semigroup (Trie a) where
  (<>) = union
  {-# INLINE (<>) #-}

instance Monoid (Trie a) where
  mempty = Empty
  {-# INLINE mempty #-}

union :: Trie a -> Trie a -> Trie a
union = \cases
  t@(Leaf _) ~_ -> t
  Empty t@(One {}; Node {}) -> t
  t@(One {}; Node {}) Empty -> t
  (One tok t) (One tok' t') -> case compare tok tok' of
    LT -> Node $ smallArrayFromListN 2 [(tok, t), (tok', t')]
    EQ -> One tok $ union t t'
    GT -> Node $ smallArrayFromListN 2 [(tok', t'), (tok, t)]
  (One tok t) (Node ts) -> Node $ insertSmallArrayWith union tok t ts
  (Node ts) (One tok t) -> Node $ insertSmallArrayWith (flip union) tok t ts
  (Node ts) (Node ts') -> Node $ mergeSmallArrayWith union ts ts'
  _ _ -> error "impossible"

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
isoTriePi l pi k = isoTriePiGen l (initPiGen l pi) k

isoTriePiGen :: Level -> PiGen -> (Iso -> Trie a) -> Trie a
isoTriePiGen l gen k =
  One TPi do
    flip foldMap'' (domChoices gen) \DomChoice {..} -> case dom of
      VSigma y a1 a2 ->
        flip foldMap'' (assocSwap l (VSigmaArg y a1 a2)) \(VSigmaArg _ a1 a2, j) -> do
          let i' = iso <> piCongL j <> Curry
          isoTrie' l a1 \ia -> do
            let ~u = transportInv ia (VVar l)
                pi = VPiArg name (a2 u) \ ~v -> residual (transportInv j (VPair u v))
            -- do isoTriePi from the start if dom is sigma
            isoTriePi (l + 1) pi \ib ->
              k $! i' <> piCongL ia <> piCongR ib
      a -> isoTrie' l a \ia -> do
        let ~u = transportInv ia (VVar l)
            sub ib = k $! iso <> piCongL ia <> piCongR ib
        case next of
          Nothing -> isoTrie' (l + 1) (residual u) sub
          Just gen' -> isoTriePiGen (l + 1) (gen' u) sub

isoTrieSigma :: Level -> VSigmaArg -> (Iso -> Trie a) -> Trie a
isoTrieSigma l sig k =
  One TSigma do
    flip foldMap'' (assocSwap l sig) \(VSigmaArg _ a b, i) ->
      isoTrie' l a \ia ->
        isoTrie' (l + 1) (b $ transportInv ia (VVar l)) \ib ->
          k $! i <> sigmaCongL ia <> sigmaCongR ib

reflTrie :: Level -> Value -> Trie a -> Trie a
reflTrie l v ~dt = case v of
  VRigid x sp -> etaTrie l (HRigid x) sp dt
  VTop x sp -> etaTrie l (HTop x) sp dt
  VU -> One TU dt
  VPi _ a b ->
    One TPi do
      reflTrie l a do
        reflTrie (l + 1) (b $ VVar l) dt
  VLam _ t ->
    One TLam do
      reflTrie (l + 1) (t $ VVar l) dt
  VSigma _ a b ->
    One TSigma do
      reflTrie l a do
        reflTrie (l + 1) (b $ VVar l) dt
  VPair t u ->
    One TPair do
      reflTrie l t do
        reflTrie l u dt

data Head
  = HRigid Level
  | HTop Name

headToken :: Head -> Int -> Token
headToken = \cases
  (HRigid x) len -> TRigid x len
  (HTop x) len -> TTop len x

-- eta-expand speculatively and infinitely
etaTrie :: Level -> Head -> Spine -> Trie a -> Trie a
etaTrie l hd sp ~dt = do
  let br = reflTrieSpine l hd sp dt
  Node $
    smallArrayFromListN
      3
      [ br,
        (TEtaLam, etaTrie (l + 1) hd (SApp sp (VVar l)) dt),
        (TEtaPair, etaTrie l hd (SFst sp) $ etaTrie l hd (SSnd sp) dt)
      ]

reflTrieSpine :: Level -> Head -> Spine -> Trie a -> (Token, Trie a)
reflTrieSpine l hd = go 0
  where
    go len sp ~dt = case sp of
      SNil -> let tok = headToken hd len in (tok, dt)
      SApp sp u -> go (len + 1) sp (One TApp (reflTrie l u dt))
      SFst sp -> go (len + 1) sp (One TFst dt)
      SSnd sp -> go (len + 1) sp (One TSnd dt)

--------------------------------------------------------------------------------
-- Lookup

child :: Token -> Trie a -> Maybe (Trie a)
child tok = \case
  Leaf {} -> error "impossible"
  Empty -> Nothing
  One tok' ch -> ch <$ guard (tok == tok')
  Node ch -> lookupSmallArray tok ch
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
          dt <- maybeToList $ child (TTop len x) dt
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
  TTop n x -> showString x . showString "/" . shows n
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
      Empty -> showString indent . showString "∅"
      One tok t
        | isEtaToken tok -> showString indent . showString "∅"
        | otherwise -> branch indent "└─ " "   " tok t
      Node ts -> branches indent $ filter (not . isEtaToken . fst) $ toList ts

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
          Empty -> showChar '\n' . showString (indent ++ next) . showString "∅"
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
