module Pretty where

import Common
import Isomorphism
import Term

--------------------------------------------------------------------------------

par :: Int -> Int -> ShowS -> ShowS
par p q = showParen (p > q)

projP, appP, sigmaP, piP, absP, pairP :: Int
projP = 5
appP = 4
sigmaP = 3
piP = 2
absP = 1
pairP = 0

freshen :: [Name] -> Name -> Name
freshen ns n
  | n `elem` ns = go 0
  | otherwise = n
  where
    go (i :: Int)
      | n' `notElem` ns = n'
      | otherwise = go (i + 1)
      where
        n' = n ++ map sub (show i)

    sub = \case
      '0' -> '₀'
      '1' -> '₁'
      '2' -> '₂'
      '3' -> '₃'
      '4' -> '₄'
      '5' -> '₅'
      '6' -> '₆'
      '7' -> '₇'
      '8' -> '₈'
      '9' -> '₉'
      _ -> error "impossible"

prettyTerm0 :: Term -> String
prettyTerm0 t = prettyTerm [] 0 t ""

prettyTerm :: [Name] -> Int -> Term -> ShowS
prettyTerm = go
  where
    go ns p = \case
      Var (Index i) -> showString (ns !! i)
      Top x -> showString x
      U -> showString "U"
      Pi "_" a b ->
        par p piP $ go ns sigmaP a . showString " → " . go ("_" : ns) piP b
      Pi (freshen ns -> n) a b ->
        par p piP $ piBind n ns a . goPi (n : ns) b
      Lam (freshen ns -> n) t ->
        par p absP $
          showString "λ " . showString n . goAbs (n : ns) t
      t :$$ u -> par p appP $ go ns appP t . showChar ' ' . go ns projP u
      Sigma "_" a b ->
        par p sigmaP $ go ns appP a . showString " × " . go ("_" : ns) sigmaP b
      Sigma (freshen ns -> n) a b ->
        par p sigmaP $ piBind n ns a . showString " × " . go (n : ns) sigmaP b
      Fst t -> par p projP $ go ns projP t . showString ".1"
      Snd t -> par p projP $ go ns projP t . showString ".2"
      Pair t u -> par p pairP $ go ns absP t . showString " , " . go ns pairP u

    piBind n ns a =
      showString "("
        . showString n
        . showString " : "
        . go ns pairP a
        . showChar ')'

    goPi ns = \case
      Pi "_" a b -> showString " → " . go ns sigmaP a . showString " → " . go ("_" : ns) piP b
      Pi (freshen ns -> n) a b ->
        showChar ' ' . piBind n ns a . goPi (n : ns) b
      b -> showString " → " . go ns piP b

    goAbs ns = \case
      Lam (freshen ns -> n) t ->
        showChar ' ' . showString n . goAbs (n : ns) t
      t -> showString ". " . go ns absP t

prettyIso0 :: Iso -> String
prettyIso0 i = prettyIso 0 i ""

prettyIso :: Int -> Iso -> ShowS
prettyIso p = \case
  Refl -> showString "refl"
  Sym i -> par p 11 $ prettyIso 12 i . showString " ⁻¹"
  Trans i j -> par p 9 $ prettyIso 9 i . showString " · " . prettyIso 9 j
  Assoc -> showString "Assoc"
  Comm -> showString "Comm"
  SigmaSwap -> showString "ΣSwap"
  Curry -> showString "Curry"
  PiSwap -> showString "ΠSwap"
  PiCongL i -> par p 10 $ showString "ΠL " . prettyIso 11 i
  PiCongR i -> par p 10 $ showString "ΠR " . prettyIso 11 i
  SigmaCongL i -> par p 10 $ showString "ΣL " . prettyIso 11 i
  SigmaCongR i -> par p 10 $ showString "ΣR " . prettyIso 11 i
