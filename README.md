# conv-mod-iso

Conversion checking modulo basic type isomorphisms.

```haskell
foldty1 :: Term
foldty1 = quote 0 $
  VPi "A" VU \a ->
    VPi "B" VU \b ->
      (a --> b --> b)
        --> b
        --> ("List" $$ a)
        --> b

foldty2 :: Term
foldty2 = quote 0 $
  VPi "A" VU \a ->
    VPi "B" VU \b ->
      ("List" $$ a)
        --> ((b *** a --> b) *** b)
        --> b

convIso0 foldty1 foldty2
-- [Sym (PiCongR (PiCongR (Trans (Trans PiSwap Curry) (PiCongL (Trans (PiCongL Comm) Curry)))))]
```
