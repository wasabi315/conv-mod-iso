module Value where

import Common
import Data.Primitive.SmallArray
import Data.String

infixr 5 -->

infixr 6 ***

infixr 5 :*

--------------------------------------------------------------------------------
-- Values

data Value
  = VRigid Level Spine
  | VTop Name Spine
  | VU
  | VPi Name VTyp (Value -> VTyp)
  | VLam Name (Value -> Value)
  | VSigma Name VTyp (Value -> VTyp)
  | VPair Value Value

type VTyp = Value

data VTypKind
  = VKRigid Level
  | VKTop Name
  | VKU
  | VKPi
  | VKSigma
  deriving stock (Eq)

data Spine
  = SNil
  | SApp Spine Value
  | SFst Spine
  | SSnd Spine

pattern VVar :: Level -> Value
pattern VVar x = VRigid x SNil

data VPiArg = VPiArg Name Value (Value -> Value)

data VSigmaArg = VSigmaArg Name Value (Value -> Value)

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

-- sugars

instance HasField "_1" Value Value where
  getField = vfst
  {-# INLINE getField #-}

instance HasField "_2" Value Value where
  getField = vsnd
  {-# INLINE getField #-}

vunpair :: Value -> (Value, Value)
vunpair = \case
  VPair t u -> (t, u)
  VRigid x sp -> (VRigid x (SFst sp), VRigid x (SSnd sp))
  VTop x sp -> (VTop x (SFst sp), VTop x (SSnd sp))
  _ -> error "vunpair: not a pair"

pattern (:*) :: Value -> Value -> Value
pattern t :* u <- (vunpair -> (t, u))
  where
    t :* u = VPair t u

{-# COMPLETE (:*) #-}

{-# INLINE (:*) #-}

(-->) :: VTyp -> VTyp -> VTyp
a --> b = VPi "_" a \ ~_ -> b

(***) :: VTyp -> VTyp -> VTyp
a *** b = VSigma "_" a \ ~_ -> b

instance IsString Value where
  fromString s = VTop s SNil

--------------------------------------------------------------------------------

data Env
  = -- identity environent and chunk
    -- most recent value come first in the chunk
    {-# UNPACK #-} Level :>> {-# UNPACK #-} SmallArray Value
  | Env :> ~Value

emptyEnv :: Env
emptyEnv = 0 :>> mempty

idEnv :: Level -> Env
idEnv = (:>> mempty)

lookupEnv :: Env -> Index -> Value
lookupEnv = \cases
  (l :>> vs) i -> fastLookup l vs i
  env i -> slowLookup env i
  where
    fastLookup (Level l) vs (Index x)
      | x < sz, (# v #) <- indexSmallArray## vs x = v
      | let x' = x - sz, x' < l = VVar (coerce $ l - x' - 1)
      | otherwise = error "lookupEnv: index out of range"
      where
        sz = sizeofSmallArray vs
    {-# INLINE fastLookup #-}

    slowLookup = \cases
      (_ :> v) 0 -> v
      (e :> _) i -> slowLookup e (i - 1)
      (l :>> vs) i -> fastLookup l vs i
{-# INLINE lookupEnv #-}
