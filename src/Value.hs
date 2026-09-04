module Value where

import Common
import Data.SkewList.Lazy (SkewList)
import Data.SkewList.Lazy qualified as SL
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

type Env = SkewList Value

data VPiArg = VPiArg Name Value (Value -> Value)

data VSigmaArg = VSigmaArg Name Value (Value -> Value)

--------------------------------------------------------------------------------

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

emptyEnv :: Env
emptyEnv = SL.empty

idEnv :: Level -> Env
idEnv n = SL.fromList [VVar k | k <- [n - 1, n - 2 .. 0]]
