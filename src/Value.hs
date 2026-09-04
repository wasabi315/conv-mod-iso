module Value where

import Common
import Data.SkewList.Lazy (SkewList)
import Data.SkewList.Lazy qualified as SL
import Data.String

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

emptyEnv :: Env
emptyEnv = SL.empty

idEnv :: Level -> Env
idEnv n = SL.fromList [VVar k | k <- [n - 1, n - 2 .. 0]]

data VPiArg = VPiArg Name Value (Value -> Value)

data VSigmaArg = VSigmaArg Name Value (Value -> Value)

--------------------------------------------------------------------------------

infixr 5 -->

infixr 6 ***

(-->) :: VTyp -> VTyp -> VTyp
a --> b = VPi "_" a \ ~_ -> b

(***) :: VTyp -> VTyp -> VTyp
a *** b = VSigma "_" a \ ~_ -> b

instance IsString Value where
  fromString s = VTop s SNil

vtyKind :: VTyp -> VTypKind
vtyKind = \case
  VRigid x _ -> VKRigid x
  VTop x _ -> VKTop x
  VU -> VKU
  VPi {} -> VKPi
  VSigma {} -> VKSigma
  _ -> error "impossible"
