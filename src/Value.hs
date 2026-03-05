module Value where

import Common
import Data.String

--------------------------------------------------------------------------------
-- Values

data Value
  = VRigid Level Spine
  | VTop Name Spine
  | VU
  | VPi Name Value (Value -> Value)
  | VLam Name (Value -> Value)
  | VSigma Name Value (Value -> Value)
  | VPair Value Value

data Spine
  = SNil
  | SApp Spine Value
  | SFst Spine
  | SSnd Spine

pattern VVar :: Level -> Value
pattern VVar x = VRigid x SNil

type Env = [Value]

data Quant = Quant Name Value (Value -> Value)

--------------------------------------------------------------------------------

infixr 5 -->

infixr 6 ***

(-->) :: Value -> Value -> Value
a --> b = VPi "_" a \ ~_ -> b

(***) :: Value -> Value -> Value
a *** b = VSigma "_" a \ ~_ -> b

instance IsString Value where
  fromString s = VTop s SNil
