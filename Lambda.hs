module Lambda where
import Prelude hiding (print)

data ITerm
   =  Ann    CTerm Type
   |  Bound  Int
   |  Free   Name
   |  ITerm :@: CTerm
  deriving (Show, Eq)

data CTerm
   =  Inf  ITerm 
   |  Lam  CTerm
  deriving (Show, Eq)

data Type
   =  TFree  Name
   |  Fun    Type Type
  deriving (Show, Eq)

data Value
   =  VLam      (Value -> Value)
   |  VNeutral  Neutral

data Neutral
   =  NFree  Name
   |  NApp   Neutral Value

data Name
   =  Global  String
   |  Local   Int
   |  Quote   Int
  deriving (Show, Eq)

vfree :: Name -> Value
vfree n = VNeutral (NFree n)

vapp :: Value -> Value -> Value
vapp (VLam f) v = f v
vapp (VNeutral n) v = VNeutral (NApp n v)

type Env = [Value]

iEval :: ITerm -> Env -> Value
iEval (Ann ct _)  env = cEval ct env
iEval (Free n)    env = vfree n
iEval (Bound i)   env = env !! i
iEval (it :@: ct) env = vapp (iEval it env) (cEval ct env)

cEval :: CTerm -> Env -> Value
cEval (Inf it) env = iEval it env
cEval (Lam ct) env = VLam (\v -> cEval ct (v:env))

type Result a = Either String a


