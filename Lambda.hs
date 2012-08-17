module Lambda where
import Prelude hiding (print)
import Control.Monad.Error

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
vfree x = VNeutral (NFree x)

vapp :: Value -> Value -> Value
vapp (VLam f) v = f v
vapp (VNeutral n) v = VNeutral (NApp n v)

type Env = [Value]

iEval :: ITerm -> Env -> Value
iEval (Ann ct _)  env = cEval ct env
iEval (Free x)    _   = vfree x
iEval (Bound i)   env = env !! i
iEval (it :@: ct) env = vapp (iEval it env) (cEval ct env)

cEval :: CTerm -> Env -> Value
cEval (Inf it) env = iEval it env
cEval (Lam ct) env = VLam (\v -> cEval ct (v:env))

data Kind = Star
  deriving (Show)

data Info
  = HasKind Kind
  | HasType Type
  deriving (Show)

type Context = [(Name, Info)]
type Result a = Either String a

cKind :: Context -> Type -> Kind -> Result ()
cKind ctx (TFree x) Star =
  case lookup x ctx of
    Just (HasKind Star) -> return ()
    Just (HasType _)    -> undefined
    Nothing             -> throwError ("unknown kind identifier: " ++ show x)
cKind ctx (Fun tp tp') Star = do
  cKind ctx tp  Star
  cKind ctx tp' Star

iType0 :: Context -> ITerm -> Result Type
iType0 = iType 0

iType :: Int -> Context -> ITerm -> Result Type
iType i ctx (Ann ct tp) = do
  cKind ctx tp Star
  cType i ctx ct tp
  return tp
iType _ _ (Bound _) = undefined
iType _ ctx (Free x) =
  case lookup x ctx of
    Just (HasKind Star) -> undefined
    Just (HasType tp)   -> return tp
    Nothing             -> throwError ("unknown type identifier: " ++ show x)
iType i ctx (it :@: ct) = do
  tp <- iType i ctx it
  case tp of
    Fun _ tp' -> do
      cType i ctx ct tp'
      return tp'
    TFree x -> throwError ("illegal application against non-function: " ++ show x)

cType :: Int -> Context -> CTerm -> Type -> Result ()
cType i ctx (Inf it) tp = do
  tp' <- iType i ctx it
  unless (tp == tp')
    (throwError ("type mismatch: " ++ show tp' ++ " vs " ++ show tp))
cType i ctx (Lam ct) (Fun tp tp') =
  cType (succ i) ((Local i, HasType tp):ctx)
    (cSubst 0 (Free (Local i)) ct) tp'
cType _ _ (Lam _) tp = throwError $
  "type mismatch / expecting function: " ++ show tp

cSubst :: Int -> ITerm -> CTerm -> CTerm
cSubst = undefined
