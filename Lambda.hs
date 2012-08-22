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
iType _ _ (Bound _) = undefined -- never encountered
iType _ ctx (Free x) =
  case lookup x ctx of
    Just (HasKind Star) -> undefined
    Just (HasType tp)   -> return tp
    Nothing             -> throwError ("unknown type identifier: " ++ show x)
iType i ctx (it :@: ct) = do
  tp <- iType i ctx it
  case tp of
    Fun tp tp' -> do
      cType i ctx ct tp
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
cType _ _ (Lam _) (TFree x) = throwError $
  "type mismatch / variable rather than function: " ++ show x

cSubst :: Int -> ITerm -> CTerm -> CTerm
cSubst i it (Inf it') = Inf (iSubst i it it')
cSubst i it (Lam ct) = Lam (cSubst (succ i) it ct)

iSubst :: Int -> ITerm -> ITerm -> ITerm
iSubst i it (Ann ct tp) = Ann (cSubst i it ct) tp
iSubst i it (Bound i') = if i == i' then it else Bound i'
iSubst _ _ (Free x) = Free x
iSubst i it (it' :@: ct) = iSubst i it it' :@: cSubst i it ct

quote0 :: Value -> CTerm
quote0 = quote 0

quote :: Int -> Value -> CTerm
quote i (VLam f) = Lam $ quote (succ i) (f (vfree (Quote i)))
quote i (VNeutral n) = Inf $ neutralQuote i n

neutralQuote :: Int -> Neutral -> ITerm
neutralQuote i (NFree x) = boundfree i x
neutralQuote i (NApp n v) = neutralQuote i n :@: quote i v

boundfree :: Int -> Name -> ITerm
boundfree i (Quote j) = Bound (i - j - 1)
boundfree _ x = Free x

----------------------------------------------------------------------

id' :: CTerm
id' = Lam $ Inf $ Bound 0

const' :: CTerm
const' = Lam $ Lam $ Inf $ Bound 1

tfree :: String -> Type
tfree name = TFree $ Global name

free :: String -> CTerm
free name = Inf $ Free $ Global name

term1 :: ITerm
term1 = Ann id' (Fun (tfree "a") (tfree "a")) :@: free "y"

term2 :: ITerm
term2 = Ann const' (Fun
  (Fun (tfree "b") (tfree "b"))
  (Fun (tfree "a")
       (Fun (tfree "b") (tfree "b"))))
  :@: id' :@: free "y"

ctx1 :: Context
ctx1 = [(Global "y", HasType (tfree "a")),
        (Global "a", HasKind Star)]

ctx2 :: Context
ctx2 = [(Global "b", HasKind Star)] ++ ctx1

-- quote0 $ iEval term1 [] = Inf (Free (Global "y"))
-- quote0 $ iEval term2 [] = Lam (Inf (Bound 0))
-- iType0 ctx1 term1 = Right (TFree (Global "a"))
-- iType0 ctx2 term2 = Right (Fun (TFree (Global "b")) (TFree (Global "b")))

