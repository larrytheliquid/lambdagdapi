module LambdaPie where
import Prelude hiding (print)
import Control.Monad.Error

data ITerm
   =  Ann    CTerm CTerm
   |  Star
   |  Pi     CTerm CTerm
   |  Bound  Int
   |  Free   Name
   |  ITerm :@: CTerm
  deriving (Show, Eq)

data CTerm
   =  Inf  ITerm 
   |  Lam  CTerm
  deriving (Show, Eq)

data Value
   =  VLam      (Value -> Value)
   |  VStar
   |  VPi Value (Value -> Value)
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
vapp VStar _ = undefined
vapp (VPi _ _) _ = undefined

type Env = [Value]

iEval :: ITerm -> Env -> Value
iEval (Ann ct _)  env = cEval ct env
iEval Star        _   = VStar
iEval (Pi ct ct') env = VPi (cEval ct env) (\v -> cEval ct' (v:env))
iEval (Free x)    _   = vfree x
iEval (Bound i)   env = env !! i
iEval (it :@: ct) env = vapp (iEval it env) (cEval ct env)

cEval :: CTerm -> Env -> Value
cEval (Inf it) env = iEval it env
cEval (Lam ct) env = VLam (\v -> cEval ct (v:env))

type Context = [(Name, Value)]
type Result a = Either String a

check :: Context -> ITerm -> String
check ctx it = case iType0 ctx it of
  Left str -> str
  Right v -> "type: " ++ show (quote0 v)

iType0 :: Context -> ITerm -> Result Value
iType0 = iType 0

iType :: Int -> Context -> ITerm -> Result Value
iType i ctx (Ann ct ct') = do
  cType i ctx ct' VStar
  let tp = cEval ct' []
  cType i ctx ct tp
  return tp
iType  _ _ Star = return VStar
iType i ctx (Pi ct ct') = do
  cType i ctx ct VStar
  let tp = cEval ct []
  cType (succ i) ((Local i, tp):ctx)
    (cSubst 0 (Free (Local i)) ct') VStar
  return VStar
iType _ _ (Bound _) = undefined -- never encountered
iType _ ctx (Free x) =
  case lookup x ctx of
    Just tp   -> return tp
    Nothing   -> throwError ("unknown type identifier: " ++ show x)
iType i ctx (it :@: ct) = do
  tp <- iType i ctx it
  case tp of
    VPi tp' f -> do
      cType i ctx ct tp'
      return (f (cEval ct []))
    _ -> throwError ("illegal application against non-function")

cType :: Int -> Context -> CTerm -> Value -> Result ()
cType i ctx (Inf it) tp = do
  tp' <- iType i ctx it
  unless (quote0 tp == quote0 tp')
    (throwError ("type mismatch: " ++ show (quote0 tp') ++ " vs " ++ show (quote0 tp)))
cType i ctx (Lam ct) (VPi tp f) =
  cType (succ i) ((Local i, tp):ctx)
    (cSubst 0 (Free (Local i)) ct) (f (vfree (Local i)))
cType _ _ (Lam _) _ = throwError $
  "type mismatch / variable rather than function"

cSubst :: Int -> ITerm -> CTerm -> CTerm
cSubst i it (Inf it') = Inf (iSubst i it it')
cSubst i it (Lam ct) = Lam (cSubst (succ i) it ct)

iSubst :: Int -> ITerm -> ITerm -> ITerm
iSubst _ _ Star = Star
iSubst i it (Pi ct ct') = Pi (cSubst i it ct) (cSubst (succ i) it ct')
iSubst i it (Ann ct tp) = Ann (cSubst i it ct) tp
iSubst i it (Bound i') = if i == i' then it else Bound i'
iSubst _ _ (Free x) = Free x
iSubst i it (it' :@: ct) = iSubst i it it' :@: cSubst i it ct

quote0 :: Value -> CTerm
quote0 = quote 0

quote :: Int -> Value -> CTerm
quote i (VLam f) = Lam $ quote (succ i) (f (vfree (Quote i)))
quote i (VNeutral n) = Inf $ neutralQuote i n
quote _ VStar = Inf Star
quote i (VPi v f) = Inf (Pi (quote i v) (quote (succ i) (f (vfree (Quote i)))))

neutralQuote :: Int -> Neutral -> ITerm
neutralQuote i (NFree x) = boundfree i x
neutralQuote i (NApp n v) = neutralQuote i n :@: quote i v

boundfree :: Int -> Name -> ITerm
boundfree i (Quote j) = Bound (i - j - 1)
boundfree _ x = Free x

----------------------------------------------------------------------

bound :: Int -> CTerm
bound x =  Inf $ Bound $ x

-- (A : Set) -> A -> A
idt :: CTerm
idt = Inf $ Pi (Inf Star) (Inf (Pi (bound 0) (bound 1)))

ide :: CTerm
ide = Lam $ Lam $ Inf $ Bound 0

id' :: ITerm
id' = Ann ide idt

idBool :: ITerm
idBool = id' :@: Inf (Free (Global "Bool"))

idFalse :: ITerm
idFalse = idBool :@: Inf (Free (Global "false"))

ctxBool :: Context
ctxBool = [(Global "Bool", VStar), (Global "false", vfree (Global "Bool"))]

-- check [] id'
-- type: Inf (Pi (Inf Star) (Inf (Pi (Inf (Bound 0)) (Inf (Bound 1)))))

-- check ctxBool idBool
-- type: Inf (Pi (Inf (Free (Global \"Bool\"))) (Inf (Free (Global \"Bool\"))))

-- check ctxBool idFalse
-- type: Inf (Free (Global \"Bool\"))
