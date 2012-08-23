module StrongChurch where
open import Data.Nat hiding ( _≟_ )
open import Data.List

data _∈_ {A : Set} (x : A) : List A → Set where
  here : ∀{xs} → x ∈ (x ∷ xs )
  there : ∀{y xs} → x ∈ xs → x ∈ (y ∷ xs)

index : ∀ {A} {x : A} {xs} → x ∈ xs → ℕ
index here = zero
index (there p) = suc (index p)

data Lookup {A : Set} (xs : List A) : ℕ → Set where
  inside : (x : A)(p : x ∈ xs) → Lookup xs (index p)
  outside : (m : ℕ) → Lookup xs (length xs + m)

_!_ : {A : Set} (xs : List A) (n : ℕ) → Lookup xs n
[] ! n = outside n
(x ∷ xs) ! zero = inside x here
(x ∷ xs) ! suc n with xs ! n
(x ∷ xs) ! suc .(index p) | inside y p = inside y (there p)
(x ∷ xs) ! suc .(length xs + n) | outside n = outside n

----------------------------------------------------------------------

data Type : Set where
  ı : Type
  _↛_ : (σ τ : Type) → Type

data Equal? : Type → Type → Set where
  yes : ∀{τ} → Equal? τ τ
  no : ∀{τ τ′} → Equal? τ τ′

_≟_ : (τ τ′ : Type) → Equal? τ τ′
ı ≟ ı = yes
ı ≟ (_ ↛ _) = no
(_ ↛ _) ≟ ı = no
(σ ↛ τ) ≟ (σ′ ↛ τ′) with σ ≟ σ′ | τ ≟ τ′
(σ ↛ τ) ≟ (.σ ↛ .τ) | yes | yes = yes
(_ ↛ _) ≟ (_ ↛ _) | _ | _ = no

data Raw : Set where
  var : ℕ → Raw
  _$_ : (st s : Raw) → Raw
  lam : (σ : Type) (t : Raw) → Raw

Context = List Type

data Term (Γ : Context) : Type → Set where
  var : ∀{τ} → τ ∈ Γ → Term Γ τ
  _$_ : ∀{σ τ} (st : Term Γ (σ ↛ τ)) (t : Term Γ σ) → Term Γ τ
  lam : ∀ σ {τ} (t : Term (σ ∷ Γ) τ) → Term Γ (σ ↛ τ)

erase : ∀{Γ τ} → Term Γ τ → Raw
erase (var p) = var (index p)
erase (st $ s) = erase st $ erase s
erase (lam σ t) = lam σ (erase t)

data Infer (Γ : Context) : Raw → Set where
  ok : (τ : Type) (t : Term Γ τ) → Infer Γ (erase t)
  bad : {t : Raw} → Infer Γ t

infer : (Γ : Context) (t : Raw) → Infer Γ t

infer Γ (var n) with Γ ! n
infer Γ (var .(index p)) | inside τ p = ok τ (var p) 
infer Γ (var .(length Γ + m)) | outside m = bad

infer Γ (st $ s) with infer Γ st
infer Γ (st $ s) | bad = bad
infer Γ (.(erase t) $ s) | ok ı t = bad
infer Γ (.(erase t) $ s) | ok (σ ↛ τ) t
  with infer Γ s
infer Γ (.(erase t) $ s) | ok (σ ↛ τ) t | bad = {!!}
infer Γ (.(erase t) $ .(erase s)) | ok (σ ↛ τ) t | ok σ′ s = {!!}

infer Γ (lam σ t) = {!!}