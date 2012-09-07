module Lambda where
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.String
open import Data.List
open import Data.Product
open import Data.Maybe

data Name : Set where
  global : String → Name
  local : ℕ → Name

data Type : Set where
  α : String → Type
  _`→_ : (τ τ′ : Type) → Type

_==Type_ : Type → Type → Bool
α x ==Type α x′ = x == x′
α _ ==Type (_ `→ _) = false
(_ `→ _) ==Type α _ = false
(σ `→ τ) ==Type (σ′ `→ τ′) =
 σ ==Type σ′ ∧ τ ==Type τ′ 

data Term↑ : Set
data Term↓ : Set

data Term↑ where
  _∶_ : (e↓ : Term↓) (τ : Type) → Term↑
  χ : String → Term↑
  _$_ : (e↑ : Term↑) (e↓ : Term↓) → Term↑

data Term↓ where
  _↑ : (e↑ : Term↑) → Term↓
  `λ : (e↓ : Term↓) → Term↓

data Kind : Set where
  ⋆ : Kind

data Info : Set where
  kind : Kind → Info
  type : Type → Info

Context : Set
Context = List (String × Info)

lookup : {A : Set} → String → List (String × A) → Maybe A
lookup s [] = nothing
lookup s ((s′ , a) ∷ xs) with s == s′
... | true = just a
... | false = lookup s xs

kind↓ : Context → Type → Kind → Maybe ⊤
kind↓ ctx (α s) ⋆ with lookup s ctx
... | just (kind ⋆) = just tt
... | just (type _) = nothing
... | nothing = nothing
kind↓ ctx (τ `→ τ′) ⋆ with kind↓ ctx τ ⋆
... | just tt = kind↓ ctx τ′ ⋆
... | nothing = nothing

type↑ : ℕ → Context → Term↑ → Maybe Type
type↓ : ℕ → Context → Term↓ → Type → Maybe ⊤

type↑ n ctx hm = {!!}

type↓ n ctx (e↑ ↑) τ with type↑ n ctx e↑
... | nothing = nothing
... | just τ′ with τ ==Type τ′
... | true = just tt
... | false = nothing
type↓ n ctx (`λ e↓) (τ `→ τ′) = {!!}
type↓ n ctx (`λ e↓) (α _) = nothing
