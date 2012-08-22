module Lambda where
open import Data.Nat
open import Data.String

data Name : Set where
  global : String → Name
  local : ℕ → Name

data Type : Set where
  α : Name → Type
  _↛_ : (τ τ′ : Type) → Type

data Term↑ : Set
data Term↓ : Set

data Term↑ where
  _∶_ : (e↓ : Term↓) (τ : Type) → Term↑
  χ : Name → Term↑
  _$_ : (e↑ : Term↑) (e↓ : Term↓) → Term↑

data Term↓ where
  _↑ : (e↑ : Term↑) → Term↓
  ƛ : (e↓ : Term↓) → Term↓

data Kind : Set where
  * : Kind


