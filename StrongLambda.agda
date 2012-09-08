{-# OPTIONS --no-positivity-check #-}
open import Data.Nat hiding ( _≟_ )
open import Data.String
open import Data.List
module StrongLambda where

data _∈_ {A : Set} (x : A) : List A → Set where
  here : ∀{xs} → x ∈ (x ∷ xs )
  there : ∀{y xs} → x ∈ xs → x ∈ (y ∷ xs)

data Name : Set where
  global : String → Name
  local : ℕ → Name

data Canonical : Set where
  ⋆ : Canonical
  Π : Canonical → (Canonical → Canonical) → Canonical

Context = List Canonical

data Term↑ Context : Canonical → Set
data Term↓ Context : Canonical → Set
postulate eval↑ : ∀{Γ τ} → Term↑ Γ τ → Canonical
postulate eval↓ : ∀{Γ τ} → Term↓ Γ τ → Canonical

data Term↑ Γ where
  _∶_ : (ρ : Term↓ Γ ⋆) →
    let τ = eval↓ ρ in
    Term↓ Γ τ → Term↑ Γ τ
  ⋆ : Term↑ Γ ⋆
  χ : ∀{τ} → τ ∈ Γ → Term↑ Γ τ
  -- _$_ : ∀{τ τ′} → Term↑ Γ (τ `→ τ′) → Term↓ Γ τ → Term↑ Γ τ′

data Term↓ Γ where
  ↓ : ∀{τ} → Term↑ Γ τ → Term↓ Γ τ
  -- `λ : ∀ {τ τ′} → Term↓ (τ ∷ Γ) τ′ → Term↓ Γ (τ `→ τ′)
