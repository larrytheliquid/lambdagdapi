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

data Value : Set
data Neutral : Set

data Value where
  ↓ : (n : Neutral) → Value
  ⋆ : Value
  Π : (τ : Value) → (τ′ : Value → Value) → Value
  `λ : (λx→v : Value → Value) → Value

data Neutral where
  χ : String → Neutral
  _$_ : Neutral → Value → Neutral

Context = List Value

data Term↑ Context : Value → Set
data Term↓ Context : Value → Set
eval↑ : ∀{Γ τ} → Term↑ Γ τ → Value
eval↓ : ∀{Γ τ} → Term↓ Γ τ → Value

data Term↑ Γ where
  _∶ʳ_ : (ρ : Term↓ Γ ⋆) →
    let τ = eval↓ ρ in
    Term↓ Γ τ → Term↑ Γ τ
  Π : (ρ : Term↓ Γ ⋆) →
    let τ = eval↓ ρ in
    Term↓ (τ ∷ Γ) ⋆ →
    Term↑ Γ ⋆
  ⋆ : Term↑ Γ ⋆
  χ : ∀{τ} → τ ∈ Γ → Term↑ Γ τ
  _$_ : ∀{τ τ′} →
    (e : Term↑ Γ (Π τ τ′)) →
    (e′ : Term↓ Γ τ) →
    let τ′′ = τ′ (eval↓ e′) in
    Term↑ Γ τ′′

data Term↓ Γ where
  ↓ : ∀{τ} → Term↑ Γ τ → Term↓ Γ τ
  `λ : ∀ {τ τ′} →
    Term↓ (τ ∷ Γ) (τ′ τ) →
    Term↓ Γ (Π τ τ′)

eval↑ (ρ ∶ʳ y) = {!!}
eval↑ (Π ρ y) = {!!}
eval↑ ⋆ = ⋆
eval↑ (χ y) = {!!}
eval↑ (e $ e′) with eval↑ e
... | `λ λx→v = λx→v (eval↓ e′)
... | ↓ n = ↓ (n $ eval↓ e′)
... | x = x -- BAD

eval↓ (↓ e) = eval↑ e
eval↓ (`λ e) = `λ λ _ → eval↓ e