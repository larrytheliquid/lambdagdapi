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
  _$_ : (n : Neutral) (v : Value) → Neutral

Context = List Value

syntax Term↓ Γ τ = ↓ τ ⊣ Γ
syntax Term↑ Γ τ = ↑ τ ⊣ Γ
data Term↑ Context : Value → Set
data Term↓ Context : Value → Set
eval↑ : ∀{Γ τ} → ↑ τ ⊣ Γ → Value
eval↓ : ∀{Γ τ} → ↓ τ ⊣ Γ → Value

data Term↑ Γ where
  _∶ʳ_ :
    (ρ : ↓ ⋆ ⊣ Γ) →
    let τ = eval↓ ρ in
    (e : ↓ τ ⊣ Γ) →
    ↑ τ ⊣ Γ
  Π :
    (ρ : ↓ ⋆ ⊣ Γ) →
    let τ = eval↓ ρ in
    (ρ′ : ↓ ⋆ ⊣ τ ∷ Γ) →
    ↑ ⋆ ⊣ Γ
  ⋆ : ↑ ⋆ ⊣ Γ
  χ : ∀{τ}
    (i : τ ∈ Γ) →
    ↑ τ ⊣ Γ
  _$_ : ∀{τ τ′}
    (e : ↑ Π τ τ′ ⊣ Γ)
    (e′ : ↓ τ ⊣ Γ) →
    let τ′′ = τ′ (eval↓ e′) in
    ↑ τ′′ ⊣ Γ

data Term↓ Γ where
  ↓ : ∀{τ}
    (e : ↑ τ ⊣ Γ) →
    ↓ τ ⊣ Γ
  `λ : ∀ {τ τ′}
    (e : ↓ τ′ τ ⊣ τ ∷ Γ) →
    ↓ Π τ τ′ ⊣ Γ

eval↑ (_ ∶ʳ e) = eval↓ e
eval↑ (Π ρ ρ′) = Π (eval↓ ρ) (λ _ → eval↓ ρ′)
eval↑ ⋆ = ⋆
eval↑ (χ {τ} _) = τ -- TODO
eval↑ (e $ e′) with eval↑ e
... | `λ λx→v = λx→v (eval↓ e′)
... | ↓ n = ↓ (n $ eval↓ e′)
... | x = x -- BAD

eval↓ (↓ e) = eval↑ e
eval↓ (`λ e) = `λ λ _ → eval↓ e