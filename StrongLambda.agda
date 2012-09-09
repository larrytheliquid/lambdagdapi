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
syntax Γ⊢ρ:↑τ Γ τ (λ ρ → X) = Γ ⊢ ρ :↑ τ ⇒ X
syntax Γ⊢ρ:↓τ Γ τ (λ ρ → X) = Γ ⊢ ρ :↓ τ ⇒ X
data Term↑ Context : Value → Set
data Term↓ Context : Value → Set
eval↑ : ∀{Γ τ} → ↑ τ ⊣ Γ → Value
eval↓ : ∀{Γ τ} → ↓ τ ⊣ Γ → Value

Γ⊢ρ:↑τ : (Γ : Context) (τ : Value) →
  (Term↑ Γ τ → Set) → Set
Γ⊢ρ:↑τ _ _ f = ∀ ρ → f ρ

Γ⊢ρ:↓τ : (Γ : Context) (τ : Value) →
  (Term↓ Γ τ → Set) → Set
Γ⊢ρ:↓τ _ _ f = ∀ ρ → f ρ

data Term↑ Γ where
  _∶ʳ_ :
      Γ ⊢ ρ :↓ ⋆
   ⇒ let τ = eval↓ ρ in
      Γ ⊢ e :↓ τ
   ⇒ ↑ τ ⊣ Γ

  ⋆ : ↑ ⋆ ⊣ Γ

  Π :
       Γ ⊢ ρ :↓ ⋆
    ⇒ let τ = eval↓ ρ in
       τ ∷ Γ ⊢ ρ′ :↓ ⋆
    ⇒ ↑ ⋆ ⊣ Γ

  χ : ∀{τ}
    (i : τ ∈ Γ) →
    ↑ τ ⊣ Γ

  _$_ : ∀{τ τ′} →
       Γ ⊢ e :↑ Π τ τ′
    ⇒ (Γ ⊢ e′ :↓ τ
    ⇒ let τ′′ = τ′ (eval↓ e′) in
      ↑ τ′′ ⊣ Γ)

data Term↓ Γ where
  ↓ : ∀{τ} →
       Γ ⊢ e :↑ τ
    ⇒ ↓ τ ⊣ Γ
  `λ : ∀ {τ τ′} →
      τ ∷ Γ ⊢ e :↓ τ′ τ
    ⇒ ↓ Π τ τ′ ⊣ Γ

eval↑ (_ ∶ʳ e) = eval↓ e
eval↑ ⋆ = ⋆
eval↑ (Π ρ ρ′) = Π (eval↓ ρ) (λ _ → eval↓ ρ′)
eval↑ (χ {τ} _) = τ -- TODO
eval↑ (e $ e′) with eval↑ e
... | `λ λx→v = λx→v (eval↓ e′)
... | ↓ n = ↓ (n $ eval↓ e′)
... | x = x -- BAD

eval↓ (↓ e) = eval↑ e
eval↓ (`λ e) = `λ λ _ → eval↓ e