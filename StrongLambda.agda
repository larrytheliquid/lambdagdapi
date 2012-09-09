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

syntax Γ⊢e:↑τ Γ τ (λ e → X) = Γ ⊢ e :↑ τ ⇒ X
syntax Γ⊢e:↓τ Γ τ (λ e → X) = Γ ⊢ e :↓ τ ⇒ X
data _⊢e:↑_ Context : Value → Set
data _⊢e:↓_ Context : Value → Set
eval↑ : ∀{Γ τ} → Γ ⊢e:↑ τ → Value
eval↓ : ∀{Γ τ} → Γ ⊢e:↓ τ → Value

Γ⊢e:↑τ : (Γ : Context) (τ : Value) →
  (Γ ⊢e:↑ τ → Set) → Set
Γ⊢e:↑τ _ _ f = ∀ ρ → f ρ

Γ⊢e:↓τ : (Γ : Context) (τ : Value) →
  (Γ ⊢e:↓ τ → Set) → Set
Γ⊢e:↓τ _ _ f = ∀ ρ → f ρ

data _⊢e:↑_ Γ where
  _∶ʳ_ :
      Γ ⊢ ρ :↓ ⋆
   ⇒ let τ = eval↓ ρ in
      Γ ⊢ e :↓ τ
   ⇒ Γ ⊢e:↑ τ

  ⋆ : Γ ⊢e:↑ ⋆

  Π :
       Γ ⊢ ρ :↓ ⋆
    ⇒ let τ = eval↓ ρ in
       τ ∷ Γ ⊢ ρ′ :↓ ⋆
    ⇒ Γ ⊢e:↑ ⋆

  χ : ∀{τ}
    (i : τ ∈ Γ) →
    Γ ⊢e:↑ τ

  _$_ : ∀{τ τ′} →
       Γ ⊢ e :↑ Π τ τ′
    ⇒ (Γ ⊢ e′ :↓ τ
    ⇒ let τ′′ = τ′ (eval↓ e′) in
      Γ ⊢e:↑ τ′′)

data _⊢e:↓_ Γ where
  ↓ : ∀{τ} →
       Γ ⊢ e :↑ τ
    ⇒ Γ ⊢e:↓ τ
  `λ : ∀ {τ τ′} →
      τ ∷ Γ ⊢ e :↓ τ′ τ
    ⇒ Γ ⊢e:↓ Π τ τ′

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