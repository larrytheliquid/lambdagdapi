{-# OPTIONS --no-positivity-check #-}
open import Data.Nat hiding ( _≟_ )
open import Data.String
open import Data.Maybe
open import Data.Product
open import Data.List hiding ( [_] )
module StrongLambda where

infixr 3 Γ⊢e:↑τ Γ⊢e:↓τ
syntax Γ⊢e:↑τ Γ τ (λ e → X) = Γ ⊢ e :↑ τ ⟫ X
syntax Γ⊢e:↓τ Γ τ (λ e → X) = Γ ⊢ e :↓ τ ⟫ X

-----------------------------------------------------------------

⟫_ : ∀{a} {A : Set a} → A → A
⟫ x = x

data _∈_ {A : Set} (x : A) : List A → Set where
  here : ∀{xs} → x ∈ (x ∷ xs )
  there : ∀{y xs} → x ∈ xs → x ∈ (y ∷ xs)

index : ∀ {A} {x : A} {xs} → x ∈ xs → ℕ
index here = zero
index (there p) = suc (index p)

data Lookup {A : Set} (xs : List A) : ℕ → Set where
  inside : (x : A)(p : x ∈ xs) → Lookup xs (index p)
  outside : (m : ℕ) → Lookup xs (length xs + m)

elim-lookup : {A : Set} {xs : List A} {n : ℕ} →
  A → Lookup xs n → A
elim-lookup _ (inside x _) = x
elim-lookup x (outside _) = x

_!_ : {A : Set} (xs : List A) (n : ℕ) → Lookup xs n
[] ! n = outside n
(x ∷ xs) ! zero = inside x here
(x ∷ xs) ! suc n with xs ! n
(x ∷ xs) ! suc .(index p) | inside y p = inside y (there p)
(x ∷ xs) ! suc .(length xs + n) | outside n = outside n

-----------------------------------------------------------------

data Value : Set
data Neutral : Set

data Value where
  [_] : (n : Neutral) → Value
  ⋆ : Value
  Π : (τ : Value) → (τ′ : Value → Value) → Value
  `λ : (λx→v : Value → Value) → Value

data Neutral where
  χ : String → Neutral
  _$_ : (n : Neutral) (v : Value) → Neutral

data Name : Set where
  local : Name
  global : (label : String) → Name

Context = List (Name × Value)
Environment = List Value

data _⊢e:↑_ Context : Value → Set
data _⊢e:↓_ Context : Value → Set
eval↑ : ∀{Γ τ} → Γ ⊢e:↑ τ → Environment → Value
eval↓ : ∀{Γ τ} → Γ ⊢e:↓ τ → Environment → Value

Γ⊢e:↑τ : (Γ : Context) (τ : Value) →
  (Γ ⊢e:↑ τ → Set) → Set
Γ⊢e:↑τ _ _ f = ∀ ρ → f ρ

Γ⊢e:↓τ : (Γ : Context) (τ : Value) →
  (Γ ⊢e:↓ τ → Set) → Set
Γ⊢e:↓τ _ _ f = ∀ ρ → f ρ

data _⊢e:↑_ Γ where
  _:ʳ_ :
    ⟫ Γ ⊢ ρ :↓ ⋆
    ⟫ let τ = eval↓ ρ [] in
    ⟫ Γ ⊢ e :↓ τ
    --------------------
    ⟫ Γ ⊢e:↑ τ

  ⋆ :
    ---------
    Γ ⊢e:↑ ⋆

  Π :
    ⟫ Γ ⊢ ρ :↓ ⋆
    ⟫ let τ = eval↓ ρ [] in
    ⟫ (local , τ) ∷ Γ ⊢ ρ′ :↓ ⋆
    --------------------
    ⟫ Γ ⊢e:↑ ⋆

  χ : ∀{n τ}
    (i : (n , τ) ∈ Γ) →
    --------------
    Γ ⊢e:↑ τ

  _$_ : ∀{τ τ′} →
    ⟫ Γ ⊢ e :↑ Π τ τ′
    ⟫ Γ ⊢ e′ :↓ τ
    ⟫ let τ′′ = τ′ (eval↓ e′ []) in
    --------------------------
    ⟫ Γ ⊢e:↑ τ′′

data _⊢e:↓_ Γ where
  [_] : ∀{τ} →
    ⟫ Γ ⊢ e :↑ τ
    ------------
    ⟫ Γ ⊢e:↓ τ

  `λ : ∀ {τ τ′} →
    ⟫ (local , τ) ∷ Γ ⊢ e :↓ τ′ τ
    ------------------
    ⟫ Γ ⊢e:↓ Π τ τ′

eval↑ (_ :ʳ e) vs = eval↓ e vs
eval↑ ⋆ _ = ⋆
eval↑ (Π ρ ρ′) vs = Π (eval↓ ρ vs) λ v → eval↓ ρ′ (v ∷ vs)
eval↑ (χ {global label} _) _ = [ χ label ]
eval↑ (χ {local} p) vs = elim-lookup
  [ χ "<invalid lookup>" ] (vs ! index p)
eval↑ (e $ e′) vs with eval↑ e vs
... | `λ λx→v = λx→v (eval↓ e′ vs)
... | [ n ] = [ n $ eval↓ e′ vs ]
... | _ = [ χ "<invalid application>" ]

eval↓ [ e ] vs = eval↑ e vs
eval↓ (`λ e) vs = `λ λ v → eval↓ e (v ∷ vs)

-----------------------------------------------------------------

idt : ((global "Bool", ⋆) ∷ []) ⊢e:↑ ⋆
idt = Π [ ⋆ ]
  [ Π [ χ here ] [ χ (there here) ] ]

id' : _ ⊢e:↑ _
id' = [ idt ] :ʳ `λ (`λ [ χ here ])

idBool : _ ⊢e:↑ _
idBool = id' $ [ χ here ]

