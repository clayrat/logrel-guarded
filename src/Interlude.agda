module Interlude where

open import Prelude
open import Meta.Variadic
open import Data.Empty
open import Data.Bool
open import Data.Dec renaming (rec to recᵈ)
open import Data.Maybe
open import Data.List
open import Data.String

private variable
  ℓ ℓ′ ℓ″ ℓ‴ : Level
  A : 𝒰 ℓ

-- ap

ap³-simple : {B : 𝒰 ℓ′} {C : 𝒰 ℓ″} {D : 𝒰 ℓ‴}
             {a₁ a₂ : A} {b₁ b₂ : B} {c₁ c₂ : C}
           → (f : A → B → C → D)
           → (p : a₁ ＝ a₂) → (q : b₁ ＝ b₂) → (r : c₁ ＝ c₂)
           → f a₁ b₁ c₁ ＝ f a₂ b₂ c₂
ap³-simple f p q r i = f (p i) (q i) (r i)
{-# INLINE ap³-simple #-}

-- Maybe

extract : A → Maybe A → A
extract d = Data.Maybe.rec d id

-- lookup lists operations

lup : String → List (String × A) → Maybe A
lup k []            = nothing
lup k ((j , x) ∷ l) = recᵈ (λ _ → just x) (λ _ → lup k l) (k ≟ j)

-- TODO formulate with filter
drp : String → List (String × A) → List (String × A)
drp n []              = []
drp n ((m , x) ∷ nxs) = recᵈ (λ _ → drp n nxs) (λ _ → ((m , x)) ∷ drp n nxs) (n ≟ m)

-- bi-implication

_↔_ : 𝒰 ℓ → 𝒰 ℓ′ → 𝒰 (ℓ ⊔ ℓ′)
A ↔ B = (A → B) × (B → A)

-- relation properties

𝒫 : 𝒰 ℓ → 𝒰 (ℓsuc ℓ)
𝒫 {ℓ} X = Corr¹ X ℓ

_∈ₚ_ : A → 𝒫 A → 𝒰 (level-of-type A)
x ∈ₚ P = P x

ℛ : 𝒰 ℓ → 𝒰 (ℓsuc ℓ)
ℛ {ℓ} X = Corr² (X , X) ℓ

normal-form : ℛ A → A → 𝒰 (level-of-type A)
normal-form {A} R x = ¬ Σ[ x′ ꞉ A ] (R x x′)

deterministic : ℛ A → 𝒰 (level-of-type A)
deterministic {A} R = ∀ (x y1 y2 : A) → R x y1 → R x y2 → y1 ＝ y2
