module Interlude where

open import Prelude
open import Correspondences.Base using (Corr¹ ; Corr²)
open import Data.Empty
open import Data.Bool
open import Data.Dec
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
lup k ((j , x) ∷ l) = if ⌊ k ≟ j ⌋ then just x else lup k l

-- TODO formulate with filter
drp : String → List (String × A) → List (String × A)
drp n []              = []
drp n ((m , x) ∷ nxs) = if ⌊ n ≟ m ⌋ then drp n nxs else (m , x) ∷ drp n nxs

-- bi-implication

_↔_ : 𝒰 ℓ → 𝒰 ℓ′ → 𝒰 (ℓ ⊔ ℓ′)
A ↔ B = (A → B) × (B → A)

-- relation properties

𝒫 : 𝒰 ℓ → 𝒰 (ℓsuc ℓ)
𝒫 {ℓ} X = Corr¹ ℓ X

_∈ₚ_ : A → 𝒫 A → 𝒰 (level-of-type A)
x ∈ₚ P = P x

ℛ : 𝒰 ℓ → 𝒰 (ℓsuc ℓ)
ℛ {ℓ} X = Corr² ℓ (X , X)

normal-form : ℛ A → A → 𝒰 (level-of-type A)
normal-form {A} R x = ¬ Σ[ x′ ꞉ A ] (R x x′)

deterministic : ℛ A → 𝒰 (level-of-type A)
deterministic {A} R =  ∀ (x y1 y2 : A) → R x y1 → R x y2 → y1 ＝ y2
