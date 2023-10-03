module Interlude where

open import Prelude
open import Correspondences.Base using (Corr²)
open import Data.Empty
open import Data.Bool
open import Data.Dec
open import Data.Maybe
open import Data.List
open import Data.String

private variable
  ℓ ℓ′ : Level
  X : 𝒰 ℓ

-- Maybe

extract : X → Maybe X → X
extract d = Data.Maybe.rec d id

-- lookup lists operations

lup : String → List (String × X) → Maybe X
lup k []            = nothing
lup k ((j , x) ∷ l) = if ⌊ k ≟ j ⌋ then just x else lup k l

-- TODO formulate with filter
drp : String → List (String × X) → List (String × X)
drp n []              = []
drp n ((m , x) ∷ nxs) = if ⌊ n ≟ m ⌋ then drp n nxs else (m , x) ∷ drp n nxs

-- bi-implication

_↔_ : 𝒰 ℓ → 𝒰 ℓ′ → 𝒰 (ℓ ⊔ ℓ′)
A ↔ B = (A → B) × (B → A)

-- relation properties

ℛ : 𝒰 ℓ → 𝒰 (ℓsuc ℓ)
ℛ {ℓ} X = Corr² ℓ (X , X)

normal-form : {X : 𝒰 ℓ} → ℛ X → X → 𝒰 ℓ
normal-form {X} R x = ¬ Σ[ x′ ꞉ X ] (R x x′)

deterministic : {X : 𝒰 ℓ} → ℛ X → 𝒰 ℓ
deterministic {X} R =  ∀ (x y1 y2 : X) → R x y1 → R x y2 → y1 ＝ y2
