module Rel where

open import Prelude
open import Correspondences.Base using (Corr²)
open import Data.Empty

private variable
  ℓ : Level

-- relation properties

ℛ : 𝒰 ℓ → 𝒰 (ℓsuc ℓ)
ℛ {ℓ} X = Corr² ℓ (X , X)

normal-form : {X : 𝒰 ℓ} → ℛ X → X → 𝒰 ℓ
normal-form {X} R x = ¬ Σ[ x′ ꞉ X ] (R x x′)

deterministic : {X : 𝒰 ℓ} → ℛ X → 𝒰 ℓ
deterministic {X} R =  ∀ (x y1 y2 : X) → R x y1 → R x y2 → y1 ＝ y2
