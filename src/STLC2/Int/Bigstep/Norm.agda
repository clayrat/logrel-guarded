module STLC2.Int.Bigstep.Norm where

open import Prelude
open import Data.Sum

open import Interlude
open import STLC2.Int.TyTerm
open import STLC2.Int.Bigstep.OpSem
open import STLC2.Int.Bigstep.Total

private variable
  Γ Δ : Ctx
  T : Ty

mutual

-- Reading back a normal form from the evaluation of
-- a term. We truly "close" a closure in reading it
-- back to a normal form by replacing every variable
-- in its context using its environment
  _⇑ : Domain T → ∅ ⊢ T
  ⟨𝓉⟩ ⇑        = 𝓉
  ⟨𝒻⟩ ⇑        = 𝒻
  (⟨ƛ t ⟩ γ) ⇑ = ƛ (close γ t)

-- Note that this operation is essentially a
-- substitution
  close : Env Γ → Γ ◇ Δ ⊢ T → Δ ⊢ T
  close {Γ} {T} γ (` i)         = [ (λ j → inject (γ T j ⇑)) , `_ ]ᵤ (split {Γ} i)
  close         γ (ƛ t)         = ƛ close γ t
  close         γ (r · s)       = close γ r · close γ s
  close         γ  𝓉            = 𝓉
  close         γ  𝒻            = 𝒻
  close         γ (⁇ r ↑ s ↓ t) = ⁇ close γ r ↑ close γ s ↓ close γ t

_normalizes-to_ : ∅ ⊢ T → ∅ ⊢ T → 𝒰
_normalizes-to_ {T} t v = Σ[ a ꞉ Domain T ] (empty ∣ t ⇓ a) × (a ⇑ ＝ v)

normalization : (t : ∅ ⊢ T) → Σ[ v ꞉ ∅ ⊢ T ] t normalizes-to v
normalization t with fundamental-lemma t ⊨empty
... | a , t⇓ , _ = (a ⇑) , a , t⇓ , refl

-- Normal form of a term is indeed a normal term
data Value : ∅ ⊢ T → 𝒰 where
  v𝓉 : Value 𝓉
  v𝒻 : Value 𝒻
  vƛ : ∀ {S T}
     → (t : ∅ ﹐ S ⊢ T) → Value (ƛ t)

⇑-Value : (a : Domain T) → Value (a ⇑)
⇑-Value ⟨𝓉⟩        = v𝓉
⇑-Value ⟨𝒻⟩        = v𝒻
⇑-Value (⟨ƛ t ⟩ γ) = vƛ (close γ t)
