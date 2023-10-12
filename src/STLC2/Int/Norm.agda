module STLC2.Int.Norm where

open import Prelude

open import Interlude
open import STLC2.Int.TyTerm
open import STLC2.Int.OpSem
open import STLC2.Int.Total
open import STLC2.Int.Readback

private variable
  T : Ty

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
