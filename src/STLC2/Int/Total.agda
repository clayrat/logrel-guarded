module STLC2.Int.Total where

open import Prelude
open import Data.Empty
open import Data.List

open import Interlude
open import STLC2.Int.TyTerm
open import STLC2.Int.OpSem

infix 4 _⊨_

-- Semantic types (logical predicate)
⟦_⟧ : (T : Ty) → Domain T → 𝒰
⟦ 𝟚 ⟧     _         = ⊤
⟦ S ⇒ T ⟧ (⟨ƛ t ⟩ δ) = ∀ {a} → a ∈ₚ ⟦ S ⟧ → Σ[ b ꞉ Domain T ] (δ ＋＋ a ∣ t ⇓ b) × b ∈ₚ ⟦ T ⟧

-- Semantic typing for environments

_⊨_ : (Γ : Ctx) → Env Γ → 𝒰
Γ ⊨ γ = ∀ {T} → (i : Γ ∋ T) → γ T i ∈ₚ ⟦ T ⟧

⊨empty : ∅ ⊨ empty
⊨empty ()

-- Extending semantically typed environments
_^_ : ∀ {Γ} {γ : Env Γ} {T a}
    → Γ ⊨ γ → a ∈ₚ ⟦ T ⟧ → Γ ﹐ T ⊨ γ ＋＋ a
(_ ^ Ta)  here     = Ta
(⊨γ ^ _) (there i) = ⊨γ i

-- Semantic typing for terms
sem-ty : ∀ {Γ} {T}
       → Γ ⊢ T → 𝒰
sem-ty {Γ} {T} t =
  ∀ {γ : Env Γ} → Γ ⊨ γ → Σ[ a ꞉ Domain T ] (γ ∣ t ⇓ a) × a ∈ₚ ⟦ T ⟧

syntax sem-ty {Γ} {T} t = Γ ⊨ t ⦂ T

-- Syntactic typing implies semantic typing
fundamental-lemma : ∀ {Γ T}
                  → (t : Γ ⊢ T) → Γ ⊨ t ⦂ T
fundamental-lemma {T} (` i)      {γ} ⊨γ =
  γ T i , ⇓` , ⊨γ i
fundamental-lemma     (ƛ t)      {γ} ⊨γ =
  (⟨ƛ t ⟩ γ) , ⇓ƛ , λ Aa → fundamental-lemma t (⊨γ ^ Aa)
fundamental-lemma     (r · s)        ⊨γ with fundamental-lemma r ⊨γ
... | ⟨ƛ t ⟩ δ , r⇓ , sf =
  let a , s⇓ , sa = fundamental-lemma s ⊨γ
      b , t⇓ , sb = sf sa
    in
  b , ⇓· r⇓ s⇓ t⇓ , sb
fundamental-lemma      𝓉             _  =
  ⟨𝓉⟩ , ⇓𝓉 , tt
fundamental-lemma      𝒻            _  =
  ⟨𝒻⟩ , ⇓𝒻 , tt
fundamental-lemma     (⁇ r ↑ s ↓ t) ⊨γ with fundamental-lemma r ⊨γ
... | ⟨𝓉⟩ , r⇓ , _ =
        let a , s⇓ , sa = fundamental-lemma s ⊨γ in
        a , ⇓⁇↑ r⇓ s⇓ , sa
... | ⟨𝒻⟩ , r⇓ , _ =
        let b , s⇓ , sb = fundamental-lemma t ⊨γ in
         b , ⇓⁇↓ r⇓ s⇓ , sb

-- Evaluation is total

⇓-total : ∀ {T}
        → (t : ∅ ⊢ T) → ⇓-well-defined t
⇓-total t = let a , t⇓a , _ = fundamental-lemma t ⊨empty in
            a , t⇓a

