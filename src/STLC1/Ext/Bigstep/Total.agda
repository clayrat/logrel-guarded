module STLC1.Ext.Bigstep.Total where

open import Prelude
open import Data.Empty
open import Data.List

open import Interlude
open import STLC1.Ext.Term
open import STLC1.Ext.Ty
open import STLC1.Ext.Bigstep.Semantics

infix 4 _⊨_

-- Semantic types (logical predicate)
⟦_⟧ : Ty → Domain → 𝒰
⟦ 𝟙 ⟧     _             = ⊤
⟦ _ ⇒ _ ⟧ (⟨𝓉𝓉⟩)         = ⊥
⟦ S ⇒ T ⟧ (⟨ƛ x ⇒ t ⟩ δ) = ∀ {a} → a ∈ₚ ⟦ S ⟧ → Σ[ b ꞉ Domain ] (δ ﹐ x ↦ a ∣ t ⇓ b) × b ∈ₚ ⟦ T ⟧

-- Semantic typing for environments
_⊨_ : Ctx → Env → 𝒰
Γ ⊨ γ = ∀ {x T} → Γ ∋ x ⦂ T → Σ[ a ꞉ Domain ] (γ ∋ x ↦ a) × a ∈ₚ ⟦ T ⟧

⊨empty : ∅ ⊨ ∅ₑ
⊨empty ∅∋x = absurd (∅-empty ∅∋x)

-- Extending semantically typed environments
_^_ : ∀ {Γ} {γ} {x} {T a}
    → Γ ⊨ γ → a ∈ₚ ⟦ T ⟧
    → Γ , x ⦂ T ⊨ γ ﹐ x ↦ a
_^_ {a} _  sa  here                 = a , hereₑ , sa
_^_     ⊨γ _  (there {x = y} y≠x i) =
  let b , y∈γ , sb = ⊨γ i in
  b , thereₑ y≠x y∈γ , sb

-- Semantic typing for terms
_⊨_⦂_ : Ctx → Term → Ty → 𝒰
Γ ⊨ t ⦂ T = ∀ {γ : Env} → Γ ⊨ γ → Σ[ a ꞉ Domain ] (γ ∣ t ⇓ a) × a ∈ₚ ⟦ T ⟧

-- Well-typed terms are semantically typed
fundamental-lemma : ∀ {Γ t T}
                  → Γ ⊢ t ⦂ T → Γ ⊨ t ⦂ T
fundamental-lemma ⊢𝓉𝓉                      ⊨γ = ⟨𝓉𝓉⟩ , ⇓𝓉𝓉 , tt
fundamental-lemma (⊢` i)                   ⊨γ =
  let a , x∈γ , sa = ⊨γ i in
  a , ⇓` x∈γ , sa
fundamental-lemma (⊢ƛ {x} {N = t} ⊢t) {γ} ⊨γ =
  (⟨ƛ x ⇒ t ⟩ γ) , ⇓ƛ , λ sa → fundamental-lemma ⊢t (⊨γ ^ sa)
fundamental-lemma (⊢r ⊢· ⊢s)             ⊨γ with fundamental-lemma ⊢r ⊨γ
... | ⟨ƛ x ⇒ t ⟩ δ , r⇓ , sf =
        let a , s⇓ , sa = fundamental-lemma ⊢s ⊨γ
            b , f⇓ , sb = sf sa
          in
        b , ⇓· r⇓ s⇓ f⇓ , sb

-- Totality of evaluation for well-typed terms in
-- well-typed environments
⇓-total : ∀ {t T}
        → ∅ ⊢ t ⦂ T → Σ[ a ꞉ Domain ] (∅ₑ ∣ t ⇓ a)
⇓-total ⊢t = let a , t⇓a , _ = fundamental-lemma ⊢t ⊨empty
              in a , t⇓a
