{-# OPTIONS --guarded #-}
module STLC1.Ext.Bigstep.TotalG where

open import Prelude
open import Data.Empty
open import Data.List

open import Later
open import Interlude
open import Guarded.Partial

open import STLC.Ty
open import STLC1.Ext.Term
open import STLC1.Ext.TyTerm
open import STLC1.Ext.Bigstep.Semantics

infix 4 _⊨_

-- guarded version of the logical relation as data

{-
data ⟦_⟧ : Ty → Domain → 𝒰 where

  ⟦𝟙⟧ : ∀ {a}
      → ⟦ 𝟙 ⟧ a

  ⟦⇒⟧ : ∀ {S T x t δ}
      → (∀ {a} → ▹ (a ∈ₚ ⟦ S ⟧) → Part (▹ (Σ[ b ꞉ Domain ] (δ ﹐ x ↦ a ∣ t ⇓ b) × b ∈ₚ ⟦ T ⟧)))
      → ⟦ S ⇒ T ⟧ (⟨ƛ x ⇒ t ⟩ δ)
-}

-- Semantic types (logical predicate)

⟦⟧-case : (Ty → ▹ (Domain → 𝒰)) → Ty → Domain → 𝒰
⟦⟧-case ⟦⟧▹  𝟙       _            = ⊤
⟦⟧-case ⟦⟧▹ (_ ⇒ _) (⟨𝓉𝓉⟩)         = ⊥
⟦⟧-case ⟦⟧▹ (S ⇒ T) (⟨ƛ x ⇒ t ⟩ δ) = ∀ {a} → ▹[ α ] ⟦⟧▹ S α a → Part (▹[ α ] (Σ[ b ꞉ Domain ] (δ ﹐ x ↦ a ∣ t ⇓ b) × ⟦⟧▹ T α b) )

⟦⟧-body : ▹ (Ty → Domain → 𝒰) → Ty → Domain → 𝒰
⟦⟧-body f = ⟦⟧-case (λ T → f ⊛ next T)

⟦_⟧ : Ty → Domain → 𝒰
⟦_⟧ = fix ⟦⟧-body

-- constructors

⟦𝟙⟧ : ∀ {a} → ⟦ 𝟙 ⟧ a
⟦𝟙⟧ = tt

⟦⇒⟧ : ∀ {S T x t δ}
    → (∀ {a} → ▹ (a ∈ₚ ⟦ S ⟧) → Part (▹ (Σ[ b ꞉ Domain ] (δ ﹐ x ↦ a ∣ t ⇓ b) × b ∈ₚ ⟦ T ⟧)))
    → ⟦ S ⇒ T ⟧ (⟨ƛ x ⇒ t ⟩ δ)
⟦⇒⟧ {S} {T} {x} {t} {δ} f {a} sa =
  transport (λ i → ▹[ α ] pfix ⟦⟧-body (~ i) α S a
                 → Part (▹[ α ] (Σ[ b ꞉ Domain ] (δ ﹐ x ↦ a ∣ t ⇓ b)
                                                 × pfix ⟦⟧-body (~ i) α T b)))
            (f {a}) sa

-- destructors

⟦⇒⟧-match : ∀ {S T x t δ}
          → ⟦ S ⇒ T ⟧ (⟨ƛ x ⇒ t ⟩ δ)
          → (∀ {a} → ▹ (a ∈ₚ ⟦ S ⟧) → Part (▹ (Σ[ b ꞉ Domain ] (δ ﹐ x ↦ a ∣ t ⇓ b) × b ∈ₚ ⟦ T ⟧)))
⟦⇒⟧-match {S} {T} {x} {t} {δ} f {a} sa =
  transport (λ i → ▹[ α ] pfix ⟦⟧-body i α S a
                 → Part (▹[ α ] (Σ[ b ꞉ Domain ] (δ ﹐ x ↦ a ∣ t ⇓ b)
                                                × pfix ⟦⟧-body i α T b)))
            (f {a}) sa

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
Γ ⊨ t ⦂ T = ∀ {γ : Env} → Γ ⊨ γ → Part (Σ[ a ꞉ Domain ] (γ ∣ t ⇓ a) × (a ∈ₚ ⟦ T ⟧))

-- Well-typed terms are semantically typed
fundamental-lemma : ∀ {Γ t T}
                  → Γ ⊢ t ⦂ T
                  → Γ ⊨ t ⦂ T
fundamental-lemma ⊢𝓉𝓉                                      _  =
  now (⟨𝓉𝓉⟩ , ⇓𝓉𝓉 , ⟦𝟙⟧ {a = ⟨𝓉𝓉⟩})
fundamental-lemma (⊢` i)                                   ⊨γ =
  let a , x∈γ , sa = ⊨γ i in
  now (a , ⇓` x∈γ , sa)
fundamental-lemma (⊢ƛ {x} {N = t} ⊢t)                  {γ} ⊨γ =
  now ( ⟨ƛ x ⇒ t ⟩ γ
      , ⇓ƛ
      , ⟦⇒⟧ (later ∘ ▹map (λ sa → mapᵖ next
                                      (fundamental-lemma ⊢t (⊨γ ^ sa)))))
fundamental-lemma (_⊢·_ {L = r} {M = s} {A} {B} ⊢r ⊢s) {γ} ⊨γ =
  fundamental-lemma ⊢r ⊨γ >>=ᵖ go
  where
  go : Σ[ a ꞉ Domain ] (γ ∣ r ⇓ a) × (a ∈ₚ ⟦ A ⇒ B ⟧) →
       Part (Σ[ a ꞉ Domain ] (γ ∣ r · s ⇓ a) × (a ∈ₚ ⟦ B ⟧))
  go (⟨ƛ x ⇒ t ⟩ δ , r⇓ , sf′) =
    let sf = ⟦⇒⟧-match sf′ in
    fundamental-lemma ⊢s ⊨γ >>=ᵖ λ where
      (a , s⇓ , sa) →
        later (Part▹ (▹map (λ where (b , f⇓ , sb) → b , ⇓· r⇓ s⇓ f⇓ , sb))
                           (sf (next sa)))

-- Totality of evaluation for well-typed terms in
-- well-typed environments
⇓-total : ∀ {t T}
        → ∅ ⊢ t ⦂ T
        → Part (Σ[ a ꞉ Domain ] (∅ₑ ∣ t ⇓ a))
⇓-total ⊢t = mapᵖ (λ where (a , t⇓a , _) → a , t⇓a)
                   (fundamental-lemma ⊢t ⊨empty)
