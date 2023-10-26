module STLC1.Int.NbE.Subst where

open import Prelude hiding ([_])
open import Data.Empty
open import Data.Dec

open import STLC1.Int.TyTerm
open import STLC1.Int.NbE.CtxExt

infixr 5 _↥⊢_
infixr 5 _≤⊢_
infix  8 _[_]ʳ
infix  8 _[_]
infix  8 _∷ˢ_
infixr 9 _∘ˢ_
infixr 9 _∘ʳ_

Sub : Ctx → Ctx → 𝒰
Sub Γ Δ = ∀ (T : Ty) → Δ ∋ T → Γ ⊢ T

Ren : Ctx → Ctx → 𝒰
Ren Γ Δ = ∀ (T : Ty) → Δ ∋ T → Γ ∋ T

ren : ∀ {Γ Δ : Ctx} → Ren Γ Δ → Sub Γ Δ
ren ρ T x = ` ρ T x

idʳ : ∀ {Γ : Ctx} → Ren Γ Γ
idʳ T = id

↥ʳ : ∀ {Γ : Ctx} {T : Ty} → Ren (Γ ﹐ T) Γ
↥ʳ T = there

_∘ʳ_ : ∀ {Γ Δ Σ : Ctx} → Ren Δ Γ → Ren Σ Δ → Ren Σ Γ
_∘ʳ_ ρ ω T = ω T ∘ ρ T

ρ-≤ : ∀ {Γ Δ : Ctx} → Γ ≤ Δ → Ren Γ Δ
ρ-≤ {Γ} (≤-id e)   = subst (Ren Γ) e idʳ
ρ-≤     (≤-ext pf) = ρ-≤ pf ∘ʳ ↥ʳ

ρ-≤-id : ∀ {Γ : Ctx} → ρ-≤ ≤-id⁰ ＝ idʳ {Γ}
ρ-≤-id {Γ} = subst-refl {B = Ren Γ} idʳ

ext : ∀ {Γ Δ : Ctx} → Ren Γ Δ → ∀ {T : Ty} → Ren (Γ ﹐ T) (Δ ﹐ T)
ext ρ _  here     = here
ext ρ T (there x) = there (ρ T x)

_[_]ʳ : ∀ {Γ Δ : Ctx} {T : Ty}
      → Δ ⊢ T
      → Ren Γ Δ
        -------
      → Γ ⊢ T
𝓉𝓉      [ ρ ]ʳ = 𝓉𝓉
_[_]ʳ {T} (` x) ρ = ` ρ T x
(ƛ t)   [ ρ ]ʳ = ƛ (t [ ext ρ ]ʳ)
(r · s) [ ρ ]ʳ = (r [ ρ ]ʳ) · (s [ ρ ]ʳ)

exts : ∀ {Γ Δ : Ctx} → Sub Γ Δ → ∀ {T : Ty} → Sub (Γ ﹐ T) (Δ ﹐ T)
exts σ _  here     = ` here
exts σ T (there x) = (σ T x) [ ↥ʳ ]ʳ

_[_] : ∀ {Γ Δ : Ctx} {T : Ty}
     → Δ ⊢ T
     → Sub Γ Δ
       -------
     → Γ ⊢ T
𝓉𝓉      [ σ ] = 𝓉𝓉
_[_] {T} (` x) σ = σ T x
(ƛ t)   [ σ ] = ƛ t [ exts σ ]
(r · s) [ σ ] = (r [ σ ]) · (s [ σ ])

idˢ : ∀ {Γ : Ctx} → Sub Γ Γ
idˢ T = `_

↥ : ∀ {Γ : Ctx} {T : Ty} → Sub (Γ ﹐ T) Γ
↥ T x = ` there x

_∘ˢ_ : ∀ {Γ Δ Σ : Ctx} → Sub Δ Γ → Sub Σ Δ → Sub Σ Γ
_∘ˢ_ σ τ T x = (σ T x) [ τ ]

_∷ˢ_ : ∀ {Γ Δ : Ctx} {S : Ty} → Sub Γ Δ → Γ ⊢ S → Sub Γ (Δ ﹐ S)
(_ ∷ˢ s) _  here     = s
(σ ∷ˢ _) T (there x) = σ T x

weaken : ∀ {Γ Δ : Ctx}
       → Γ ≤ Δ
         --------
       → Sub Γ Δ
weaken pf T x = ` ρ-≤ pf T x

weaken-id : ∀ {Γ : Ctx}
          → weaken ≤-id⁰ ＝ idˢ {Γ}
weaken-id = fun-ext λ T → fun-ext λ x →
              ap (λ q → ` q T x) ρ-≤-id

weaken-ext : ∀ {Γ : Ctx} {T : Ty}
          → weaken (≤-ext ≤-id⁰) ＝ ↥ {Γ} {T}
weaken-ext {Γ} {T} = fun-ext λ S → fun-ext λ x →
                       ap (λ q → ` there {Γ} {S} {T} (q S x))
                          ρ-≤-id

_≤⊢_ : ∀ {Γ Δ : Ctx} {T : Ty}
      → Γ ≤ Δ → Δ ⊢ T → Γ ⊢ T
pf ≤⊢ t = t [ weaken pf ]

_↥⊢_ : ∀ {Γ : Ctx} {T : Ty} → (S : Ty) → Γ ⊢ T → Γ ﹐ S ⊢ T
_ ↥⊢ t = t [ ↥ ]

sub-tail : ∀ {Γ Δ : Ctx} {S : Ty} {s : Γ ⊢ S} {σ : Sub Γ Δ}
         → (↥ ∘ˢ (σ ∷ˢ s)) ＝ σ
sub-tail = refl

sub-dist : ∀ {Γ Δ Σ : Ctx} {S : Ty} {τ : Sub Γ Δ} {σ : Sub Δ Σ} {s : Δ ⊢ S}
         → (σ ∷ˢ s) ∘ˢ τ ＝ σ ∘ˢ τ ∷ˢ (s [ τ ])
sub-dist {Σ} {S} {τ} {σ} {s} = fun-ext λ T → fun-ext (go T)
  where
  go : (T : Ty) → (x : Σ ﹐ S ∋ T) → ((σ ∷ˢ s) ∘ˢ τ) T x ＝ (σ ∘ˢ τ ∷ˢ (s [ τ ])) T x
  go _  here     = refl
  go _ (there x) = refl

-- TODO cong lemmas are redundant w/ homotopical equality
cong-ext : ∀ {Γ Δ : Ctx} {ρ ρ′ : Ren Γ Δ}
         → ρ ＝ ρ′
         → ∀ {T : Ty} → ext ρ {T} ＝ ext ρ′
cong-ext ρ＝ρ′ {T} = ap (λ q → ext q {T}) ρ＝ρ′

cong-rename : ∀ {Γ Δ : Ctx} {ρ ρ′ : Ren Γ Δ} {T : Ty} {t : Δ ⊢ T}
            → ρ ＝ ρ′
            → t [ ρ ]ʳ ＝ t [ ρ′ ]ʳ
cong-rename {t} ρ＝ρ′ = ap (λ q → t [ q ]ʳ) ρ＝ρ′

cong-exts : ∀ {Γ Δ : Ctx} {σ σ′ : Sub Γ Δ}
          → σ ＝ σ′
          → ∀ {T : Ty} → exts σ {T} ＝ exts σ′
cong-exts σ＝σ′ {T} = ap (λ q → exts q {T}) σ＝σ′

cong-sub : ∀ {Γ Δ : Ctx} {σ σ′ : Sub Γ Δ} {T : Ty} {t t′ : Δ ⊢ T}
         → σ ＝ σ′
         → t ＝ t′
         → t [ σ ] ＝ t′ [ σ′ ]
cong-sub {t} {t′} σ＝σ′ t＝t′ = ap² _[_] t＝t′ σ＝σ′

cong-cons : ∀ {Γ Δ : Ctx} {S : Ty} {s s′ : Γ ⊢ S} {σ τ : Sub Γ Δ}
          → s ＝ s′
          → σ ＝ τ
          → σ ∷ˢ s ＝ τ ∷ˢ s′
cong-cons s＝s′ σ＝τ = ap² _∷ˢ_ σ＝τ s＝s′

cong-seq : ∀ {Γ Δ Σ : Ctx} {τ τ′ : Sub Γ Δ} {σ σ′ : Sub Δ Σ}
         → σ ＝ σ′
         → τ ＝ τ′
         → σ ∘ˢ τ ＝ σ′ ∘ˢ τ′
cong-seq σ＝σ′ τ＝τ′ = ap² _∘ˢ_ σ＝σ′ τ＝τ′

ren-ext : ∀ {Γ Δ : Ctx} {S : Ty} {ρ : Ren Γ Δ}
        → ren (ext ρ) ＝ exts (ren ρ) {S}
ren-ext {Δ} {S} {ρ} = fun-ext λ T → fun-ext (go T)
  where
  go : (T : Ty) → (x : Δ ﹐ S ∋ T) → ren (ext ρ) T x ＝ exts (ren ρ) T x
  go _  here     = refl
  go _ (there x) = refl

rename-subst-ren : ∀ {Γ Δ : Ctx} {T : Ty} {ρ : Ren Γ Δ} {t : Δ ⊢ T}
                 → t [ ρ ]ʳ ＝ t [ ren ρ ]
rename-subst-ren {t = 𝓉𝓉}    = refl
rename-subst-ren {t = ` x}   = refl
rename-subst-ren {ρ} {t = ƛ t} =
  ap ƛ_ (rename-subst-ren {ρ = ext ρ} {t}
         ∙ cong-sub {t = t} ren-ext refl)
rename-subst-ren {t = r · s} =
  ap² _·_ rename-subst-ren rename-subst-ren

ren-shift : ∀ {Γ : Ctx} {S : Ty}
          → ren ↥ʳ ＝ ↥ {Γ} {S}
ren-shift {Γ} = fun-ext λ T → fun-ext (go T)
  where
  go : (T : Ty) → (x : Γ ∋ T) → ren ↥ʳ T x ＝ ↥ T x
  go _  here     = refl
  go _ (there x) = refl

rename-shift : ∀ {Γ : Ctx} {S T : Ty} {s : Γ ⊢ S}
             → s [ ↥ʳ {T = T} ]ʳ ＝ s [ ↥ ]
rename-shift {Γ} {S} {T} {s} = rename-subst-ren

exts-cons-shift : ∀ {Γ Δ : Ctx} {S : Ty} {σ : Sub Γ Δ}
                → exts σ {S} ＝ (σ ∘ˢ ↥) ∷ˢ ` here
exts-cons-shift {Δ} {S} {σ} = fun-ext λ T → fun-ext (go T)
  where
  go : (T : Ty) → (x : Δ ﹐ S ∋ T) → exts σ T x ＝ ((σ ∘ˢ ↥) ∷ˢ ` here) T x
  go _  here     = refl
  go T (there x) = rename-subst-ren

exts-idˢ : ∀ {Γ : Ctx} {S : Ty}
         → exts idˢ ＝ idˢ {Γ ﹐ S}
exts-idˢ {Γ} {S} = fun-ext λ T → fun-ext (go T)
  where
  go : (T : Ty) → (x : Γ ﹐ S ∋ T) → exts idˢ T x ＝ idˢ T x
  go _   here     = refl
  go _ (there x) = refl

[id]-identity : ∀ {Γ : Ctx} {T : Ty} {t : Γ ⊢ T}
              → t [ idˢ ] ＝ t
[id]-identity {t = 𝓉𝓉}    = refl
[id]-identity {t = ` x}   = refl
[id]-identity {t = ƛ t}   = ap ƛ_ (cong-sub {t = t} exts-idˢ refl ∙ [id]-identity)
[id]-identity {t = r · s} = ap² _·_ [id]-identity [id]-identity

sub-idR : ∀ {Γ Δ : Ctx} {σ : Sub Γ Δ}
        → σ ∘ˢ idˢ ＝ σ
sub-idR = fun-ext λ _ → fun-ext λ _ → [id]-identity

compose-ext : ∀ {Γ Δ Σ : Ctx} {ρ : Ren Δ Σ} {ω : Ren Γ Δ} {S : Ty}
            → (ext ρ) ∘ʳ (ext ω) ＝ ext (ρ ∘ʳ ω) {S}
compose-ext {Σ} {ρ} {ω} {S} = fun-ext λ T → fun-ext (go T)
  where
  go : (T : Ty) → (x : Σ ﹐ S ∋ T) → ((ext ρ) ∘ʳ (ext ω)) T x ＝ ext (ρ ∘ʳ ω) T x
  go _  here     = refl
  go _ (there x) = refl

compose-rename : ∀ {Γ Δ Σ : Ctx} {T : Ty} {t : Σ ⊢ T} {ω : Ren Γ Δ}
                   {ρ : Ren Δ Σ}
               → t [ ρ ]ʳ [ ω ]ʳ ＝ t [ ρ ∘ʳ ω ]ʳ
compose-rename {t = 𝓉𝓉}    = refl
compose-rename {t = ` x}   = refl
compose-rename {t = ƛ t}   = ap ƛ_ (compose-rename {t = t} ∙ cong-rename compose-ext)
compose-rename {t = r · s} = ap² _·_ compose-rename compose-rename

commute-subst-rename : ∀ {Γ Δ Σ Φ : Ctx} {T : Ty} {t : Σ ⊢ T}
                         {σ : Sub Γ Δ} {ρ : Ren Δ Σ}
                         {ρ′ : Ren Γ Φ} {σ′ : Sub Φ Σ}
                     → (∀ {S : Ty} {x : Σ ∋ S} → σ S (ρ S x) ＝ σ′ S x [ ρ′ ]ʳ)
                     → t [ ρ ]ʳ [ σ ] ＝ t [ σ′ ] [ ρ′ ]ʳ
commute-subst-rename                 {t = 𝓉𝓉}                      pf = refl
commute-subst-rename                 {t = ` x}                     pf = pf
commute-subst-rename {Σ} {T = S ⇒ T} {t = ƛ t}   {σ} {ρ} {ρ′} {σ′} pf =
  ap ƛ_ (commute-subst-rename {t = t} (λ {U} {x} → go U x))
  where
  go : (U : Ty) → (x : Σ ﹐ S ∋ U) → exts σ U (ext ρ U x) ＝ exts σ′ U x [ ext ρ′ ]ʳ
  go _  here     = refl
  go U (there x) =   ap (_[ ↥ʳ ]ʳ) pf
                   ∙ compose-rename {t = σ′ U x} {↥ʳ {T = S}} {ρ′}
                   ∙ sym (compose-rename {t = σ′ U x} {ext ρ′ {S}} {↥ʳ})
commute-subst-rename                 {t = r · s} {σ} {ρ} {ρ′} {σ′} pf =
  ap² _·_ (commute-subst-rename {t = r} {σ} {ρ} {ρ′} {σ′} pf)
          (commute-subst-rename {t = s} {σ} {ρ} {ρ′} {σ′} pf)

sub-there-shift : ∀ {Γ Δ : Ctx} {S T : Ty} {σ : Sub Γ (Δ ﹐ S)} {x : Δ ∋ T}
                → σ T (there x) ＝ (↥ ∘ˢ σ) T x
sub-there-shift = refl

exts-seq : ∀ {Γ Δ Σ : Ctx} {τ : Sub Γ Δ} {σ : Sub Δ Σ} {S : Ty}
         → exts σ ∘ˢ exts τ ＝ exts (σ ∘ˢ τ) {S}
exts-seq {Σ} {τ} {σ} {S} = fun-ext λ T → fun-ext (go T)
  where
  go : (T : Ty) → (x : Σ ﹐ S ∋ T) → (exts σ ∘ˢ exts τ) T x ＝ exts (σ ∘ˢ τ) T x
  go _  here     = refl
  go T (there x) =   sub-there-shift {σ = exts σ ∘ˢ exts τ} {x = x}
                   ∙ commute-subst-rename {t = σ T x} refl

sub-sub : ∀ {Γ Δ Σ : Ctx} {T : Ty} {τ : Sub Γ Δ} {σ : Sub Δ Σ} {t : Σ ⊢ T}
        → t [ σ ] [ τ ] ＝ t [ σ ∘ˢ τ ]
sub-sub         {t = 𝓉𝓉}    = refl
sub-sub         {t = ` x}   = refl
sub-sub {τ} {σ} {t = ƛ t}   = ap ƛ_ (  sub-sub {τ = exts τ} {exts σ} {t}
                                     ∙ cong-sub {t = t} exts-seq refl)
sub-sub         {t = r · s} = ap² _·_ (sub-sub {t = r}) (sub-sub {t = s})

sub-assoc : ∀ {Γ Δ Σ Φ : Ctx} {σ : Sub Δ Γ} {τ : Sub Σ Δ} {θ : Sub Φ Σ}
          → (σ ∘ˢ τ) ∘ˢ θ ＝ (σ ∘ˢ τ ∘ˢ θ)
sub-assoc {σ} {τ} {θ} = fun-ext λ T → fun-ext λ x → sub-sub {τ = θ} {τ} {t = σ T x}

subst-zero-exts-cons : ∀ {Γ Δ : Ctx} {S : Ty} {σ : Sub Γ Δ} {s : Γ ⊢ S}
                     → exts σ ∘ˢ (idˢ ∷ˢ s) ＝ σ ∷ˢ s
subst-zero-exts-cons {S = S} {σ} {s} =
  exts σ ∘ˢ (idˢ ∷ˢ s)
    ＝⟨ cong-seq exts-cons-shift refl ⟩
  ((σ ∘ˢ ↥) ∷ˢ ` here) ∘ˢ (idˢ ∷ˢ s)
    ＝⟨ sub-dist ⟩
  ((σ ∘ˢ ↥) ∘ˢ (idˢ ∷ˢ s)) ∷ˢ s
    ＝⟨ cong-cons refl (sub-assoc {σ = σ}) ⟩
  (σ ∘ˢ ↥ ∘ˢ (idˢ ∷ˢ s)) ∷ˢ s
    ＝⟨ cong-cons refl (cong-seq {σ = σ} refl (sub-tail {s = s} {σ = idˢ})) ⟩
  (σ ∘ˢ idˢ) ∷ˢ s
    ＝⟨ cong-cons refl (sub-idR {σ = σ}) ⟩
  σ ∷ˢ s
    ∎

compose-ρ-≤ : ∀ {Γ″ Γ′ Γ : Ctx} {T : Ty}
            → (Γ″≤Γ′ : Γ″ ≤ Γ′)
            → (Γ′≤Γ : Γ′ ≤ Γ)
            → (x : Γ ∋ T)
            → ρ-≤ Γ″≤Γ′ T (ρ-≤ Γ′≤Γ T x) ＝ ρ-≤ (≤-trans Γ″≤Γ′ Γ′≤Γ) T x
compose-ρ-≤ {Γ″}                        {Γ} {T} (≤-id e)                      Γ′≤Γ                        x =
  J (λ Γ₁ e₁ → (Γ₁≤Γ : Γ₁ ≤ Γ) →
        subst (Ren Γ″) e₁ idʳ T (ρ-≤ Γ₁≤Γ T x) ＝ ρ-≤ (≤-trans (≤-id e₁) Γ₁≤Γ) T x)
    (λ Γ₁≤Γ →   ap (λ q → q T (ρ-≤ Γ₁≤Γ T x)) ρ-≤-id
              ∙ sym (ap (λ q → ρ-≤ q T x) (≤-trans-id-l {ΓΔ = Γ₁≤Γ})))
    e Γ′≤Γ
compose-ρ-≤ {.(Γ″ ﹐ T″)} {Γ′}          {Γ} {T} (≤-ext {Γ = Γ″} {T = T″} pf) (≤-id e)                     x =
  J (λ Γ₀ e₀ → (x₀ : Γ₀ ∋ T) →
       (ρ-≤ pf ∘ʳ ↥ʳ) T (subst (Ren Γ′) e₀ idʳ T x₀) ＝ ρ-≤ (subst (Γ″ ﹐ T″ ≤_) e₀ (≤-ext pf)) T x₀)
    (λ x₀ →   ap (λ q → (ρ-≤ pf ∘ʳ ↥ʳ {T = T″}) T (q T x₀)) ρ-≤-id
            ∙ ap (λ q → ρ-≤ q T x₀) (sym (≤-trans-id-r {ΓΔ = ≤-ext pf})))
    e x
compose-ρ-≤                                     (≤-ext pf1)                  (≤-ext pf2)                  x =
  ap there (compose-ρ-≤ pf1 (≤-ext pf2) x)

compose-weaken : ∀ {Γ″ Γ′ Γ : Ctx} {T : Ty}
               → (Γ″≤Γ′ : Γ″ ≤ Γ′)
               → (Γ′≤Γ : Γ′ ≤ Γ)
               → (t : Γ ⊢ T)
               → Γ″≤Γ′ ≤⊢ Γ′≤Γ ≤⊢ t ＝ (≤-trans Γ″≤Γ′ Γ′≤Γ) ≤⊢ t
compose-weaken Γ″≤Γ′ Γ′≤Γ t =
    sub-sub {τ = weaken Γ″≤Γ′} {weaken Γ′≤Γ} {t}
  ∙ cong-sub {t = t}
      (fun-ext λ T → fun-ext λ x → ap `_ (compose-ρ-≤ Γ″≤Γ′ Γ′≤Γ x))
      refl
