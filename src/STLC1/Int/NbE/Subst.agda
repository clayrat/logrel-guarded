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
Sub Γ Δ = ∀ {T : Ty} → Δ ∋ T → Γ ⊢ T

Ren : Ctx → Ctx → 𝒰
Ren Γ Δ = ∀ {T : Ty} → Δ ∋ T → Γ ∋ T

ren : ∀ {Γ Δ : Ctx} → Ren Γ Δ → Sub Γ Δ
ren ρ x = ` ρ x

idʳ : ∀ {Γ : Ctx} → Ren Γ Γ
idʳ = id

↥ʳ : ∀ {Γ : Ctx} {T : Ty} → Ren (Γ ﹐ T) Γ
↥ʳ = there

_∘ʳ_ : ∀ {Γ Δ Σ : Ctx} → Ren Δ Γ → Ren Σ Δ → Ren Σ Γ
ρ ∘ʳ ω = ω ∘ ρ

ρ-≤ : ∀ {Γ Δ : Ctx} → Γ ≤ Δ → Ren Γ Δ
ρ-≤ {Γ} (≤-id  e)  {T} = subst (Ren Γ) e idʳ
ρ-≤     (≤-ext pf)     = ρ-≤ pf ∘ʳ ↥ʳ

ext : ∀ {Γ Δ : Ctx} → Ren Γ Δ → ∀ {T : Ty} → Ren (Γ ﹐ T) (Δ ﹐ T)
ext ρ  here     = here
ext ρ (there x) = there (ρ x)

_[_]ʳ : ∀ {Γ Δ : Ctx} {T : Ty}
      → Δ ⊢ T
      → Ren Γ Δ
        -------
      → Γ ⊢ T
𝓉𝓉      [ ρ ]ʳ = 𝓉𝓉
` x     [ ρ ]ʳ = ` ρ x
(ƛ t)   [ ρ ]ʳ = ƛ (t [ ext ρ ]ʳ)
(r · s) [ ρ ]ʳ = (r [ ρ ]ʳ) · (s [ ρ ]ʳ)

exts : ∀ {Γ Δ : Ctx} → Sub Γ Δ → ∀ {T : Ty} → Sub (Γ ﹐ T) (Δ ﹐ T)
exts σ  here     = ` here
exts σ (there x) = (σ x) [ ↥ʳ ]ʳ

_[_] : ∀ {Γ Δ : Ctx} {T : Ty}
     → Δ ⊢ T
     → Sub Γ Δ
       -------
     → Γ ⊢ T
𝓉𝓉      [ σ ] = 𝓉𝓉
(` x)   [ σ ] = σ x
(ƛ t)   [ σ ] = ƛ t [ exts σ ]
(r · s) [ σ ] = (r [ σ ]) · (s [ σ ])

idˢ : ∀ {Γ : Ctx} → Sub Γ Γ
idˢ = `_

↥ : ∀ {Γ : Ctx} {T : Ty} → Sub (Γ ﹐ T) Γ
↥ x = ` there x

_∘ˢ_ : ∀ {Γ Δ Σ : Ctx} → Sub Δ Γ → Sub Σ Δ → Sub Σ Γ
(σ ∘ˢ τ) x = (σ x) [ τ ]

_∷ˢ_ : ∀ {Γ Δ : Ctx} {S : Ty} → Sub Γ Δ → Γ ⊢ S → Sub Γ (Δ ﹐ S)
(_ ∷ˢ s)  here     = s
(σ ∷ˢ _) (there x) = σ x

weaken : ∀ {Γ Δ : Ctx}
       → Γ ≤ Δ
         --------
       → Sub Γ Δ
weaken pf x = ` ρ-≤ pf x

_≤⊢_ : ∀ {Γ Δ : Ctx} {T : Ty}
      → Γ ≤ Δ → Δ ⊢ T → Γ ⊢ T
pf ≤⊢ t = t [ weaken pf ]

_↥⊢_ : ∀ {Γ : Ctx} {T : Ty} → (S : Ty) → Γ ⊢ T → Γ ﹐ S ⊢ T
_ ↥⊢ t = t [ ↥ ]

sub-tail : ∀ {Γ Δ : Ctx} {S T : Ty} {s : Γ ⊢ S} {σ : Sub Γ Δ}
         → (↥ ∘ˢ (σ ∷ˢ s)) {T = T} ＝ σ
sub-tail = refl

sub-dist : ∀ {Γ Δ Σ : Ctx} {S T : Ty} {τ : Sub Γ Δ} {σ : Sub Δ Σ} {s : Δ ⊢ S}
         → (σ ∷ˢ s) ∘ˢ τ ＝ (σ ∘ˢ τ ∷ˢ (s [ τ ])) {T}
sub-dist {Σ} {S} {T} {τ} {σ} {s} = fun-ext go
  where
  go : (x : Σ ﹐ S ∋ T) → ((σ ∷ˢ s) ∘ˢ τ) x ＝ (σ ∘ˢ τ ∷ˢ (s [ τ ])) x
  go  here     = refl
  go (there x) = refl

cong-ext : ∀ {Γ Δ : Ctx} {ρ ρ′ : Ren Γ Δ} {T : Ty}
         → (∀ {S : Ty} → ρ ＝ ρ′ {S})
         → ∀ {S : Ty} → ext ρ {T} {S} ＝ ext ρ′
cong-ext {Δ} {ρ} {ρ′} {T} ρ＝ρ′ {S} = fun-ext go
  where
  go : (x : Δ ﹐ T ∋ S) → ext ρ x ＝ ext ρ′ x
  go  here     = refl
  go (there x) = ap there (happly ρ＝ρ′ x)

cong-rename : ∀ {Γ Δ : Ctx} {ρ ρ′ : Ren Γ Δ} {T : Ty} {t : Δ ⊢ T}
            → (∀ {S : Ty} → ρ ＝ ρ′ {S})
            → t [ ρ ]ʳ ＝ t [ ρ′ ]ʳ
cong-rename {t = 𝓉𝓉}    ρ＝ρ′ = refl
cong-rename {t = ` x}   ρ＝ρ′ = ap `_ (happly ρ＝ρ′ x)
cong-rename {t = ƛ t}   ρ＝ρ′ = ap ƛ_ (cong-rename {t = t} (cong-ext ρ＝ρ′))
cong-rename {t = r · s} ρ＝ρ′ = ap² _·_ (cong-rename {t = r} ρ＝ρ′) (cong-rename {t = s} ρ＝ρ′)

cong-exts : ∀ {Γ Δ : Ctx} {σ σ′ : Sub Γ Δ} {T : Ty}
          → (∀ {S : Ty} → σ ＝ σ′ {S})
          → (∀ {S : Ty} → exts σ {T} {S} ＝ exts σ′)
cong-exts {Δ} {σ} {σ′} {T} σ＝σ′ {S} = fun-ext go
  where
  go : (x : Δ ﹐ T ∋ S) → exts σ x ＝ exts σ′ x
  go  here     = refl
  go (there x) = ap (_[ there ]ʳ) (happly σ＝σ′ x)

cong-sub : ∀ {Γ Δ : Ctx} {σ σ′ : Sub Γ Δ} {T : Ty} {t t′ : Δ ⊢ T}
         → (∀ {S : Ty} → σ ＝ σ′ {S})
         → t ＝ t′
         → t [ σ ] ＝ t′ [ σ′ ]
cong-sub      {t = 𝓉𝓉} {t′ = 𝓉𝓉}    σ＝σ′ t＝t′ = refl
cong-sub      {t = 𝓉𝓉} {t′ = ` _}   σ＝σ′ t＝t′ = absurd (𝓉𝓉≠` t＝t′)
cong-sub      {t = 𝓉𝓉} {t′ = _ · _} σ＝σ′ t＝t′ = absurd (𝓉𝓉≠· t＝t′)
cong-sub {σ′} {t = ` x}             σ＝σ′ t＝t′ = happly σ＝σ′ x ∙ ap _[ σ′ ] t＝t′
cong-sub {σ′} {t = ƛ t}             σ＝σ′ t＝t′ =
    ap ƛ_ (cong-sub  {σ′ = exts σ′} {t = t} (cong-exts σ＝σ′) refl)
  ∙ ap (_[ σ′ ]) t＝t′
cong-sub {σ′} {t = r · s}           σ＝σ′ t＝t′ =
    ap² _·_ (cong-sub {t = r} σ＝σ′ refl) (cong-sub {t = s} σ＝σ′ refl)
  ∙ ap (_[ σ′ ]) t＝t′

cong-cons : ∀ {Γ Δ : Ctx} {S : Ty} {s s′ : Γ ⊢ S} {σ τ : Sub Γ Δ}
          → s ＝ s′
          → (∀ {T : Ty} → σ {T} ＝ τ {T})
          → ∀ {T : Ty} → σ ∷ˢ s ＝ (τ ∷ˢ s′) {T}
cong-cons {Δ} {S} {s} {s′} {σ} {τ} s＝s′ σ＝τ {T} = fun-ext go
  where
  go : (x : Δ ﹐ S ∋ T) → (σ ∷ˢ s) x ＝ (τ ∷ˢ s′) x
  go  here     = s＝s′
  go (there x) = happly σ＝τ x

cong-seq : ∀ {Γ Δ Σ : Ctx} {τ τ′ : Sub Γ Δ} {σ σ′ : Sub Δ Σ}
         → (∀ {T : Ty} → σ {T} ＝ σ′)
         → (∀ {T : Ty} → τ {T} ＝ τ′)
         → (∀ {T : Ty} → (σ ∘ˢ τ) {T} ＝ σ′ ∘ˢ τ′)
cong-seq {Σ} {τ} {τ′} {σ} {σ′} σ＝σ′ τ＝τ′ {T} =
  fun-ext (λ x → cong-sub {σ = τ} {σ′ = τ′} {t = σ x} {t′ = σ′ x} τ＝τ′ (happly σ＝σ′ x))

ren-ext : ∀ {Γ Δ : Ctx} {S T : Ty} {ρ : Ren Γ Δ}
        → ren (ext ρ) ＝ exts (ren ρ) {S} {T}
ren-ext {Δ} {S} {T} {ρ} = fun-ext go
  where
  go : (x : Δ ﹐ S ∋ T) → (ren (ext ρ)) x ＝ exts (ren ρ) x
  go  here     = refl
  go (there x) = refl

rename-subst-ren : ∀ {Γ Δ : Ctx} {T : Ty} {ρ : Ren Γ Δ} {t : Δ ⊢ T}
                 → t [ ρ ]ʳ ＝ t [ ren ρ ]
rename-subst-ren {t = 𝓉𝓉}    = refl
rename-subst-ren {t = ` x}   = refl
rename-subst-ren {ρ} {t = ƛ t} =
  ap ƛ_ (rename-subst-ren {ρ = ext ρ} {t}
         ∙ cong-sub {t = t} ren-ext refl)
rename-subst-ren {t = r · s} =
  ap² _·_ rename-subst-ren rename-subst-ren

ren-shift : ∀ {Γ : Ctx} {S T : Ty}
          → ren ↥ʳ ＝ ↥ {Γ} {S} {T}
ren-shift {Γ} {T} = fun-ext go
  where
  go : (x : Γ ∋ T) → ren ↥ʳ x ＝ ↥ x
  go  here     = refl
  go (there x) = refl

rename-shift : ∀ {Γ : Ctx} {S T : Ty} {s : Γ ⊢ S}
             → s [ ↥ʳ {T = T} ]ʳ ＝ s [ ↥ ]
rename-shift {Γ} {S} {T} {s} = rename-subst-ren

exts-cons-shift : ∀ {Γ Δ : Ctx} {S T : Ty} {σ : Sub Γ Δ}
                → exts σ {S} {T} ＝ (σ ∘ˢ ↥) ∷ˢ ` here
exts-cons-shift {Δ} {S} {T} {σ} = fun-ext go
  where
  go : (x : Δ ﹐ S ∋ T) → exts σ x ＝ ((σ ∘ˢ ↥) ∷ˢ ` here) x
  go  here     = refl
  go (there x) = rename-subst-ren

exts-idˢ : ∀ {Γ : Ctx} {S T : Ty}
         → exts idˢ ＝ idˢ {Γ ﹐ S} {T}
exts-idˢ {Γ} {S} {T} = fun-ext go
  where
  go : (x : Γ ﹐ S ∋ T) → exts idˢ x ＝ idˢ x
  go  here     = refl
  go (there x) = refl

[id]-identity : ∀ {Γ : Ctx} {T : Ty} {t : Γ ⊢ T}
              → t [ idˢ ] ＝ t
[id]-identity {t = 𝓉𝓉}    = refl
[id]-identity {t = ` x}   = refl
[id]-identity {t = ƛ t}   = ap ƛ_ (cong-sub {t = t} exts-idˢ refl ∙ [id]-identity)
[id]-identity {t = r · s} = ap² _·_ [id]-identity [id]-identity

sub-idR : ∀ {Γ Δ : Ctx} {σ : Sub Γ Δ} {T : Ty}
        → (σ ∘ˢ idˢ) ＝ σ {T}
sub-idR = fun-ext λ _ → [id]-identity

compose-ext : ∀ {Γ Δ Σ : Ctx} {ρ : Ren Δ Σ} {ω : Ren Γ Δ} {S T : Ty}
            → (ext ρ) ∘ʳ (ext ω) ＝ ext (ρ ∘ʳ ω) {S} {T}
compose-ext {Σ} {ρ} {ω} {S} {T} = fun-ext go where
  go : (x : Σ ﹐ S ∋ T) → ((ext ρ) ∘ʳ (ext ω)) x ＝ ext (ρ ∘ʳ ω) x
  go  here     = refl
  go (there x) = refl

compose-rename : ∀ {Γ Δ Σ : Ctx} {T : Ty} {t : Σ ⊢ T} {ω : Ren Γ Δ}
                   {ρ : Ren Δ Σ}
               → t [ ρ ]ʳ [ ω ]ʳ ＝ t [ ρ ∘ʳ ω ]ʳ
compose-rename {t = 𝓉𝓉}    = refl
compose-rename {t = ` x}   = refl
compose-rename {t = ƛ t}   = ap ƛ_ (compose-rename {t = t} ∙ cong-rename compose-ext)
compose-rename {t = r · s} = ap² _·_ compose-rename compose-rename

commute-subst-rename : ∀ {Γ Δ Σ Φ : Ctx} {T : Ty} {t : Σ ⊢ T}
                         {σ : Sub Γ Δ} {ρ : Ren Δ Σ}
                         {ρ′ : Ren Γ Φ } {σ′ : Sub Φ Σ}
                     → (∀ {S : Ty} {x : Σ ∋ S} → σ (ρ x) ＝ σ′ x [ ρ′ ]ʳ)
                     → t [ ρ ]ʳ [ σ ] ＝ t [ σ′ ] [ ρ′ ]ʳ
commute-subst-rename                 {t = 𝓉𝓉}                      pf = refl
commute-subst-rename                 {t = ` x}                     pf = pf
commute-subst-rename {Σ} {T = S ⇒ T} {t = ƛ t}   {σ} {ρ} {ρ′} {σ′} pf =
  ap ƛ_ (commute-subst-rename {t = t} (λ {U} {x} → go x))
  where
  go : ∀ {U : Ty} (x : Σ ﹐ S ∋ U) → exts σ (ext ρ x) ＝ exts σ′ x [ ext ρ′ ]ʳ
  go  here     = refl
  go (there x) =   ap (_[ ↥ʳ ]ʳ) pf
                 ∙ compose-rename {t = σ′ x} {↥ʳ {T = S}} {ρ′}
                 ∙ sym (compose-rename {t = σ′ x} {ext ρ′ {S}} {↥ʳ})
commute-subst-rename                 {t = r · s} {σ} {ρ} {ρ′} {σ′} pf =
  ap² _·_ (commute-subst-rename {t = r} {σ} {ρ} {ρ′} {σ′} pf)
          (commute-subst-rename {t = s} {σ} {ρ} {ρ′} {σ′} pf)

sub-there-shift : ∀ {Γ Δ : Ctx} {S T : Ty} {σ : Sub Γ (Δ ﹐ S)} {x : Δ ∋ T}
                → σ (there x) ＝ (↥ ∘ˢ σ) x
sub-there-shift = refl

exts-seq : ∀ {Γ Δ Σ : Ctx} {τ : Sub Γ Δ} {σ : Sub Δ Σ} {S : Ty}
         → ∀ {T : Ty} → (exts σ ∘ˢ exts τ) ＝ exts (σ ∘ˢ τ) {S} {T}
exts-seq {Σ} {τ} {σ} {S} {T} = fun-ext go
  where
  go : (x : Σ ﹐ S ∋ T) → (exts σ ∘ˢ exts τ) x ＝ exts (σ ∘ˢ τ) x
  go  here     = refl
  go (there x) =   sub-there-shift {σ = exts σ ∘ˢ exts τ} {x = x}
                 ∙ commute-subst-rename {t = σ x} refl

sub-sub : ∀ {Γ Δ Σ : Ctx} {T : Ty} {τ : Sub Γ Δ} {σ : Sub Δ Σ} {t : Σ ⊢ T}
        → t [ σ ] [ τ ] ＝ t [ σ ∘ˢ τ ]
sub-sub         {t = 𝓉𝓉}    = refl
sub-sub         {t = ` x}   = refl
sub-sub {τ} {σ} {t = ƛ t}   = ap ƛ_ (  sub-sub {τ = exts τ} {exts σ} {t}
                                     ∙ cong-sub {t = t} exts-seq refl)
sub-sub         {t = r · s} = ap² _·_ (sub-sub {t = r}) (sub-sub {t = s})

sub-assoc : ∀ {Γ Δ Σ Φ : Ctx} {σ : Sub Δ Γ} {τ : Sub Σ Δ} {θ : Sub Φ Σ}
          → ∀ {T : Ty} → (σ ∘ˢ τ) ∘ˢ θ ＝ (σ ∘ˢ τ ∘ˢ θ) {T}
sub-assoc {σ} {τ} {θ} = fun-ext λ x → sub-sub {τ = θ} {τ} {t = σ x}

subst-zero-exts-cons : ∀ {Γ Δ : Ctx} {S T : Ty} {σ : Sub Γ Δ} {s : Γ ⊢ S}
                     → exts σ ∘ˢ (idˢ ∷ˢ s) ＝ (σ ∷ˢ s) {T}
subst-zero-exts-cons {S = S} {T} {σ} {s} =
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
            → ρ-≤ Γ″≤Γ′ (ρ-≤ Γ′≤Γ x) ＝ ρ-≤ (≤-trans Γ″≤Γ′ Γ′≤Γ) x
compose-ρ-≤ {Γ″}          {Γ′}              {T} (≤-id e″)                    (≤-id e′)                    x =
  J² (λ Γ₁ e₁ Γ₀ e₀ → (x₀ : Γ₀ ∋ T) →
        subst (Ren Γ″) e₁ idʳ (subst (Ren Γ₁) e₀ idʳ x₀) ＝ subst (Ren Γ″) (e₁ ∙ e₀) idʳ x₀)
     (λ x₀ →   ap (λ q → subst (Ren Γ″) refl idʳ (q x₀)) (subst-refl {B = Ren Γ″} idʳ)
             ∙ ap (λ q → q x₀) (subst-refl {B = Ren Γ″} idʳ)
             ∙ ap (λ q → q x₀) (sym (subst-refl {B = Ren Γ″} idʳ))
             ∙ ap (λ q → subst (Ren Γ″) q idʳ x₀) (sym (∙-id-r refl)))
     e″ e′ x
compose-ρ-≤ {Γ″}          {.(Γ′ ﹐ T′)} {Γ}     (≤-id e)                     (≤-ext {Γ = Γ′} {T = T′} pf) x =
  J (λ Γ₂ e₂ →
       subst (Ren Γ₂) (sym e₂) idʳ ((ρ-≤ pf ∘ʳ ↥ʳ) x) ＝ ρ-≤ (subst (_≤ Γ) e₂ (≤-ext pf)) x)
    (  ap (λ q → q ((ρ-≤ pf ∘ʳ ↥ʳ) x)) (subst-refl {B = Ren (Γ′ ﹐ T′)} idʳ)
     ∙ ap (λ q → ρ-≤ q x) (sym (subst-refl {B = _≤ Γ} (≤-ext pf))))
    (sym e)
compose-ρ-≤ {.(Γ″ ﹐ T″)} {Γ′}          {Γ} {T} (≤-ext {Γ = Γ″} {T = T″} pf) (≤-id e)                     x =
  J (λ Γ₀ e₀ → (x₀ : Γ₀ ∋ T) →
       (ρ-≤ pf ∘ʳ ↥ʳ) (subst (Ren Γ′) e₀ idʳ x₀) ＝ ρ-≤ (subst (Γ″ ﹐ T″ ≤_) e₀ (≤-ext pf)) x₀)
    (λ x₀ →   ap (λ q → (ρ-≤ pf ∘ʳ ↥ʳ {T = T″}) (q x₀)) (subst-refl {B = Ren Γ′} idʳ)
            ∙ ap (λ q → ρ-≤ q x₀) (sym (subst-refl {B = Γ″ ﹐ T″ ≤_} (≤-ext pf))))
    e x
compose-ρ-≤                                     (≤-ext pf1)                  (≤-ext pf2)                  x =
  ap there (compose-ρ-≤ pf1 (≤-ext pf2) x)
