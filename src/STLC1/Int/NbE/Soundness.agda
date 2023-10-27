module STLC1.Int.NbE.Soundness where

open import Prelude hiding ([_])
open import Data.Empty
open import Data.Dec
open import Data.Maybe renaming (rec to recᵐ)

open import STLC1.Int.TyTerm
open import STLC1.Int.NbE.CtxExt
open import STLC1.Int.NbE.Subst
open import STLC1.Int.NbE.Norm
open import STLC1.Int.NbE.DefEq
open import STLC1.Int.NbE.Completeness

infix 3 _==^_
infix 3 _==⊤̂_
infix 4 _Ⓡ_
infix 4 _Ⓡˢ_

_==^_ : {Γ : Ctx} {T : Ty} → Γ ⊢ T → Ne^ T → 𝒰
_==^_ {Γ} t 𝓊̂ = recᵐ ⊥ (λ 𝓊-ne → t == 𝓊-ne .fst) (𝓊̂ Γ)

_==⊤̂_ : ∀ {Γ : Ctx} → Γ ⊢ 𝟙 → ⟦ 𝟙 ⟧ᵗ → 𝒰
_==⊤̂_ {Γ} t  unit   = t == 𝓉𝓉
_==⊤̂_ {Γ} t (ne 𝓊̂) = t ==^ 𝓊̂

_Ⓡ_ : ∀ {Γ : Ctx} {T : Ty} → Γ ⊢ T → ⟦ T ⟧ᵗ → 𝒰
_Ⓡ_ {Γ} {T = 𝟙} t 𝓋̂ =
    ∀ {Γ′ : Ctx}
    → (Γ′≤Γ : Γ′ ≤ Γ)
    → Γ′≤Γ ≤⊢ t ==⊤̂ 𝓋̂
_Ⓡ_ {Γ} {S ⇒ T} r f =
    ∀ {Γ′ : Ctx}
    → (Γ′≤Γ : Γ′ ≤ Γ)
    → ∀ {s : Γ′ ⊢ S} {a : ⟦ S ⟧ᵗ}
    → s Ⓡ a
    → (Γ′≤Γ ≤⊢ r) · s Ⓡ f a

==-Ⓡ-trans : ∀ {Γ : Ctx} {T : Ty} {t t′ : Γ ⊢ T} {a : ⟦ T ⟧ᵗ}
           → t == t′
           → t Ⓡ a
             -------
           → t′ Ⓡ a
==-Ⓡ-trans {T = 𝟙}     {t} {t′} {a = unit} t==t′ pf      Γ′≤Γ      =
    begin==
  Γ′≤Γ ≤⊢ t′
    ==⟨ sym⁼⁼ (cong⁼⁼-sub t==t′) ⟩
  Γ′≤Γ ≤⊢ t
    ==⟨ pf Γ′≤Γ ⟩
  𝓉𝓉
    ==∎
==-Ⓡ-trans {T = 𝟙}     {t} {t′} {a = ne 𝓊̂} t==t′ pf {Γ′} Γ′≤Γ     = go (pf Γ′≤Γ)
  where
  go : Γ′≤Γ ≤⊢ t ==^ 𝓊̂ → Γ′≤Γ ≤⊢ t′ ==^ 𝓊̂
  go pf′ with 𝓊̂ Γ′
  ... | just (𝓊 , _) =
           begin==
         Γ′≤Γ ≤⊢ t′
           ==⟨ sym⁼⁼ (cong⁼⁼-sub t==t′) ⟩
         Γ′≤Γ ≤⊢ t
           ==⟨ pf′ ⟩
         𝓊
           ==∎
==-Ⓡ-trans {T = S ⇒ T}          {a}        r==r′ pf      Γ′≤Γ sⓇa =
  ==-Ⓡ-trans r·s==r′·s r·sⓇfa
  where
    r·s==r′·s = app-compat (cong⁼⁼-sub r==r′) refl⁼⁼
    r·sⓇfa = pf Γ′≤Γ sⓇa

Ⓡ-weaken : ∀ {Γ′ Γ : Ctx} {T : Ty} {Γ′≤Γ : Γ′ ≤ Γ} {t : Γ ⊢ T} {a : ⟦ T ⟧ᵗ}
          → t Ⓡ a
          → Γ′≤Γ ≤⊢ t Ⓡ a
Ⓡ-weaken {T = 𝟙}     {Γ′≤Γ} {t} {a} pf Γ″≤Γ′                  =
  subst (_==⊤̂ a)
    (sym $ compose-weaken Γ″≤Γ′ Γ′≤Γ t)
    (pf (≤-trans Γ″≤Γ′ Γ′≤Γ))
Ⓡ-weaken {T = S ⇒ T} {Γ′≤Γ} {t} {a} pf Γ″≤Γ′ {s} {a = b} sⓇa =
  subst (λ q → q · s Ⓡ a b)
    (sym $ compose-weaken Γ″≤Γ′ Γ′≤Γ t)
    (pf (≤-trans Γ″≤Γ′ Γ′≤Γ) sⓇa)

mutual
  ==^→Ⓡ↑ : ∀ {Γ : Ctx} {T : Ty} {𝓊 : Γ ⊢ T} {𝓊̂ : Ne^ T}
          → (∀ {Γ′ : Ctx}
             → (Γ′≤Γ : Γ′ ≤ Γ)
             → Γ′≤Γ ≤⊢ 𝓊 ==^ 𝓊̂)
            -------------------
          → 𝓊 Ⓡ (↑ᵀ 𝓊̂)
  ==^→Ⓡ↑ {T = 𝟙}              pf                        = pf
  ==^→Ⓡ↑ {T = S ⇒ T} {𝓊} {𝓊̂} pf {Γ′} Γ′≤Γ {s} {a} sⓇa =
    ==^→Ⓡ↑ {T = T} 𝓊·s==𝓊̂·↓ˢa
    where
    -- TODO merge
    𝓊·s==𝓊̂·↓ˢa : ∀ {Γ″ : Ctx}
                → (Γ″≤Γ′ : Γ″ ≤ Γ′)
                → Γ″≤Γ′ ≤⊢ (Γ′≤Γ ≤⊢ 𝓊) · s ==^ 𝓊̂ ·^ (↓ᵀ a)
    𝓊·s==𝓊̂·↓ˢa {Γ″} Γ″≤Γ′ = go (pf (≤-trans Γ″≤Γ′ Γ′≤Γ))
      where
      go : ≤-trans Γ″≤Γ′ Γ′≤Γ ≤⊢ 𝓊 ==^ 𝓊̂
         → Γ″≤Γ′ ≤⊢ (Γ′≤Γ ≤⊢ 𝓊) · s ==^ (𝓊̂ ·^ ↓ᵀ a)
      go with 𝓊̂ Γ″
      ... | just (𝓊″ , _) = λ 𝓊==𝓊″ →
          begin==
        Γ″≤Γ′ ≤⊢ (Γ′≤Γ ≤⊢ 𝓊) · s
          ==⟨ app-compat (＝→== (compose-weaken Γ″≤Γ′ Γ′≤Γ 𝓊)) refl⁼⁼ ⟩
        (≤-trans Γ″≤Γ′ Γ′≤Γ ≤⊢ 𝓊) · (Γ″≤Γ′ ≤⊢ s)
          ==⟨ app-compat 𝓊==𝓊″ refl⁼⁼ ⟩
        𝓊″ · (Γ″≤Γ′ ≤⊢ s)
          ==⟨ app-compat refl⁼⁼ (Ⓡ→==↓ sⓇa Γ″≤Γ′) ⟩
        𝓊″ · ↓ᵀ a Γ″ .fst
          ==∎
      ... | nothing = id

  xⓇ↑ᵀ𝓍̂ : ∀ {Γ : Ctx} {T : Ty}
        → ` here {Γ} {T} Ⓡ ↑ᵀ (𝓍̂ T Γ)
  xⓇ↑ᵀ𝓍̂ {T} = ==^→Ⓡ↑ x==𝓍̂
    where
    x==𝓍̂ : ∀ {Γ Γ′ : Ctx}
         → (Γ′≤Γ,T : Γ′ ≤ Γ ﹐ T)
         → Γ′≤Γ,T ≤⊢ ` here ==^ 𝓍̂ T Γ
    x==𝓍̂ {Γ} {Γ′} Γ′≤Γ,T with Γ′ ≤? (Γ ﹐ T)
    ... | yes prf = ＝→== (ap (λ q → ` ρ-≤ q T here) (is-prop-β (≤-is-prop Γ′ (Γ ﹐ T)) Γ′≤Γ,T prf))
    ... | no ctra = ctra Γ′≤Γ,T

  Ⓡ→==↓ : ∀ {Γ′ Γ : Ctx} {T : Ty} {t : Γ ⊢ T} {a : ⟦ T ⟧ᵗ}
        → t Ⓡ a
          ----------------------------
        → (Γ′≤Γ : Γ′ ≤ Γ)
        → Γ′≤Γ ≤⊢ t == ↓ᵀ a Γ′ .fst
  Ⓡ→==↓      {T = 𝟙}         {a = unit} pf      = pf
  Ⓡ→==↓ {Γ′} {T = 𝟙}     {t} {a = ne x} pf Γ′≤Γ = go (pf Γ′≤Γ)
    where
    go : Γ′≤Γ ≤⊢ t ==^ x → Γ′≤Γ ≤⊢ t == ↓ᵀ (ne x) Γ′ .fst
    go with x Γ′
    ... | just tm = id
    ... | nothing = λ e → absurd e
  Ⓡ→==↓ {Γ′} {T = S ⇒ T} {t} {a = f}    pf Γ′≤Γ =
      begin==
    Γ′≤Γ ≤⊢ t
      ==⟨ η ⟩
    ƛ (S ↥⊢ Γ′≤Γ ≤⊢ t) · ` here
      ==⟨ abs-compat go ⟩
    ↓ᵀ f Γ′ .fst
      ==∎
     where
     go : (S ↥⊢ Γ′≤Γ ≤⊢ t) · ` here == ↓ᵀ (f (↑ᵀ (𝓍̂ S Γ′))) (Γ′ ﹐ S) .fst
     go = begin==
        (S ↥⊢ Γ′≤Γ ≤⊢ t) · ` here
          ==⟨ app-compat (＝→== (  sub-sub {τ = ↥} {weaken Γ′≤Γ} {t}
                                ∙ sym [id]-identity))
                         refl⁼⁼ ⟩
        (≤-ext Γ′≤Γ ≤⊢ t) [ idˢ ] · ` here
          ==⟨ app-compat
                (＝→== (sym (ap (λ q → (≤-ext Γ′≤Γ ≤⊢ t) [ q ]) weaken-id)))
                (＝→== (sym (ap (λ q → q S here) weaken-id))) ⟩
        ≤-id⁰ ≤⊢ (≤-ext Γ′≤Γ ≤⊢ t) · ` here
          ==⟨ Ⓡ→==↓ (pf (≤-ext Γ′≤Γ) (xⓇ↑ᵀ𝓍̂ {Γ′} {S}))
                    ≤-id⁰ ⟩
        ↓ᵀ (f (↑ᵀ (𝓍̂ S Γ′))) (Γ′ ﹐ S) .fst
          ==∎

_Ⓡˢ_ : ∀ {Γ Δ : Ctx} → Sub Γ Δ → ⟦ Δ ⟧ᶜ → 𝒰
_Ⓡˢ_ {Δ = Δ} σ δ = ∀ {T : Ty} → (x : Δ ∋ T) → σ T x Ⓡ env-lookup x δ

Ⓡˢ-weaken : ∀ {Γ′ Γ Δ : Ctx} {Γ′≤Γ : Γ′ ≤ Γ} {σ : Sub Γ Δ} {δ : ⟦ Δ ⟧ᶜ}
           → σ Ⓡˢ δ
           → σ ∘ˢ (weaken Γ′≤Γ) Ⓡˢ δ
Ⓡˢ-weaken {Γ′≤Γ = Γ′≤Γ} σⓇδ x = Ⓡ-weaken {Γ′≤Γ = Γ′≤Γ} (σⓇδ x)

_⊨_ : ∀ {T : Ty} → (Δ : Ctx) → Δ ⊢ T → 𝒰
_⊨_ {T} Δ t =
  ∀ {Γ : Ctx} {σ : Sub Γ Δ} {δ : ⟦ Δ ⟧ᶜ}
  → σ Ⓡˢ δ
    -------
  → t [ σ ] Ⓡ ⟦⊢ t ⟧ δ

fundamental-lemma : ∀ {Δ : Ctx} {T : Ty} {t : Δ ⊢ T}
                  → Δ ⊨ t
fundamental-lemma                 {t = 𝓉𝓉}            σⓇδ      _                = refl⁼⁼
fundamental-lemma                 {t = ` x}           σⓇδ                       = σⓇδ x
fundamental-lemma {Δ} {T = S ⇒ T} {t = ƛ t}   {σ} {δ} σⓇδ {Γ′} Γ′≤Γ {s} {a} sⓇa =
  ==-Ⓡ-trans (sym⁼⁼ β) t[exts-σ][s/x]Ⓡ⟦t⟧⟨δ,a⟩
  where

  t[exts-σ] : Γ′ ﹐ S ⊢ T
  t[exts-σ] = t [ exts σ ] [ exts (weaken Γ′≤Γ) ]

  σ∷s : Sub Γ′ (Δ ﹐ S)
  σ∷s = exts σ ∘ˢ exts (weaken Γ′≤Γ) ∘ˢ (idˢ ∷ˢ s)

  subst-lemma₁ : ∀ {U : Ty} {x : Δ ∋ U} → (σ ∘ˢ weaken Γ′≤Γ) U x ＝ σ∷s U (there x)
  subst-lemma₁ {U} {x} =
    (σ ∘ˢ weaken Γ′≤Γ) U x
      ＝⟨⟩
    (σ ∘ˢ ↥ ∘ˢ (weaken Γ′≤Γ ∷ˢ s)) U x
      ＝⟨ ap (λ q → q U x) (sym $ sub-assoc {σ = σ} {↥} {weaken Γ′≤Γ ∷ˢ s}) ⟩
    ((σ ∘ˢ ↥) ∘ˢ (weaken Γ′≤Γ ∷ˢ s)) U x
      ＝⟨⟩
    ((↥ ∘ˢ ((σ ∘ˢ ↥) ∷ˢ ` here)) ∘ˢ (weaken Γ′≤Γ ∷ˢ s)) U x
      ＝⟨⟩
    (↥ ∘ˢ ((σ ∘ˢ ↥) ∷ˢ ` here) ∘ˢ (weaken Γ′≤Γ ∷ˢ s)) U x
      ＝⟨ ap (λ q → q U x) (sym $ cong-seq {σ = ↥} refl (cong-seq {σ = exts σ} exts-cons-shift refl)) ⟩
    (↥ ∘ˢ exts σ ∘ˢ (weaken Γ′≤Γ ∷ˢ s)) U x
      ＝⟨ ap (λ q → q U x) (sym $ cong-seq {σ = ↥ ∘ˢ exts σ} refl subst-zero-exts-cons) ⟩
    (↥ ∘ˢ exts σ ∘ˢ (exts (weaken Γ′≤Γ) ∘ˢ (idˢ ∷ˢ s))) U x
      ＝⟨⟩
    σ∷s U (there x)
      ∎

  subst-lemma₂ : t[exts-σ] [ s ]₀ ＝ t [ σ∷s ]
  subst-lemma₂ =   sub-sub {τ = idˢ ∷ˢ s} {exts (weaken Γ′≤Γ)} {t [ exts σ ]}
                 ∙ sub-sub {τ = exts (weaken Γ′≤Γ) ∘ˢ (idˢ ∷ˢ s)} {exts σ} {t}

  σ∷sⓇ⟨δ,a⟩ : σ∷s Ⓡˢ (δ , a)
  σ∷sⓇ⟨δ,a⟩  here             = sⓇa
  σ∷sⓇ⟨δ,a⟩ (there {A = U} x) =
    subst (_Ⓡ env-lookup x δ)
      subst-lemma₁
      (Ⓡˢ-weaken {Γ′≤Γ = Γ′≤Γ} σⓇδ x)

  t[exts-σ][s/x]Ⓡ⟦t⟧⟨δ,a⟩ : t[exts-σ] [ s ]₀ Ⓡ ⟦⊢ t ⟧ (δ , a)
  t[exts-σ][s/x]Ⓡ⟦t⟧⟨δ,a⟩ =
    subst (_Ⓡ ⟦⊢ t ⟧ (δ , a))
      (sym subst-lemma₂)
      (fundamental-lemma {t = t} σ∷sⓇ⟨δ,a⟩)

fundamental-lemma                 {t = r · s} {σ} {δ} σⓇδ                       =
  let Γ⊨r = fundamental-lemma {t = r} σⓇδ
      Γ⊨s = fundamental-lemma {t = s} σⓇδ
    in
  subst ((λ q → q · s [ σ ] Ⓡ ⟦⊢ r ⟧ δ (⟦⊢ s ⟧ δ)))
    (ap (λ q → (r [ σ ]) [ q ]) weaken-id ∙ [id]-identity {t = r [ σ ]})
    (Γ⊨r (≤-id refl) Γ⊨s)

idⓇ↑Γ : ∀ {Γ : Ctx}
       → idˢ Ⓡˢ (↑ᶜ Γ)
idⓇ↑Γ           here     = xⓇ↑ᵀ𝓍̂
idⓇ↑Γ {Γ ﹐ T} (there x) =
  subst (λ q → ` x [ q ] Ⓡ env-lookup x (↑ᶜ Γ))
        weaken-ext
        (Ⓡ-weaken {Γ′≤Γ = ≤-ext {T = T} ≤-id⁰} {t = ` x} (idⓇ↑Γ {Γ} x))

nf-== : ∀ {Γ : Ctx} {T : Ty} {t : Γ ⊢ T}
      → t == nf t
nf-== {Γ} {T} {t} =
  let tⓇ⟦t⟧↑Γ = fundamental-lemma {t = t} (idⓇ↑Γ {Γ})
      t==↓ᵀ⟦t⟧↑Γ = Ⓡ→==↓ tⓇ⟦t⟧↑Γ ≤-id⁰
    in
  trans⁼⁼
    (＝→== (  sym ([id]-identity {t = t})
            ∙ sym ([id]-identity {t = t [ idˢ ]})
            ∙ ap (λ q → (t [ idˢ ]) [ q ]) (sym weaken-id)))
    t==↓ᵀ⟦t⟧↑Γ

-- aka stability
nf-preserves-meaning : ∀ {Γ : Ctx} {T : Ty} {t : Γ ⊢ T} {γ : ⟦ Γ ⟧ᶜ}
                     → ⟦⊢ t ⟧ γ ＝ ⟦⊢ nf t ⟧ γ
nf-preserves-meaning {t = t} = ==→⟦＝⟧ (nf-== {t = t})

nf-idempotent : ∀ {Γ : Ctx} {T : Ty} {t : Γ ⊢ T}
              → nf t ＝ nf (nf t)
nf-idempotent {t = t} = completeness (nf-== {t = t})

soundness : ∀ {Γ : Ctx} {T : Ty} {t : Γ ⊢ T} {γ : ⟦ Γ ⟧ᶜ }
          → (⟦⊢ t ⟧ γ ＝ ⟦⊢ nf t ⟧ γ) × (nf t ＝ nf (nf t))
soundness {t = t} = nf-preserves-meaning {t = t} , nf-idempotent {t = t}
