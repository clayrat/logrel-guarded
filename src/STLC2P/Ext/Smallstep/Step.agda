module STLC2P.Ext.Smallstep.Step where

open import Prelude
open import Data.Empty
open import Data.Dec
open import Data.String

open import Interlude
open import STLC2P.Ext.Term

infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  2 _—↠_
infix  3 _∎ᵣ
infix  4 _—→_
infix  9 _[_:=_]

-- substitution

_[_:=_] : Term → Id → Term → Term
(` x) [ y := V ] with x ≟ y
... | yes _              = V
... | no  _              = ` x
(ƛ x ⇒ N) [ y := V ] with x ≟ y
... | yes _              = ƛ x ⇒ N
... | no  _              = ƛ x ⇒ N [ y := V ]
(L · M) [ y := V ]       = L [ y := V ] · M [ y := V ]
𝓉 [ _ := _ ]             = 𝓉
𝒻 [ _ := _ ]             = 𝒻
(⁇ L ↑ M ↓ N) [ y := V ] = (⁇ L [ y := V ] ↑ M [ y := V ] ↓ N [ y := V ])
(〈 L ⹁ M 〉) [ y := V ]     = 〈 L [ y := V ] ⹁ M [ y := V ] 〉
(N ⇀₁) [ y := V ]        = (N [ y := V ] ⇀₁)
(N ⇀₂) [ y := V ]        = (N [ y := V ] ⇀₂)

-- values

data Value : Term → 𝒰 where
  V-ƛ : ∀ {x N} → Value (ƛ x ⇒ N)
  V-𝓉 : Value 𝓉
  V-𝒻 : Value 𝒻
  V-〈〉 : ∀ {L M} → Value L → Value M → Value 〈 L ⹁ M 〉

-- reduction step

data _—→_ : Term → Term → 𝒰 where
  ξ-·₁ : ∀ {L L′ M}
    → L —→ L′
      -----------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {V M M′}
    → Value V
    → M —→ M′
      -----------------
    → V · M —→ V · M′

  β-ƛ : ∀ {x N V}
    → Value V
      ------------------------------
    → (ƛ x ⇒ N) · V —→ N [ x := V ]

  β-𝓉 : ∀ {M N}
      ----------------
    → ⁇ 𝓉 ↑ M ↓ N —→ M

  β-𝒻 : ∀ {M N}
      -----------------
    → ⁇ 𝒻 ↑ M ↓ N —→ N

  ξ-⁇ : ∀ {L L′ M N}
    → L —→ L′
      ---------------------------
    → ⁇ L ↑ M ↓ N —→ ⁇ L′ ↑ M ↓ N

  ξ-〈〉₁ : ∀ {L L′ M}
    → L —→ L′
      --------------------
    → 〈 L ⹁ M 〉 —→ 〈 L′ ⹁ M 〉

  ξ-〈〉₂ : ∀ {L M M′}
    → Value L
    → M —→ M′
      --------------------
    → 〈 L ⹁ M 〉 —→ 〈 L ⹁ M′ 〉

  ξ-⇀₁ : ∀ {L L′}
    → L —→ L′
      -----------------
    → (L ⇀₁) —→ (L′ ⇀₁)

  ξ-⇀₂ : ∀ {L L′}
    → L —→ L′
      -----------------
    → (L ⇀₂) —→ (L′ ⇀₂)

  β-〈〉₁ : ∀ {V₁ V₂}
    → Value V₁
    → Value V₂
      --------------------
    → (〈 V₁ ⹁ V₂ 〉 ⇀₁) —→ V₁

  β-〈〉₂ : ∀ {V₁ V₂}
    → Value V₁
    → Value V₂
      --------------------
    → (〈 V₁ ⹁ V₂ 〉 ⇀₂) —→ V₂

-- step RTC

data _—↠_ : Term → Term → 𝒰 where
  _∎ᵣ : ∀ M
      ---------
    → M —↠ M

  _—→⟨_⟩_ : ∀ L {M N}
    → L —→ M
    → M —↠ N
      ---------
    → L —↠ N

begin_ : ∀ {M N}
  → M —↠ N
    ------
  → M —↠ N
begin M—↠N = M—↠N

-- lifting
^—↠ : ∀ {L M} → L —→ M → L —↠ M
^—↠ {L} {M} LM = L —→⟨ LM ⟩ M ∎ᵣ

-- concatenating
_—↠∘_ : ∀ {L M N} → L —↠ M → M —↠ N → L —↠ N
(_ ∎ᵣ)            —↠∘ LN = LN
(L₀ —→⟨ L₀L ⟩ LM) —↠∘ MN = L₀ —→⟨ L₀L ⟩ (LM —↠∘ MN)

-- appending
_—↠+_ : ∀ {L M N} → L —↠ M → M —→ N → L —↠ N
LM —↠+ MN = LM —↠∘ (^—↠ MN)

-- congruence on multistep
multistep-appr : ∀ {V M M′}
               → Value V
               → M —↠ M′
               → (V · M) —↠ (V · M′)
multistep-appr {V} {M} {.M} VV (.M ∎ᵣ)         = V · M ∎ᵣ
multistep-appr {V} {M} {M′} VV (.M —→⟨ S ⟩ MS) = V · M —→⟨ ξ-·₂ VV S ⟩ multistep-appr VV MS

multistep-test0 : ∀ {L L′ M N}
                → L —↠ L′
                → ⁇ L ↑ M ↓ N —↠ ⁇ L′ ↑ M ↓ N
multistep-test0 {L} {.L} {M} {N} (.L ∎ᵣ)         = ⁇ L ↑ M ↓ N ∎ᵣ
multistep-test0 {L} {L′} {M} {N} (.L —→⟨ S ⟩ MS) = ⁇ L ↑ M ↓ N —→⟨ ξ-⁇ S ⟩ multistep-test0 MS

multistep-pairl : ∀ {L L′ M}
                → L —↠ L′
                → 〈 L ⹁ M 〉 —↠ 〈 L′ ⹁ M 〉
multistep-pairl {L} {.L} {M} (.L ∎ᵣ)         = 〈 L ⹁ M 〉 ∎ᵣ
multistep-pairl {L} {L′} {M} (.L —→⟨ S ⟩ MS) = 〈 L ⹁ M 〉 —→⟨ ξ-〈〉₁ S ⟩ multistep-pairl MS

multistep-pairr : ∀ {L M M′}
                → Value L
                → M —↠ M′
                → 〈 L ⹁ M 〉 —↠ 〈 L ⹁ M′ 〉
multistep-pairr {L} {M} {.M} VL (.M ∎ᵣ)         = 〈 L ⹁ M 〉 ∎ᵣ
multistep-pairr {L} {M} {M′} VL (.M —→⟨ S ⟩ MS) = 〈 L ⹁ M 〉 —→⟨ ξ-〈〉₂ VL S ⟩ multistep-pairr VL MS

multistep-fst : ∀ {L L′}
              → L —↠ L′
              → (L ⇀₁) —↠ (L′ ⇀₁)
multistep-fst {L} {.L} (.L ∎ᵣ)         = L ⇀₁ ∎ᵣ
multistep-fst {L} {L′} (.L —→⟨ S ⟩ MS) = L ⇀₁ —→⟨ ξ-⇀₁ S ⟩ multistep-fst MS

multistep-snd : ∀ {L L′}
              → L —↠ L′
              → (L ⇀₂) —↠ (L′ ⇀₂)
multistep-snd {L} {.L} (.L ∎ᵣ)         = L ⇀₂ ∎ᵣ
multistep-snd {L} {L′} (.L —→⟨ S ⟩ MS) = L ⇀₂ —→⟨ ξ-⇀₂ S ⟩ multistep-snd MS

-- normal form

nf : Term → 𝒰
nf = normal-form _—→_

nf-is-prop : ∀ {t} → is-prop (nf t)
nf-is-prop = ¬-is-prop

value-nf : ∀ {t} → Value t → nf t
value-nf {.(ƛ x ⇒ N)} (V-ƛ {x} {N})        (M , ())
value-nf {.(〈 L ⹁ M 〉)} (V-〈〉 {L} {M} VL VM) (.(〈 L′ ⹁ M 〉) , ξ-〈〉₁ {L′} st)   = value-nf VL (L′ , st)
value-nf {.(〈 L ⹁ M 〉)} (V-〈〉 {L} {M} VL VM) (.(〈 L ⹁ M′ 〉) , ξ-〈〉₂ {M′} _ st) = value-nf VM (M′ , st)

-- context invariance

-- appears free in
data afi : Id → Term → 𝒰 where
  afi-var   : ∀ {x} → afi x (` x)
  afi-appl  : ∀ {x M N} → afi x M → afi x (M · N)
  afi-appr  : ∀ {x M N} → afi x N → afi x (M · N)
  afi-abs   : ∀ {x y N} → x ≠ y → afi x N → afi x (ƛ y ⇒ N)
  -- booleans
  afi-test0 : ∀ {x L M N} → afi x L → afi x (⁇ L ↑ M ↓ N)
  afi-test1 : ∀ {x L M N} → afi x M → afi x (⁇ L ↑ M ↓ N)
  afi-test2 : ∀ {x L M N} → afi x N → afi x (⁇ L ↑ M ↓ N)
  -- pairs
  afi-pairl : ∀ {x L M} → afi x L → afi x (〈 L ⹁ M 〉)
  afi-pairr : ∀ {x L M} → afi x M → afi x (〈 L ⹁ M 〉)
  afi-fst   : ∀ {x L} → afi x L → afi x (L ⇀₁)
  afi-snd   : ∀ {x L} → afi x L → afi x (L ⇀₂)

closed : Term → 𝒰
closed t = ∀ i → ¬ afi i t

-- determinism

step-det : deterministic _—→_
step-det .(L · M)          .(L₁ · M)         .(L₂ · M)        (ξ-·₁ {L} {L′ = L₁} {M} LL₁)       (ξ-·₁ {L′ = L₂} LL₂)       =
  ap (_· M) (step-det L L₁ L₂ LL₁ LL₂)
step-det .(L · M₁)         .(L′ · M₁)        .(L · M₂)        (ξ-·₁ {L} {L′} {M = M₁} LL′)       (ξ-·₂ {M′ = M₂} VL _)      =
  absurd (value-nf VL (L′ , LL′))
step-det .(L · M)          .(L · M′)         .(L′ · M)        (ξ-·₂ {V = L} {M} {M′} VL _)       (ξ-·₁ {L′} LL′)            =
  absurd (value-nf VL (L′ , LL′))
step-det .(L · M)          .(L · M₁)         .(L · M₂)        (ξ-·₂ {V = L} {M} {M′ = M₁} _ MM₁) (ξ-·₂ {M′ = M₂} _ MM₂)     =
  ap (L ·_) (step-det M M₁ M₂ MM₁ MM₂)
step-det .((ƛ x ⇒ N) · M₁) .((ƛ x ⇒ N) · M₂) .(N [ x := M₁ ]) (ξ-·₂ {M′ = M₂} _ M₁₂)             (β-ƛ {x} {N} {V = M₁} VM₁) =
  absurd (value-nf VM₁ (M₂ , M₁₂))
step-det .((ƛ x ⇒ N) · L)  .(N [ x := L ])   .((ƛ x ⇒ N) · M) (β-ƛ {x} {N} {V = L} VL)           (ξ-·₂ {M′ = M} _ LM)       =
  absurd (value-nf VL (M , LM))
step-det .((ƛ _ ⇒ _) · _)  .(N [ x := V ])   .(N [ x := V ])  (β-ƛ {x} {N} {V} VV)               (β-ƛ _)                    =
  refl
step-det .(⁇ 𝓉 ↑ M ↓ _)     M               .M                 β-𝓉                                β-𝓉                       =
  refl
step-det .(⁇ 𝒻 ↑ _ ↓ N)    N               .N                 β-𝒻                                β-𝒻                       =
  refl
step-det .(⁇ L ↑ M ↓ N)    .(⁇ L₁ ↑ M ↓ N)  .(⁇ L₂ ↑ M ↓ N)   (ξ-⁇ {L} {L′ = L₁} {M} {N} LL₁)    (ξ-⁇ {L′ = L₂} LL₂)        =
  ap (λ q → ⁇ q ↑ M ↓ N) (step-det L L₁ L₂ LL₁ LL₂)
step-det .(〈 L ⹁ M 〉)        .(〈 L₁ ⹁ M 〉)     .(〈 L₂ ⹁ M 〉)       (ξ-〈〉₁ {L} {L′ = L₁} {M} LL₁)       (ξ-〈〉₁ {L} {L′ = L₂} LL₂)   =
  ap (λ q → 〈 q ⹁ M 〉) (step-det L L₁ L₂ LL₁ LL₂)
step-det .(〈 L ⹁ _ 〉)       .(〈 L₁ ⹁ _ 〉)      .(〈 L ⹁ _ 〉)        (ξ-〈〉₁ {L} {L′ = L₁} LL₁)           (ξ-〈〉₂ VL _)                =
  absurd (value-nf VL (L₁ , LL₁))
step-det .(〈 L ⹁ _ 〉)       .(〈 L ⹁ _ 〉)       .(〈 L₂ ⹁ _ 〉)       (ξ-〈〉₂ {L} VL _)                    (ξ-〈〉₁ {L′ = L₂} LL₂)       =
  absurd (value-nf VL (L₂ , LL₂))
step-det .(〈 L ⹁ M 〉)       .(〈 L ⹁ M₁ 〉)      .(〈 L ⹁ M₂ 〉)       (ξ-〈〉₂ {L} {M} {M′ = M₁} VL MM₁)    (ξ-〈〉₂ {M′ = M₂} _ MM₂)     =
  ap (λ q → 〈 L ⹁ q 〉) (step-det M M₁ M₂ MM₁ MM₂)
step-det .(L ⇀₁)          .(L₁ ⇀₁)          .(L₂ ⇀₁)         (ξ-⇀₁ {L} {L′ = L₁} LL₁)           (ξ-⇀₁ {L′ = L₂} LL₂)       =
  ap _⇀₁ (step-det L L₁ L₂ LL₁ LL₂)
step-det .(〈 V₁ ⹁ V₂ 〉 ⇀₁)  .(L ⇀₁)           V₁               (ξ-⇀₁ {L′ = L} V→L)                (β-〈〉₁ {V₂} VV1 VV2)        =
  absurd (value-nf (V-〈〉 VV1 VV2) (L , V→L))
step-det .(L ⇀₂)          .(L₁ ⇀₂)          .(L₂ ⇀₂)         (ξ-⇀₂ {L} {L′ = L₁} LL₁)           (ξ-⇀₂ {L′ = L₂} LL₂)       =
  ap _⇀₂ (step-det L L₁ L₂ LL₁ LL₂)
step-det .(〈 V₁ ⹁ V₂ 〉 ⇀₂)  .(L ⇀₂)           V₂               (ξ-⇀₂ {L′ = L} V→L)                (β-〈〉₂ {V₁} {V₂} VV1 VV2)   =
  absurd (value-nf (V-〈〉 VV1 VV2) (L , V→L))
step-det .(〈 V₁ ⹁ V₂ 〉 ⇀₁)    V₁              .(L ⇀₁)          (β-〈〉₁ {V₁} {V₂} VV1 VV2)           (ξ-⇀₁ {L′ = L} V→L)        =
  absurd (value-nf (V-〈〉 VV1 VV2) (L , V→L))
step-det .(〈 V ⹁ _ 〉 ⇀₁)    V              .V                  (β-〈〉₁ _ _)                         (β-〈〉₁ {V₁ = V} _ _)        =
  refl
step-det .(〈 V₁ ⹁ V₂ 〉 ⇀₂)   V₂              .(L ⇀₂)           (β-〈〉₂ {V₁} {V₂} VV1 VV2)           (ξ-⇀₂ {L′ = L} V→L)        =
  absurd (value-nf (V-〈〉 VV1 VV2) (L , V→L))
step-det .(〈 _ ⹁ V 〉 ⇀₂)    V              .V                  (β-〈〉₂ {V₂ = V} _ _)                (β-〈〉₂ _ _)                 =
  refl

-- halting

halts : Term → 𝒰
halts t = Σ[ t′ ꞉ Term ] (t —↠ t′) × Value t′

value-halts : {v : Term} → Value v → halts v
value-halts {v} V = v , (v ∎ᵣ) , V

step-preserves-halting : {t t′ : Term}
                       → (t —→ t′)
                       → (halts t ↔ halts t′)
step-preserves-halting {t} {t′} S =
  (λ where
      (t″ , (.t″ ∎ᵣ) , V) →
        absurd (value-nf V (t′ , S))
      (t″ , (.t —→⟨ TM ⟩ STM) , V) →
        t″ , subst (_—↠ t″) (step-det _ _ _ TM S) STM , V)
  ,
  (λ where
      (t₀ , STM , V) → t₀ , (t —→⟨ S ⟩ STM) , V)

-- subsitution properties

vacuous-subst : ∀ t x
              → ¬ afi x t → ∀ t′ → t [ x := t′ ] ＝ t
vacuous-subst (` y)           x nafi t′ with y ≟ x
... | yes prf = absurd (nafi (subst (λ q → afi x (` q)) (sym prf) afi-var))
... | no ctra = refl
vacuous-subst (ƛ y ⇒ t)       x nafi t′ with y ≟ x
... | yes prf = refl
... | no ctra = ap (ƛ y ⇒_) (vacuous-subst t x (nafi ∘ afi-abs (ctra ∘ sym)) t′)
vacuous-subst (t₁ · t₂)       x nafi t′ =
  ap² _·_ (vacuous-subst t₁ x (nafi ∘ afi-appl) t′)
          (vacuous-subst t₂ x (nafi ∘ afi-appr) t′)
vacuous-subst 𝓉               x nafi t′ = refl
vacuous-subst 𝒻               x nafi t′ = refl
vacuous-subst (⁇ t ↑ t₁ ↓ t₂) x nafi t′ =
  ap³-simple ⁇_↑_↓_ (vacuous-subst t x (nafi ∘ afi-test0) t′)
                    (vacuous-subst t₁ x (nafi ∘ afi-test1) t′)
                    (vacuous-subst t₂ x (nafi ∘ afi-test2) t′)
vacuous-subst 〈 t₁ ⹁ t₂ 〉        x nafi t′ =
  ap² 〈_⹁_〉 (vacuous-subst t₁ x (nafi ∘ afi-pairl) t′)
          (vacuous-subst t₂ x (nafi ∘ afi-pairr) t′)
vacuous-subst (t ⇀₁)          x nafi t′ =
  ap _⇀₁ (vacuous-subst t x (nafi ∘ afi-fst) t′)
vacuous-subst (t ⇀₂)          x nafi t′ =
  ap _⇀₂ (vacuous-subst t x (nafi ∘ afi-snd) t′)

subst-closed : ∀ {t}
             → closed t → ∀ x t′ → t [ x := t′ ] ＝ t
subst-closed {t} c x t′ = vacuous-subst t x (c x) t′

subst-not-afi : ∀ t x v
              → closed v → ¬ afi x (t [ x := v ])
subst-not-afi (` y)           x v cv a with y ≟ x
...                                          | yes _   = cv x a
subst-not-afi (` y)          .y v cv afi-var | no ctra = ctra refl
subst-not-afi (ƛ y ⇒ t)       x v cv a with y ≟ x
subst-not-afi (ƛ y ⇒ t)       x v cv (afi-abs x≠y a) | yes prf = x≠y (sym prf)
subst-not-afi (ƛ y ⇒ t)       x v cv (afi-abs x≠y a) | no _    =
  subst-not-afi t x v cv a
subst-not-afi (t₁ · t₂)       x v cv (afi-appl a)  = subst-not-afi t₁ x v cv a
subst-not-afi (t₁ · t₂)       x v cv (afi-appr a)  = subst-not-afi t₂ x v cv a
subst-not-afi (⁇ t ↑ t₁ ↓ t₂) x v cv (afi-test0 a) = subst-not-afi t x v cv a
subst-not-afi (⁇ t ↑ t₁ ↓ t₂) x v cv (afi-test1 a) = subst-not-afi t₁ x v cv a
subst-not-afi (⁇ t ↑ t₁ ↓ t₂) x v cv (afi-test2 a) = subst-not-afi t₂ x v cv a
subst-not-afi 〈 t₁ ⹁ t₂ 〉       x v cv (afi-pairl a) = subst-not-afi t₁ x v cv a
subst-not-afi 〈 t₁ ⹁ t₂ 〉       x v cv (afi-pairr a) = subst-not-afi t₂ x v cv a
subst-not-afi (t ⇀₁)          x v cv (afi-fst a)   = subst-not-afi t x v cv a
subst-not-afi (t ⇀₂)          x v cv (afi-snd a)   = subst-not-afi t x v cv a

duplicate-subst : ∀ t x v w
                → closed v
                → t [ x := v ] [ x := w ] ＝ t [ x := v ]
duplicate-subst t x v w cv = vacuous-subst (t [ x := v ]) x (subst-not-afi t x v cv) w

-- noisy because of repeated matching (can't backpropagate a match after a same redex has surfaced)
swap-subst : ∀ t x y v w
           → x ≠ y → closed v → closed w
           → t [ x := v ] [ y := w ] ＝ t [ y := w ] [ x := v ]
swap-subst (` z)           x y v w x≠y cv cw with z ≟ x | z ≟ y
swap-subst (` z)           x y v w x≠y cv cw | yes zx | yes zy  = absurd (x≠y (sym zx ∙ zy))
swap-subst (` z)           x y v w x≠y cv cw | yes zx | no z≠y with z ≟ x -- AARGH
swap-subst (` z)           x y v w x≠y cv cw | yes zx | no z≠y | yes _ = subst-closed cv y w
swap-subst (` z)           x y v w x≠y cv cw | yes zx | no z≠y | no ctra = absurd (ctra zx)
swap-subst (` z)           x y v w x≠y cv cw | no z≠x | yes zy with z ≟ y -- AARGH
swap-subst (` z)           x y v w x≠y cv cw | no z≠x | yes zy | yes _ = sym (subst-closed cw x v)
swap-subst (` z)           x y v w x≠y cv cw | no z≠x | yes zy | no ctra = absurd (ctra zy)
swap-subst (` z)           x y v w x≠y cv cw | no z≠x | no z≠y with z ≟ x  -- AAAARGGH
swap-subst (` z)           x y v w x≠y cv cw | no z≠x | no z≠y | yes prf = absurd (z≠x prf)
swap-subst (` z)           x y v w x≠y cv cw | no z≠x | no z≠y | no _ with z ≟ y
swap-subst (` z)           x y v w x≠y cv cw | no z≠x | no z≠y | no _ | yes prf = absurd (z≠y prf)
swap-subst (` z)           x y v w x≠y cv cw | no z≠x | no z≠y | no _ | no _ = refl
swap-subst (ƛ z ⇒ t)       x y v w x≠y cv cw with z ≟ x | z ≟ y
swap-subst (ƛ z ⇒ t)       x y v w x≠y cv cw | yes zx | yes zy = absurd (x≠y (sym zx ∙ zy))
swap-subst (ƛ z ⇒ t)       x y v w x≠y cv cw | yes zx | no z≠y with z ≟ x -- AARGH
swap-subst (ƛ z ⇒ t)       x y v w x≠y cv cw | yes zx | no z≠y | yes _ with z ≟ y
swap-subst (ƛ z ⇒ t)       x y v w x≠y cv cw | yes zx | no z≠y | yes _ | yes prf = absurd (z≠y prf)
swap-subst (ƛ z ⇒ t)       x y v w x≠y cv cw | yes zx | no z≠y | yes _ | no _ = refl
swap-subst (ƛ z ⇒ t)       x y v w x≠y cv cw | yes zx | no z≠y | no ctra = absurd (ctra zx)
swap-subst (ƛ z ⇒ t)       x y v w x≠y cv cw | no z≠x | yes zy with z ≟ x -- AARGH
swap-subst (ƛ z ⇒ t)       x y v w x≠y cv cw | no z≠x | yes zy | yes prf = absurd (z≠x prf)
swap-subst (ƛ z ⇒ t)       x y v w x≠y cv cw | no z≠x | yes zy | no _ with z ≟ y
swap-subst (ƛ z ⇒ t)       x y v w x≠y cv cw | no z≠x | yes zy | no _ | yes _ = refl
swap-subst (ƛ z ⇒ t)       x y v w x≠y cv cw | no z≠x | yes zy | no _ | no ctra = absurd (ctra zy)
swap-subst (ƛ z ⇒ t)       x y v w x≠y cv cw | no z≠x | no z≠y with z ≟ x -- AARGH
swap-subst (ƛ z ⇒ t)       x y v w x≠y cv cw | no z≠x | no z≠y | yes prf = absurd (z≠x prf)
swap-subst (ƛ z ⇒ t)       x y v w x≠y cv cw | no z≠x | no z≠y | no _ with z ≟ y
swap-subst (ƛ z ⇒ t)       x y v w x≠y cv cw | no z≠x | no z≠y | no _ | yes prf = absurd (z≠y prf)
swap-subst (ƛ z ⇒ t)       x y v w x≠y cv cw | no z≠x | no z≠y | no _ | no _ =
  ap (ƛ z ⇒_) (swap-subst t x y v w x≠y cv cw)
swap-subst (t₁ · t₂)       x y v w x≠y cv cw =
  ap² (_·_) (swap-subst t₁ x y v w x≠y cv cw)
            (swap-subst t₂ x y v w x≠y cv cw)
swap-subst  𝓉              x y v w x≠y cv cw = refl
swap-subst  𝒻              x y v w x≠y cv cw = refl
swap-subst (⁇ t ↑ t₁ ↓ t₂) x y v w x≠y cv cw =
  ap³-simple ⁇_↑_↓_ (swap-subst t x y v w x≠y cv cw)
                    (swap-subst t₁ x y v w x≠y cv cw)
                    (swap-subst t₂ x y v w x≠y cv cw)
swap-subst 〈 t₁ ⹁ t₂ 〉       x y v w x≠y cv cw =
  ap² 〈_⹁_〉 (swap-subst t₁ x y v w x≠y cv cw)
          (swap-subst t₂ x y v w x≠y cv cw)
swap-subst (t ⇀₁)          x y v w x≠y cv cw =
  ap _⇀₁ (swap-subst t x y v w x≠y cv cw)
swap-subst (t ⇀₂)          x y v w x≠y cv cw =
  ap _⇀₂ (swap-subst t x y v w x≠y cv cw)
