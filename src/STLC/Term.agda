module STLC.Term where

open import Prelude
open import Data.Empty
open import Data.Unit
open import Data.Dec
open import Data.String
open import Structures.IdentitySystem
open import Interlude

-- names

Id : 𝒰
Id = String

infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  2 _—↠_
infix  3 _∎ᵣ
infix  4 _—→_
infix  5 ƛ_⇒_
infixl 7 _·_
infix  9 `_
infix  9 _[_:=_]

-- terms

data Term : 𝒰 where
  𝓉𝓉    : Term
  `_    : Id → Term
  ƛ_⇒_ : Id → Term → Term
  _·_   : Term → Term → Term

-- terms form a set

module Term-path-code where

  Code : Term → Term → 𝒰
  Code  𝓉𝓉        𝓉𝓉       = ⊤
  Code (` x)     (` y)     = x ＝ y
  Code (ƛ x ⇒ M) (ƛ y ⇒ N) = (x ＝ y) × Code M N
  Code (L · M)   (P · Q)   = Code L P × Code M Q
  Code  _         _        = ⊥

  code-refl : ∀ L → Code L L
  code-refl  𝓉𝓉       = tt
  code-refl (` x)     = refl
  code-refl (ƛ x ⇒ N) = refl , (code-refl N)
  code-refl (L · M)   = code-refl L , code-refl M

  decode : ∀ {L M} → Code L M → L ＝ M
  decode {L = 𝓉𝓉} {M = 𝓉𝓉}    tt       = refl
  decode {` x}     {` y}      c        = ap `_ c
  decode {ƛ x ⇒ L} {ƛ y ⇒ M} (xy , c)  = ap² ƛ_⇒_ xy (decode c)
  decode {L₁ · M₁} {L₂ · M₂} (cl , cm) = ap² _·_ (decode cl) (decode cm)

  code-is-prop : ∀ L M → is-prop (Code L M)
  code-is-prop 𝓉𝓉         𝓉𝓉       = hlevel!
  code-is-prop 𝓉𝓉        (` y)     = hlevel!
  code-is-prop 𝓉𝓉        (ƛ y ⇒ M) = hlevel!
  code-is-prop 𝓉𝓉        (L₂ · M₂) = hlevel!
  code-is-prop (` x)      𝓉𝓉       = hlevel!
  code-is-prop (` x)     (` y)     = hlevel!
  code-is-prop (` x)     (ƛ y ⇒ M) = hlevel!
  code-is-prop (` x)     (L₂ · M₂) = hlevel!
  code-is-prop (ƛ x ⇒ L)  𝓉𝓉       = hlevel!
  code-is-prop (ƛ x ⇒ L) (` y)     = hlevel!
  code-is-prop (ƛ x ⇒ L) (ƛ y ⇒ M) =
    -- hlevel! fails
    ×-is-of-hlevel 1 (path-is-of-hlevel′ 1 (hedberg-helper 0 string-is-discrete) x y) (code-is-prop L M)
  code-is-prop (ƛ x ⇒ L) (L₂ · M₂) = hlevel!
  code-is-prop (L₁ · M₁)  𝓉𝓉       = hlevel!
  code-is-prop (L₁ · M₁) (` y)     = hlevel!
  code-is-prop (L₁ · M₁) (ƛ y ⇒ M) = hlevel!
  code-is-prop (L₁ · M₁) (L₂ · M₂) = ×-is-of-hlevel 1 (code-is-prop L₁ L₂) (code-is-prop M₁ M₂)

  Term-identity-system : is-identity-system Code code-refl
  Term-identity-system = set-identity-system code-is-prop decode

Term-is-set : is-set Term
Term-is-set = identity-system→is-of-hlevel 1
                Term-path-code.Term-identity-system
                Term-path-code.code-is-prop

-- substitution

_[_:=_] : Term → Id → Term → Term
𝓉𝓉 [ y := V ]      = 𝓉𝓉
(` x) [ y := V ] with x ≟ y
... | yes _        = V
... | no  _        = ` x
(ƛ x ⇒ N) [ y := V ] with x ≟ y
... | yes _        = ƛ x ⇒ N
... | no  _        = ƛ x ⇒ N [ y := V ]
(L · M) [ y := V ] = L [ y := V ] · M [ y := V ]

-- values

data Value : Term → 𝒰 where
  V-𝓉𝓉 : Value 𝓉𝓉
  V-ƛ : ∀ {x N} → Value (ƛ x ⇒ N)

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

-- normal form

nf : Term → 𝒰
nf = normal-form _—→_

nf-is-prop : ∀ {t} → is-prop (nf t)
nf-is-prop = ¬-is-prop

value-nf : ∀ {t} → Value t → nf t
value-nf {.(ƛ x ⇒ N)} (V-ƛ {x} {N}) (M , ())

-- context invariance

-- appears free in
data afi : String → Term → 𝒰 where
  afi-var  : ∀ {x} → afi x (` x)
  afi-appl : ∀ {x M N} → afi x M → afi x (M · N)
  afi-appr : ∀ {x M N} → afi x N → afi x (M · N)
  afi-abs  : ∀ {x y N} → x ≠ y → afi x N → afi x (ƛ y ⇒ N)

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
vacuous-subst 𝓉𝓉        x nafi t′ = refl
vacuous-subst (` y)     x nafi t′ with y ≟ x
... | yes prf = absurd (nafi (subst (λ q → afi x (` q)) (sym prf) afi-var))
... | no ctra = refl
vacuous-subst (ƛ y ⇒ t) x nafi t′ with y ≟ x
... | yes prf = refl
... | no ctra = ap (ƛ y ⇒_) (vacuous-subst t x (nafi ∘ afi-abs (ctra ∘ sym)) t′)
vacuous-subst (t₁ · t₂) x nafi t′ =
  ap² _·_ (vacuous-subst t₁ x (nafi ∘ afi-appl) t′)
          (vacuous-subst t₂ x (nafi ∘ afi-appr) t′)

subst-closed : ∀ {t}
             → closed t → ∀ x t′ → t [ x := t′ ] ＝ t
subst-closed {t} c x t′ = vacuous-subst t x (c x) t′

subst-not-afi : ∀ t x v
              → closed v → ¬ afi x (t [ x := v ])
subst-not-afi (` y)      x v cv a with y ≟ x
...                                     | yes _   = cv x a
subst-not-afi (` y)     .y v cv afi-var | no ctra = ctra refl
subst-not-afi (ƛ y ⇒ t)  x v cv a with y ≟ x
subst-not-afi (ƛ y ⇒ t)  x v cv (afi-abs x≠y a) | yes prf = x≠y (sym prf)
subst-not-afi (ƛ y ⇒ t)  x v cv (afi-abs x≠y a) | no _    =
  subst-not-afi t x v cv a
subst-not-afi (t₁ · t₂)  x v cv (afi-appl a) = subst-not-afi t₁ x v cv a
subst-not-afi (t₁ · t₂)  x v cv (afi-appr a) = subst-not-afi t₂ x v cv a
duplicate-subst : ∀ t x v w
                → closed v
                → t [ x := v ] [ x := w ] ＝ t [ x := v ]
duplicate-subst t x v w cv = vacuous-subst (t [ x := v ]) x (subst-not-afi t x v cv) w

-- noisy because of repeated matching (can't backpropagate a match after a same redex has surfaced)
swap-subst : ∀ t x y v w
           → x ≠ y → closed v → closed w
           → t [ x := v ] [ y := w ] ＝ t [ y := w ] [ x := v ]
swap-subst 𝓉𝓉        x y v w x≠y cv cw = refl
swap-subst (` z)     x y v w x≠y cv cw with z ≟ x | z ≟ y
swap-subst (` z)     x y v w x≠y cv cw | yes zx | yes zy  = absurd (x≠y (sym zx ∙ zy))
swap-subst (` z)     x y v w x≠y cv cw | yes zx | no z≠y with z ≟ x -- AARGH
swap-subst (` z)     x y v w x≠y cv cw | yes zx | no z≠y | yes _ = subst-closed cv y w
swap-subst (` z)     x y v w x≠y cv cw | yes zx | no z≠y | no ctra = absurd (ctra zx)
swap-subst (` z)     x y v w x≠y cv cw | no z≠x | yes zy with z ≟ y -- AARGH
swap-subst (` z)     x y v w x≠y cv cw | no z≠x | yes zy | yes _ = sym (subst-closed cw x v)
swap-subst (` z)     x y v w x≠y cv cw | no z≠x | yes zy | no ctra = absurd (ctra zy)
swap-subst (` z)     x y v w x≠y cv cw | no z≠x | no z≠y with z ≟ x  -- AAAARGGH
swap-subst (` z)     x y v w x≠y cv cw | no z≠x | no z≠y | yes prf = absurd (z≠x prf)
swap-subst (` z)     x y v w x≠y cv cw | no z≠x | no z≠y | no _ with z ≟ y
swap-subst (` z)     x y v w x≠y cv cw | no z≠x | no z≠y | no _ | yes prf = absurd (z≠y prf)
swap-subst (` z)     x y v w x≠y cv cw | no z≠x | no z≠y | no _ | no _ = refl
swap-subst (ƛ z ⇒ t) x y v w x≠y cv cw with z ≟ x | z ≟ y
swap-subst (ƛ z ⇒ t) x y v w x≠y cv cw | yes zx | yes zy = absurd (x≠y (sym zx ∙ zy))
swap-subst (ƛ z ⇒ t) x y v w x≠y cv cw | yes zx | no z≠y with z ≟ x -- AARGH
swap-subst (ƛ z ⇒ t) x y v w x≠y cv cw | yes zx | no z≠y | yes _ with z ≟ y
swap-subst (ƛ z ⇒ t) x y v w x≠y cv cw | yes zx | no z≠y | yes _ | yes prf = absurd (z≠y prf)
swap-subst (ƛ z ⇒ t) x y v w x≠y cv cw | yes zx | no z≠y | yes _ | no _ = refl
swap-subst (ƛ z ⇒ t) x y v w x≠y cv cw | yes zx | no z≠y | no ctra = absurd (ctra zx)
swap-subst (ƛ z ⇒ t) x y v w x≠y cv cw | no z≠x | yes zy with z ≟ x -- AARGH
swap-subst (ƛ z ⇒ t) x y v w x≠y cv cw | no z≠x | yes zy | yes prf = absurd (z≠x prf)
swap-subst (ƛ z ⇒ t) x y v w x≠y cv cw | no z≠x | yes zy | no _ with z ≟ y
swap-subst (ƛ z ⇒ t) x y v w x≠y cv cw | no z≠x | yes zy | no _ | yes _ = refl
swap-subst (ƛ z ⇒ t) x y v w x≠y cv cw | no z≠x | yes zy | no _ | no ctra = absurd (ctra zy)
swap-subst (ƛ z ⇒ t) x y v w x≠y cv cw | no z≠x | no z≠y with z ≟ x -- AARGH
swap-subst (ƛ z ⇒ t) x y v w x≠y cv cw | no z≠x | no z≠y | yes prf = absurd (z≠x prf)
swap-subst (ƛ z ⇒ t) x y v w x≠y cv cw | no z≠x | no z≠y | no _ with z ≟ y
swap-subst (ƛ z ⇒ t) x y v w x≠y cv cw | no z≠x | no z≠y | no _ | yes prf = absurd (z≠y prf)
swap-subst (ƛ z ⇒ t) x y v w x≠y cv cw | no z≠x | no z≠y | no _ | no _ =
  ap (ƛ z ⇒_) (swap-subst t x y v w x≠y cv cw)
swap-subst (t₁ · t₂) x y v w x≠y cv cw =
  ap² (_·_) (swap-subst t₁ x y v w x≠y cv cw)
            (swap-subst t₂ x y v w x≠y cv cw)
