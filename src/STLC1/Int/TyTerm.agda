module STLC1.Int.TyTerm where

open import Prelude
open import Data.Empty
open import Data.Unit
open import Data.Dec
open import Data.List hiding (Code ; code-refl ; decode)
open import Structures.IdentitySystem hiding (J)

open import STLC.Ty

infix  4  _∋_
infix  4  _⊢_
infixl 5 _﹐_
infix  5 ƛ_
infixl 7 _·_
infix  9 `_

-- contexts

data Ctx : 𝒰 where
  ∅   : Ctx
  _﹐_ : Ctx → Ty → Ctx

Ctx-≅ : Ctx ≅ List Ty
Ctx-≅ = ff , iso gg ri li
  where
  ff : Ctx → List Ty
  ff ∅       = []
  ff (Γ ﹐ T) = T ∷ ff Γ
  gg : List Ty → Ctx
  gg []      = ∅
  gg (T ∷ l) = gg l ﹐ T
  ri : gg is-right-inverse-of ff
  ri []            = refl
  ri (T ∷ l) = ap (T ∷_) (ri l)
  li : gg is-left-inverse-of ff
  li ∅          = refl
  li (Γ ﹐ T) = ap (_﹐ T) (li Γ)

Ctx-is-discrete : is-discrete Ctx
Ctx-is-discrete = is-discrete-embedding (equiv→embedding (iso→equiv Ctx-≅)) (list-is-discrete Ty-is-discrete)

instance
  decomp-discrete-Ctx : goal-decomposition (quote is-discrete) Ctx
  decomp-discrete-Ctx = decomp (quote Ctx-is-discrete) []

-- TODO these should be derivable via Ctx-≅
module Ctx-path-code where

  Code : Ctx → Ctx → 𝒰
  Code ∅       ∅       = ⊤
  Code ∅       (_ ﹐ _) = ⊥
  Code (_ ﹐ _) ∅       = ⊥
  Code (Γ ﹐ T) (Δ ﹐ S) = (T ＝ S) × Code Γ Δ

  code-refl : (Γ : Ctx) → Code Γ Γ
  code-refl ∅       = tt
  code-refl (Γ ﹐ _) = refl , code-refl Γ

  decode : ∀ {Γ Δ} → Code Γ Δ → Γ ＝ Δ
  decode {Γ = ∅}     {Δ = ∅}      _      = refl
  decode {Γ = Γ ﹐ T} {Δ = Δ ﹐ S} (p , c) = ap² _﹐_ (decode c) p

  encode : ∀ {Γ Δ} → Γ ＝ Δ → Code Γ Δ
  encode {Γ} e = subst (Code Γ) e (code-refl Γ)

∅≠, : ∀ {Γ T} → ∅ ≠ Γ ﹐ T
∅≠, = Ctx-path-code.encode

,-inj : ∀ {Γ Δ T S} → Γ ﹐ T ＝ Δ ﹐ S → (Γ ＝ Δ) × (T ＝ S)
,-inj e = let c1 , c2 = Ctx-path-code.encode e in
          Ctx-path-code.decode c2 , c1

Ctx-ne-ext : ∀ {Γ T} → Γ ≠ Γ ﹐ T
Ctx-ne-ext {(∅)}   e = ∅≠, e
Ctx-ne-ext {Γ ﹐ S} e = Ctx-ne-ext $ ,-inj e .fst

Ctx-is-set : is-set Ctx
Ctx-is-set = iso→is-of-hlevel 2 Ctx-≅ (list-is-of-hlevel 0 Ty-is-set)

-- de Brujin indices

data _∋_ : Ctx → Ty → 𝒰 where

  here : ∀ {Γ A}
      ------------------
       → Γ ﹐ A ∋ A

  there : ∀ {Γ A B}
        → Γ ∋ A
          ------------------
        → Γ ﹐ B ∋ A

∅-empty : ∀ {A} → ¬ (∅ ∋ A)
∅-empty ()

-- typed terms

data _⊢_ : Ctx → Ty → 𝒰 where

  -- unit
  𝓉𝓉 : ∀ {Γ}
      ----------
    → Γ ⊢ 𝟙

  -- Axiom
  `_ : ∀ {Γ A}
    → Γ ∋ A
      -----------
    → Γ ⊢ A

  -- ⇒-I
  ƛ_ : ∀ {Γ A B}
    → Γ ﹐ A ⊢ B
      -------------------
    → Γ ⊢ A ⇒ B

  -- ⇒-E
  _·_ : ∀ {Γ A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
      -------------
    → Γ ⊢ B

module Tm-path-code where

  Code : ∀ {Γ T} → Γ ⊢ T → Γ ⊢ T → 𝒰
  Code          𝓉𝓉                   𝓉𝓉                  = ⊤
  Code          𝓉𝓉                  (` x₂)               = ⊥
  Code          𝓉𝓉                  (r₂ · s₂)            = ⊥
  Code         (` x₁)                𝓉𝓉                  = ⊥
  Code         (` x₁)               (` x₂)               = x₁ ＝ x₂
  Code         (` x₁)               (ƛ t₂)               = ⊥
  Code         (` x₁)               (r₂ · s₂)            = ⊥
  Code         (ƛ t₁)               (` x₂)               = ⊥
  Code         (ƛ t₁)               (ƛ t₂)               = Code t₁ t₂
  Code         (ƛ t₁)               (r₂ · s₂)            = ⊥
  Code         (r₁ · s₁)             𝓉𝓉                  = ⊥
  Code         (r₁ · s₁)            (` x₂)               = ⊥
  Code         (r₁ · s₁)            (ƛ t₂)               = ⊥
  Code {Γ} {T} (_·_ {A = A₁} r₁ s₁) (_·_ {A = A₂} r₂ s₂) =
    Σ[ eA ꞉ (A₁ ＝ A₂) ] (  Code r₁ (subst (λ q → Γ ⊢ q ⇒ T) (sym eA) r₂)
                         × Code s₁ (subst (Γ ⊢_) (sym eA) s₂))

  code-refl : ∀ {Γ T} → (t : Γ ⊢ T) → Code t t
  code-refl  𝓉𝓉                   = tt
  code-refl (` x)                 = refl
  code-refl (ƛ t)                 = code-refl t
  code-refl {Γ} {T} (_·_ {A} r s) =
    refl , subst (Code r) (sym (subst-refl {B = λ q → Γ ⊢ q ⇒ T} r)) (code-refl r)
         , subst (Code s) (sym (subst-refl {B = Γ ⊢_}            s)) (code-refl s)

  decode : ∀ {Γ T} {t₁ t₂ : Γ ⊢ T} → Code t₁ t₂ → t₁ ＝ t₂
  decode         {t₁ = 𝓉𝓉}            {(𝓉𝓉)}                c             = refl
  decode         {t₁ = 𝓉𝓉}            {` x₂}                c             = absurd c
  decode         {t₁ = 𝓉𝓉}            {r₂ · s₂}             c             = absurd c
  decode         {t₁ = ` x₁}          {(𝓉𝓉)}                c             = absurd c
  decode         {t₁ = ` x₁}          {` x₂}                c             = ap `_ c
  decode         {t₁ = ` x₁}          {ƛ t₂}                c             = absurd c
  decode         {t₁ = ` x₁}          {r₂ · s₂}             c             = absurd c
  decode         {t₁ = ƛ t₁}          {` x}                 c             = absurd c
  decode         {t₁ = ƛ t₁}          {ƛ t₂}                c             = ap ƛ_ (decode c)
  decode         {t₁ = ƛ t₁}          {r₂ · s₂}             c             = absurd c
  decode         {t₁ = r₁ · s₁}       {(𝓉𝓉)}                c             = absurd c
  decode         {t₁ = r₁ · s₁}       {` x₂}                c             = absurd c
  decode         {t₁ = r₁ · s₁}       {ƛ t₂}                c             = absurd c
  decode {Γ} {T} {_·_ {A = A₁} r₁ s₁} {_·_ {A = A₂} r₂ s₂} (eA , cr , cs) =
    J (λ A eA′ → (r : Γ ⊢ A ⇒ T)
               → (s : Γ ⊢ A)
               → Code r (subst (λ q → Γ ⊢ q ⇒ T) eA′ r₂)
               → Code s (subst (_⊢_ Γ) eA′ s₂)
               → r · s ＝ r₂ · s₂)
      (λ r s cr′ cs′ → ap² _·_
                          (decode (subst (Code r) (subst-refl {B = λ q → Γ ⊢ q ⇒ T} r₂) cr′))
                          (decode (subst (Code s) (subst-refl {B = Γ ⊢_} s₂) cs′)))
      (sym eA)
      r₁ s₁ cr cs

  encode : ∀ {Γ T} {t₁ t₂ : Γ ⊢ T} → t₁ ＝ t₂ → Code t₁ t₂
  encode {Γ} {T} {t₁} {t₂} e = subst (Code t₁) e (code-refl t₁)

𝓉𝓉≠` : ∀ {Γ x} → 𝓉𝓉 {Γ} ≠ ` x
𝓉𝓉≠` = Tm-path-code.encode

𝓉𝓉≠· : ∀ {Γ T r s} → 𝓉𝓉 {Γ} ≠ _·_ {A = T} r s
𝓉𝓉≠· = Tm-path-code.encode
