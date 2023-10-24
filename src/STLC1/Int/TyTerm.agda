module STLC1.Int.TyTerm where

open import Prelude
open import Data.Empty
open import Data.Unit
open import Data.Dec
--open import Data.Sum
open import Data.List
open import Structures.IdentitySystem hiding (J)

infix  4  _∋_
infix  4  _⊢_
infixl 5 _﹐_
infixr 7 _⇒_
infix  5 ƛ_
infixl 7 _·_
infix  9 `_

-- types

data Ty : 𝒰 where
  𝟙   : Ty
  _⇒_ : Ty → Ty → Ty

module Ty-path-code where

  Code : Ty → Ty → 𝒰
  Code  𝟙         𝟙        = ⊤
  Code  𝟙        (_ ⇒ _)   = ⊥
  Code (_ ⇒ _)    𝟙        = ⊥
  Code (S₁ ⇒ T₁) (S₂ ⇒ T₂) = Code S₁ S₂ × Code T₁ T₂

  code-refl : (t : Ty) → Code t t
  code-refl  𝟙      = tt
  code-refl (S ⇒ T) = code-refl S , code-refl T

  encode : ∀ {t₁ t₂} → t₁ ＝ t₂ → Code t₁ t₂
  encode {t₁} e = subst (Code t₁) e (code-refl t₁)

  decode : ∀ {t₁ t₂} → Code t₁ t₂ → t₁ ＝ t₂
  decode {t₁ = 𝟙}  {t₂ = 𝟙}   _        = refl
  decode {S₁ ⇒ T₁} {S₂ ⇒ T₂} (eS , eT) = ap² _⇒_ (decode eS) (decode eT)

  code-prop : ∀ t₁ t₂ → is-prop (Code t₁ t₂)
  code-prop  𝟙         𝟙        = hlevel!
  code-prop  𝟙        (_ ⇒ _)   = hlevel!
  code-prop (_ ⇒ _)    𝟙        = hlevel!
  code-prop (S₁ ⇒ T₁) (S₂ ⇒ T₂) = ×-is-of-hlevel 1 (code-prop S₁ S₂) (code-prop T₁ T₂)

  identity-system : is-identity-system Code code-refl
  identity-system = set-identity-system code-prop decode

𝟙≠⇒ : {S T : Ty} → 𝟙 ≠ S ⇒ T
𝟙≠⇒ = Ty-path-code.encode

⇒-inj : {S₁ T₁ S₂ T₂ : Ty} → S₁ ⇒ T₁ ＝ S₂ ⇒ T₂ → (S₁ ＝ S₂) × (T₁ ＝ T₂)
⇒-inj e = let c1 , c2 = Ty-path-code.encode e in
          Ty-path-code.decode c1 , Ty-path-code.decode c2

Ty-is-discrete : is-discrete Ty
Ty-is-discrete = is-discrete-η go
  where
  go : Dec on-paths-of Ty
  go  𝟙         𝟙        = yes refl
  go  𝟙        (S ⇒ T)   = no 𝟙≠⇒
  go (S ⇒ T)    𝟙        = no (𝟙≠⇒ ∘ sym)
  go (S₁ ⇒ T₁) (S₂ ⇒ T₂) with (go S₁ S₂ , go T₁ T₂)
  ... | yes prf₁ , yes prf₂ = yes (ap (_⇒ T₁) prf₁ ∙ ap (S₂ ⇒_) prf₂)
  ... | yes _    , no ctra₂ = no λ prf₂ → ctra₂ (⇒-inj prf₂ .snd)
  ... | no ctra₁ , _        = no λ prf₁ → ctra₁ (⇒-inj prf₁ .fst)

instance
  decomp-discrete-Ty : goal-decomposition (quote is-discrete) Ty
  decomp-discrete-Ty = decomp (quote Ty-is-discrete) []

Ty-is-set : is-set Ty
Ty-is-set = identity-system→is-of-hlevel 1 Ty-path-code.identity-system Ty-path-code.code-prop

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

{-
-- Context append
_◇_ : Ctx → Ctx → Ctx
Δ ◇ ∅       = Δ
Δ ◇ (Γ ﹐ S) = Δ ◇ Γ ﹐ S

-- Inject de Brujin index into larger context
inject-var : ∀ {Γ Δ T}
           → Γ ∋ T → Δ ◇ Γ ∋ T
inject-var  here     = here
inject-var (there x) = there (inject-var x)

-- Inject term into larger context (similar to weakening)
inject : ∀ {Γ Δ T}
       → Γ ⊢ T → Δ ◇ Γ ⊢ T
inject (` i)         = ` inject-var i
inject (ƛ t)         = ƛ inject t
inject (r · s)       = inject r · inject s
inject 𝓉             = 𝓉
inject 𝒻             = 𝒻
inject (⁇ r ↑ s ↓ t) = ⁇ inject r ↑ inject s ↓ inject t

-- If we have a variable in a injected context
-- we can determine where it came from
split : ∀ {Γ Δ T}
      → Γ ◇ Δ ∋ T → (Γ ∋ T) ⊎ (Δ ∋ T)
split {Δ = ∅}      i        = inl i
split {Δ = Δ ﹐ _}  here     = inr here
split {Δ = Δ ﹐ _} (there i) = [ inl , inr ∘ there ]ᵤ (split {Δ = Δ} i)
-}
