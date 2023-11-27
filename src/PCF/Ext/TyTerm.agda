module PCF.Ext.TyTerm where

open import Prelude
open import Data.Empty
open import Data.Unit
open import Data.Nat hiding (_·_; Code; code-refl; decode; identity-system; code-is-prop)
open import Data.String
open import Structures.IdentitySystem
open import Meta.Search.HLevel

open import Interlude
open import PCF.Ty

infix  5 ƛ_⦂_⇒_
infix  5 ?⁰_↑_↓_
infixl 7 _·_
infix  9 Y_
infix  9 `_
infix  9 ＃_

-- names

Id : 𝒰
Id = String

-- terms

data Term : 𝒰 where
  `_      : Id → Term
  ƛ_⦂_⇒_   : Id → Ty → Term → Term
  _·_     : Term → Term → Term
  Y_      : Term → Term
  ＃_     : ℕ → Term
  𝓈       : Term → Term
  𝓅       : Term → Term
  ?⁰_↑_↓_ : Term → Term → Term → Term

-- terms form a set

module Term-path-code where

  Code : Term → Term → 𝒰
  Code (` x)             (` y)             = x ＝ y
  Code (ƛ x ⦂ A ⇒ M)     (ƛ y ⦂ B ⇒ N)      = (x ＝ y) × (A ＝ B) × Code M N
  Code (L · M)           (P · Q)           = Code L P × Code M Q
  Code (Y M)             (Y N)             = Code M N
  Code (＃ m)            (＃ n)             = m ＝ n
  Code (𝓈 M)             (𝓈 N)             = Code M N
  Code (𝓅 M)             (𝓅 N)            = Code M N
  Code (?⁰ M₁ ↑ N₁ ↓ L₁) (?⁰ M₂ ↑ N₂ ↓ L₂) = Code M₁ M₂ × Code N₁ N₂ × Code L₁ L₂
  Code  _         _        = ⊥

  code-refl : ∀ L → Code L L
  code-refl (` x)          = refl
  code-refl (ƛ x ⦂ A ⇒ N)  = refl , refl , code-refl N
  code-refl (L · M)        = code-refl L , code-refl M
  code-refl (Y M)          = code-refl M
  code-refl (＃ m)         = refl
  code-refl (𝓈 M)          = code-refl M
  code-refl (𝓅 M)          = code-refl M
  code-refl (?⁰ M ↑ N ↓ L) = code-refl M , code-refl N , code-refl L

  decode : ∀ {L M} → Code L M → L ＝ M
  decode {` x}            {` y}              c              = ap `_ c
  decode {ƛ x ⦂ A ⇒ L}    {ƛ y ⦂ B ⇒ M}       (xy , ab , c)  = ap³-simple ƛ_⦂_⇒_ xy ab (decode c)
  decode {L₁ · M₁}        {L₂ · M₂}          (cl , cm)      = ap² _·_ (decode cl) (decode cm)
  decode {Y L}            {Y M}              c              = ap Y_ (decode c)
  decode {＃ m}            {＃ n}             c             = ap ＃_ c
  decode {𝓈 L}            {𝓈 M}               c             = ap 𝓈 (decode c)
  decode {𝓅 L}            {𝓅 M}              c             = ap 𝓅 (decode c)
  decode {?⁰ L₁ ↑ M₁ ↓ N₁} {?⁰ L₂ ↑ M₂ ↓ N₂} (cl , cm , cn) = ap³-simple ?⁰_↑_↓_ (decode cl) (decode cm) (decode cn)

  code-is-prop : ∀ L M → is-prop (Code L M)
  code-is-prop (` x) (` y) = hlevel!
  code-is-prop (` _) (ƛ _ ⦂ _ ⇒ _) = hlevel!
  code-is-prop (` _) (M · M₁) = hlevel!
  code-is-prop (` _) (Y M) = hlevel!
  code-is-prop (` _) (＃ x₁) = hlevel!
  code-is-prop (` _) (𝓈 M) = hlevel!
  code-is-prop (` _) (𝓅 M) = hlevel!
  code-is-prop (` _) (?⁰ M ↑ M₁ ↓ M₂) = hlevel!
  code-is-prop (ƛ _ ⦂ _ ⇒ _) (` x₁) = hlevel!
  code-is-prop (ƛ x ⦂ A ⇒ L) (ƛ y ⦂ B ⇒ M) =
    ×-is-of-hlevel 1
      (path-is-of-hlevel′ 1 (hedberg-helper 0 string-is-discrete) x y)
      (×-is-of-hlevel 1
        (path-is-of-hlevel′ 1 Ty-is-set A B)
        (code-is-prop L M))
  code-is-prop (ƛ _ ⦂ _ ⇒ _) (M · M₁) = hlevel!
  code-is-prop (ƛ _ ⦂ _ ⇒ _) (Y M) = hlevel!
  code-is-prop (ƛ _ ⦂ _ ⇒ _) (＃ x₁) = hlevel!
  code-is-prop (ƛ _ ⦂ _ ⇒ _) (𝓈 M) = hlevel!
  code-is-prop (ƛ _ ⦂ _ ⇒ _) (𝓅 M) = hlevel!
  code-is-prop (ƛ _ ⦂ _ ⇒ _) (?⁰ M ↑ M₁ ↓ M₂) = hlevel!
  code-is-prop (L · L₁) (` x) = hlevel!
  code-is-prop (L · L₁) (ƛ _ ⦂ _ ⇒ _) = hlevel!
  code-is-prop (L₁ · M₁) (L₂ · M₂) = ×-is-of-hlevel 1 (code-is-prop L₁ L₂) (code-is-prop M₁ M₂)
  code-is-prop (L · L₁) (Y M) = hlevel!
  code-is-prop (L · L₁) (＃ x) = hlevel!
  code-is-prop (L · L₁) (𝓈 M) = hlevel!
  code-is-prop (L · L₁) (𝓅 M) = hlevel!
  code-is-prop (L · L₁) (?⁰ M ↑ M₁ ↓ M₂) = hlevel!
  code-is-prop (Y L) (` x) = hlevel!
  code-is-prop (Y L) (ƛ _ ⦂ _ ⇒ _) = hlevel!
  code-is-prop (Y L) (M · M₁) = hlevel!
  code-is-prop (Y L) (Y M) = code-is-prop L M
  code-is-prop (Y L) (＃ x) = hlevel!
  code-is-prop (Y L) (𝓈 M) = hlevel!
  code-is-prop (Y L) (𝓅 M) = hlevel!
  code-is-prop (Y L) (?⁰ M ↑ M₁ ↓ M₂) = hlevel!
  code-is-prop (＃ x) (` x₁) = hlevel!
  code-is-prop (＃ x) (ƛ _ ⦂ _ ⇒ _) = hlevel!
  code-is-prop (＃ x) (M · M₁) = hlevel!
  code-is-prop (＃ x) (Y M) = hlevel!
  code-is-prop (＃ x) (＃ x₁) = hlevel!
  code-is-prop (＃ x) (𝓈 M) = hlevel!
  code-is-prop (＃ x) (𝓅 M) = hlevel!
  code-is-prop (＃ x) (?⁰ M ↑ M₁ ↓ M₂) = hlevel!
  code-is-prop (𝓈 L) (` x) = hlevel!
  code-is-prop (𝓈 L) (ƛ _ ⦂ _ ⇒ _) = hlevel!
  code-is-prop (𝓈 L) (M · M₁) = hlevel!
  code-is-prop (𝓈 L) (Y M) = hlevel!
  code-is-prop (𝓈 L) (＃ x) = hlevel!
  code-is-prop (𝓈 L) (𝓈 M) = code-is-prop L M
  code-is-prop (𝓈 L) (𝓅 M) = hlevel!
  code-is-prop (𝓈 L) (?⁰ M ↑ M₁ ↓ M₂) = hlevel!
  code-is-prop (𝓅 L) (` x) = hlevel!
  code-is-prop (𝓅 L) (ƛ _ ⦂ _ ⇒ _) = hlevel!
  code-is-prop (𝓅 L) (M · M₁) = hlevel!
  code-is-prop (𝓅 L) (Y M) = hlevel!
  code-is-prop (𝓅 L) (＃ x) = hlevel!
  code-is-prop (𝓅 L) (𝓈 M) = hlevel!
  code-is-prop (𝓅 L) (𝓅 M) = code-is-prop L M
  code-is-prop (𝓅 L) (?⁰ M ↑ M₁ ↓ M₂) = hlevel!
  code-is-prop (?⁰ L ↑ L₁ ↓ L₂) (` x) = hlevel!
  code-is-prop (?⁰ L ↑ L₁ ↓ L₂) (ƛ _ ⦂ _ ⇒ _) = hlevel!
  code-is-prop (?⁰ L ↑ L₁ ↓ L₂) (M · M₁) = hlevel!
  code-is-prop (?⁰ L ↑ L₁ ↓ L₂) (Y M) = hlevel!
  code-is-prop (?⁰ L ↑ L₁ ↓ L₂) (＃ x) = hlevel!
  code-is-prop (?⁰ L ↑ L₁ ↓ L₂) (𝓈 M) = hlevel!
  code-is-prop (?⁰ L ↑ L₁ ↓ L₂) (𝓅 M) = hlevel!
  code-is-prop (?⁰ L₁ ↑ M₁ ↓ N₁) (?⁰ L₂ ↑ M₂ ↓ N₂) =
    ×-is-of-hlevel 1 (code-is-prop L₁ L₂) (×-is-of-hlevel 1 (code-is-prop M₁ M₂) (code-is-prop N₁ N₂))

  Term-identity-system : is-identity-system Code code-refl
  Term-identity-system = set-identity-system code-is-prop decode

Term-is-set : is-set Term
Term-is-set = identity-system→is-of-hlevel 1
                Term-path-code.Term-identity-system
                Term-path-code.code-is-prop

Term-is-of-hlevel : (n : HLevel) → is-of-hlevel (2 + n) Term
Term-is-of-hlevel n = is-of-hlevel-+-left 2 n Term-is-set

instance
  decomp-hlevel-Term : goal-decomposition (quote is-of-hlevel) Term
  decomp-hlevel-Term = decomp (quote Term-is-of-hlevel) (`level-minus 2 ∷ [])

-- Values

data Val : 𝒰 where
  v-＃ : ℕ → Val
  v-ƛ  : Id → Ty → Term → Val

module Val-path-code where

  Code : Val → Val → 𝒰
  Code (v-＃ x) (v-＃ y) = x ＝ y
  Code (v-ƛ x A L) (v-ƛ y B M) = (x ＝ y) × (A ＝ B) × (L ＝ M)
  Code _ _ = ⊥

  code-refl : ∀ L → Code L L
  code-refl (v-＃ x) = refl
  code-refl (v-ƛ x T t) = refl , refl , refl

  decode : ∀ {L M} → Code L M → L ＝ M
  decode {v-＃ x} {v-＃ y}     c       = ap v-＃ c
  decode {v-ƛ x A L} {v-ƛ y B M} (cx , ct , cl) = ap³-simple v-ƛ cx ct cl

  encode : ∀ {L M} → L ＝ M → Code L M
  encode {L} {M} e = subst (Code L) e (code-refl L)

  code-is-prop : ∀ L M → is-prop (Code L M)
  code-is-prop (v-＃ x) (v-＃ y) = hlevel!
  code-is-prop (v-＃ _) (v-ƛ _ _ _) = hlevel!
  code-is-prop (v-ƛ _ _ _) (v-＃ _) = hlevel!
  code-is-prop (v-ƛ x A L) (v-ƛ y B M) =
    ×-is-of-hlevel 1 (path-is-of-hlevel′ 1 (hedberg-helper 0 string-is-discrete) x y) $
    ×-is-of-hlevel 1 (path-is-of-hlevel′ 1 Ty-is-set A B)
                     (path-is-of-hlevel′ 1 (Term-is-of-hlevel 0) L M)

  identity-system : is-identity-system Code code-refl
  identity-system = set-identity-system code-is-prop decode

Val-is-set : is-set Val
Val-is-set = identity-system→is-of-hlevel 1
                Val-path-code.identity-system
                Val-path-code.code-is-prop

v-＃≠v-ƛ : ∀ {n x A t} → v-＃ n ≠ v-ƛ x A t
v-＃≠v-ƛ = Val-path-code.encode

v-＃-inj : ∀ {m n} → v-＃ m ＝ v-＃ n → m ＝ n
v-＃-inj = Val-path-code.encode

v-ƛ-inj : ∀ {x y A B r s} → v-ƛ x A r ＝ v-ƛ y B s → (x ＝ y) × (A ＝ B) × (r ＝ s)
v-ƛ-inj = Val-path-code.encode

data IsVal : Term → Val → 𝒰 where
  is-＃ : ∀ {n} → IsVal (＃ n) (v-＃ n)
  is-ƛ  : ∀ {x A t} → IsVal (ƛ x ⦂ A ⇒ t) (v-ƛ x A t)

IsVal-unique : ∀ N M V
             → IsVal N V
             → IsVal M V
             → N ＝ M
IsVal-unique .(＃ _)        .(＃ _)        .(v-＃ _)    is-＃ is-＃ = refl
IsVal-unique .(ƛ _ ⦂ _ ⇒ _) .(ƛ _ ⦂ _ ⇒ _) .(v-ƛ _ _ _) is-ƛ  is-ƛ = refl

-- appears free in

data afi : String → Term → 𝒰 where
  afi-`   : ∀ {x} → afi x (` x)
  afi-·-l : ∀ {x M N} → afi x M → afi x (M · N)
  afi-·-r : ∀ {x M N} → afi x N → afi x (M · N)
  afi-ƛ   : ∀ {x y A N} → x ≠ y → afi x N → afi x (ƛ y ⦂ A ⇒ N)
  afi-Y   : ∀ {x M} → afi x M → afi x (Y M)
  -- booleans
  afi-?-b : ∀ {x L M N} → afi x L → afi x (?⁰ L ↑ M ↓ N)
  afi-?-t : ∀ {x L M N} → afi x M → afi x (?⁰ L ↑ M ↓ N)
  afi-?-f : ∀ {x L M N} → afi x N → afi x (?⁰ L ↑ M ↓ N)
  -- numbers
  afi-𝓈   : ∀ {x M} → afi x M → afi x (𝓈 M)
  afi-𝓅   : ∀ {x M} → afi x M → afi x (𝓅 M)

closed : Term → 𝒰
closed t = ∀ i → ¬ afi i t
