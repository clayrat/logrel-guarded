module PCF.Ext.Term where

open import Prelude
open import Data.Empty
--open import Data.Unit
--open import Data.Dec
open import Data.Nat hiding (_·_)
open import Data.String
--open import Structures.IdentitySystem

--open import Interlude

-- names

Id : 𝒰
Id = String

infix  5 ƛ_⇒_
infix  5 ?⁰_↑_↓_
infixl 7 _·_
infix  9 Y_
infix  9 `_
infix  9 ＃_

-- terms

data Term : 𝒰 where
  `_      : Id → Term
  ƛ_⇒_    : Id → Term → Term
  _·_     : Term → Term → Term
  Y_      : Term → Term
  ＃_     : ℕ → Term
  𝓈       : Term → Term
  𝓅       : Term → Term
  ?⁰_↑_↓_ : Term → Term → Term → Term

{-
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
-}

-- Values
data Val : 𝒰 where
  v-＃ : ℕ → Val
  v-ƛ  : Id → Term → Val

data IsVal : Term → Val → 𝒰 where
  is-＃ : ∀ {n} → IsVal (＃ n) (v-＃ n)
  is-ƛ  : ∀ {x t} → IsVal (ƛ x ⇒ t) (v-ƛ x t)

{-
data Val : Term → 𝒰 where
  v-＃ : ∀ n
        ----------
       → Val (＃ n)

  v-ƛ  : ∀ x t
        ----------
       → Val (ƛ x ⇒ t)
-}
{-
-- appears free in

data afi : String → Term → 𝒰 where
  afi-`   : ∀ {x} → afi x (` x)
  afi-·-l : ∀ {x M N} → afi x M → afi x (M · N)
  afi-·-r : ∀ {x M N} → afi x N → afi x (M · N)
  afi-ƛ   : ∀ {x y N} → x ≠ y → afi x N → afi x (ƛ y ⇒ N)
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
-}
