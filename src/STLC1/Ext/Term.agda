module STLC1.Ext.Term where

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

infix  5 ƛ_⇒_
infixl 7 _·_
infix  9 `_

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
