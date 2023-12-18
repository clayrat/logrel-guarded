module STLC.Ty where

open import Prelude
open import Data.Empty
open import Data.Unit
open import Data.Dec
open import Data.List hiding (Code ; code-refl ; decode ; identity-system)
open import Structures.IdentitySystem hiding (J)

infixr 7 _⇒_

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
