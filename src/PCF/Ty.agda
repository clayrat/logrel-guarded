module PCF.Ty where

open import Prelude
open import Data.Empty
open import Data.Unit

infixr 7 _⇒_

-- types

data Ty : 𝒰 where
  _⇒_ : Ty → Ty → Ty
  𝓝  : Ty

module Ty-path-code where

  Code : Ty → Ty → 𝒰
  Code  𝓝        𝓝       = ⊤
  Code  𝓝       (_ ⇒ _)   = ⊥
  Code (_ ⇒ _)    𝓝       = ⊥
  Code (S₁ ⇒ T₁) (S₂ ⇒ T₂) = Code S₁ S₂ × Code T₁ T₂

  code-refl : (t : Ty) → Code t t
  code-refl  𝓝     = tt
  code-refl (S ⇒ T) = code-refl S , code-refl T

  encode : ∀ {t₁ t₂} → t₁ ＝ t₂ → Code t₁ t₂
  encode {t₁} e = subst (Code t₁) e (code-refl t₁)

  decode : ∀ {t₁ t₂} → Code t₁ t₂ → t₁ ＝ t₂
  decode {t₁ = 𝓝} {t₂ = 𝓝}  _        = refl
  decode {S₁ ⇒ T₁} {S₂ ⇒ T₂} (eS , eT) = ap² _⇒_ (decode eS) (decode eT)

  code-prop : ∀ t₁ t₂ → is-prop (Code t₁ t₂)
  code-prop  𝓝        𝓝       = hlevel!
  code-prop  𝓝       (_ ⇒ _)   = hlevel!
  code-prop (_ ⇒ _)    𝓝       = hlevel!
  code-prop (S₁ ⇒ T₁) (S₂ ⇒ T₂) = ×-is-of-hlevel 1 (code-prop S₁ S₂) (code-prop T₁ T₂)

  identity-system : is-identity-system Code code-refl
  identity-system = set-identity-system code-prop decode

Ty-is-set : is-set Ty
Ty-is-set = identity-system→is-of-hlevel 1 Ty-path-code.identity-system Ty-path-code.code-prop

⇒-inj : {S₁ T₁ S₂ T₂ : Ty} → S₁ ⇒ T₁ ＝ S₂ ⇒ T₂ → (S₁ ＝ S₂) × (T₁ ＝ T₂)
⇒-inj e = let c1 , c2 = Ty-path-code.encode e in
          Ty-path-code.decode c1 , Ty-path-code.decode c2
