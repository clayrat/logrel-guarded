{-# OPTIONS --guarded #-}
module Later where

open import Agda.Primitive.Cubical using ( primHComp ; primComp )
open import Prelude
open import Foundations.Cubes
open import Prim

private
  variable
    ℓ ℓ′ ℓ″ : Level
    A : 𝒰 ℓ
    B : A → 𝒰 ℓ′

infixl 4 _⊛_
infixr -2 ▹-syntax

-- We postulate Tick as it is supposed to be an abstract sort.
postulate
  Tick : LockU

▹_ : 𝒰 ℓ → 𝒰 ℓ
▹_ A = (@tick α : Tick) -> A

▸_ : ▹ 𝒰 ℓ → 𝒰 ℓ
▸ A▹ = (@tick α : Tick) → A▹ α

▹-syntax : ▹ 𝒰 ℓ → 𝒰 ℓ
▹-syntax A▹ = (@tick α : Tick) → A▹ α

syntax ▹-syntax (λ α → e) = ▹[ α ] e

transport▹ : (A : I → ▹ 𝒰 ℓ) → ▸ A i0 → ▸ A i1
transport▹ A = transp (λ i → ▸ A i) i0

next : A → ▹ A
next x _ = x

▸-next : ▸ (next A) ＝ ▹ A
▸-next = refl

_⊛_ : ▹ ((a : A) → B a)
     → (a : ▹ A) → ▹[ α ] B (a α)
(f ⊛ x) α = f α (x α)

▹map : ((a : A) → B a)
     → (a : ▹ A) → ▹[ α ] B (a α)
▹map f x α = f (x α)

-- TODO simplified
▹map² : {B C : 𝒰 ℓ} → (f : A → B → C) → ▹ A → ▹ B → ▹ C
▹map² f x y α = f (x α) (y α)

▹-ext : {x▹ y▹ : ▹ A} → (▹[ α ] (x▹ α ＝ y▹ α)) → x▹ ＝ y▹
▹-ext e i α = e α i

▹-ap : {x▹ y▹ : ▹ A} → x▹ ＝ y▹ → ▹[ α ] (x▹ α ＝ y▹ α)
▹-ap e α i = e i α

▹-extP : {P : I → ▹ 𝒰 ℓ} {x▹ : ▹[ α ] P i0 α} {y▹ : ▹[ α ] P i1 α}
     → (▹[ α ] ＜ (x▹ α) ／ (λ i → P i α) ＼ (y▹ α) ＞)
     → ＜ x▹ ／ (λ i → ▹[ α ] P i α) ＼ y▹ ＞
▹-extP e i α = e α i

▹-apP : {P : I → ▹ 𝒰 ℓ} {x▹ : ▹[ α ] P i0 α} {y▹ : ▹[ α ] P i1 α}
     → ＜ x▹ ／ (λ i → ▹[ α ] P i α) ＼ y▹ ＞
     → (▹[ α ] ＜ (x▹ α) ／ (λ i → P i α) ＼ (y▹ α) ＞)
▹-apP e α i = e i α

postulate
  tick-irr : (x : ▹ A) → ▹[ α ] ▹[ β ] x α ＝ x β

-- These will compute only on diamond ticks.
  dfix : (▹ A → A) → ▹ A
  pfix : (f : ▹ A → A) → dfix f ＝ next (f (dfix f))

pfix-ext : (f : ▹ A → A) → ▹[ α ] (dfix f α ＝ f (dfix f))
pfix-ext f α i = pfix f i α

fix : (▹ A → A) → A
fix f = f (dfix f)

fix-path : (f : ▹ A → A) → fix f ＝ f (next (fix f))
fix-path f i = f (pfix f i)

-- A form of Banach's fixed point theorem
dfix-unique : ∀ {f▹ : ▹ A → A} {x : ▹ A}
            → x ＝ next (f▹ x)
            → x ＝ dfix f▹
dfix-unique {f▹} e = fix λ ih▹ → e ∙ ▹-ext (▹map (ap f▹) ih▹) ∙ sym (pfix f▹)

fix-unique : ∀ {f▹ : ▹ A → A} {x : A}
           → x ＝ f▹ (next x)
           → x ＝ fix f▹
fix-unique {f▹} e = fix λ ih▹ → e ∙ ap f▹ (▹-ext ih▹) ∙ sym (fix-path f▹)

▹Alg : 𝒰 ℓ → 𝒰 ℓ
▹Alg A = ▹ A → A

-- hlevel interaction

▹is-contr : {A : ▹ 𝒰 ℓ}
  → ▹[ α ] is-contr (A α)
  → is-contr (▹[ α ] (A α))
▹is-contr p = is-contr-η $ (λ α → is-contr-β (p α) .fst) , λ y i α → is-contr-β (p α) .snd (y α) i

▹is-prop : {A : ▹ 𝒰 ℓ}
  → ▹[ α ] is-prop (A α)
  → is-prop (▹[ α ] (A α))
▹is-prop p = is-prop-η λ x y i α → is-prop-β (p α) (x α) (y α) i

▹is-of-hlevel : {A : ▹ 𝒰 ℓ} {n : HLevel}
  → ▹[ α ] is-of-hlevel n (A α)
  → is-of-hlevel n (▹[ α ] (A α))
▹is-of-hlevel {n = zero}          = ▹is-contr
▹is-of-hlevel {n = suc zero}      = ▹is-prop
▹is-of-hlevel {n = suc (suc n)} a =
  is-of-hlevel-η n λ p q →
    retract→is-of-hlevel (suc n) ▹-extP ▹-apP (λ _ → refl)
    (▹is-of-hlevel λ α → is-of-hlevel-β n (a α) (p α) (q α))
