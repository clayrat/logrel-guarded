module STLC2P.Multi where

open import Prelude
open import Data.Empty
open import Data.Dec
open import Data.Maybe
open import Data.List
open import Data.List.Correspondences.Unary.All
open import Data.String

open import Interlude
open import STLC2P.Term
open import STLC2P.Ty

-- multisubstitution

Env : 𝒰
Env = List (String × Term)

msubst : Env → Term → Term
msubst []             t = t
msubst ((x , s) ∷ ss) t = msubst ss (t [ x := s ])

msubst-closed : ∀ {t}
              → closed t → ∀ ss → msubst ss t ＝ t
msubst-closed ct []             = refl
msubst-closed ct ((y , s) ∷ ss) =
  ap (msubst ss) (subst-closed ct y s) ∙ msubst-closed ct ss

closed-env : (@0 e : Env) → 𝒰
closed-env = All (closed ∘ snd)

subst-msubst : ∀ {env v}
             → closed v → closed-env env
             → ∀ x t
             → msubst env (t [ x := v ]) ＝ (msubst (drp x env) t) [ x := v ]
subst-msubst {env = []}        {v} cv []        x t = refl
subst-msubst {((y , p) ∷ env)} {v} cv (cp ∷ ce) x t with x ≟ y
... | yes prf = ap (msubst env) (ap (λ q → t [ x := v ] [ q := p ]) (sym prf)
                                 ∙ duplicate-subst t x v p cv)
              ∙ subst-msubst cv ce x t
... | no ctra = ap (msubst env) (swap-subst t x y v p ctra cv cp)
              ∙ subst-msubst cv ce x (t [ y := p ])

msubst-var : ∀ {ss}
           → closed-env ss
           → ∀ x
           → msubst ss (` x) ＝ extract (` x) (lup x ss)
msubst-var {ss = []}        []         x = refl
msubst-var {((y , t) ∷ ss)} (ct ∷ css) x with x ≟ y
... | yes prf = msubst-closed ct ss
... | no ctra = msubst-var css x

msubst-abs : ∀ ss x t
           → msubst ss (ƛ x ⇒ t) ＝ ƛ x ⇒ msubst (drp x ss) t
msubst-abs []             x t = refl
msubst-abs ((y , p) ∷ ss) x t with x ≟ y
... | yes prf = msubst-abs ss x t
... | no ctra = msubst-abs ss x (t [ y := p ])

msubst-app : ∀ ss t1 t2
           → msubst ss (t1 · t2) ＝ (msubst ss t1) · (msubst ss t2)
msubst-app []             t1 t2 = refl
msubst-app ((y , t) ∷ ss) t1 t2 = msubst-app ss (t1 [ y := t ]) (t2 [ y := t ])

msubst-true : ∀ ss → msubst ss 𝓉 ＝ 𝓉
msubst-true []       = refl
msubst-true (_ ∷ ss) = msubst-true ss

msubst-false : ∀ ss → msubst ss 𝒻 ＝ 𝒻
msubst-false []       = refl
msubst-false (_ ∷ ss) = msubst-false ss

msubst-if : ∀ ss b t f
          → msubst ss (⁇ b ↑ t ↓ f) ＝ ⁇ (msubst ss b) ↑ (msubst ss t) ↓ (msubst ss f)
msubst-if []       b t f = refl
msubst-if ((x , q) ∷ ss) b t f = msubst-if ss (b [ x := q ]) (t [ x := q ]) (f [ x := q ])

msubst-pair : ∀ ss t s
            → msubst ss 〈 t ⹁ s 〉 ＝ 〈 msubst ss t ⹁ msubst ss s 〉
msubst-pair []             t s = refl
msubst-pair ((x , q) ∷ ss) t s = msubst-pair ss (t [ x := q ]) (s [ x := q ])

msubst-fst : ∀ ss t
           → msubst ss (t ⇀₁) ＝ (msubst ss t ⇀₁)
msubst-fst []             t = refl
msubst-fst ((x , q) ∷ ss) t = msubst-fst ss (t [ x := q ])

msubst-snd : ∀ ss t
           → msubst ss (t ⇀₂) ＝ (msubst ss t ⇀₂)
msubst-snd []             t = refl
msubst-snd ((x , q) ∷ ss) t = msubst-snd ss (t [ x := q ])

-- multiextension
-- TODO essentially just context concatenation

Tass : 𝒰
Tass = List (String × Ty)

mupdate : Tass → Context → Context
mupdate []              Γ = Γ
mupdate ((x , v) ∷ xts) Γ = (mupdate xts Γ) , x ⦂ v

mupdate-lookup : ∀ {c x T}
               → mupdate c ∅ ∋ x ⦂ T
               → lup x c ＝ just T
mupdate-lookup {((y , S) ∷ c)} {.y} {.S}  here         with y ≟ y  -- wtf
... | yes _   = refl
... | no ctra = absurd (ctra refl)
mupdate-lookup {((y , S) ∷ c)} {x}  {T}  (there x≠y l) with x ≟ y
... | yes prf = absurd (x≠y prf)
... | no _    = mupdate-lookup l

