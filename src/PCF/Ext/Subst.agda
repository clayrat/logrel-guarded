module PCF.Ext.Subst where

open import Prelude
open import Data.Empty
open import Data.Unit
open import Data.Dec renaming (rec to recᵈ)
open import Data.Nat hiding (_·_)
open import Data.String
open import Data.List
open import Data.List.Correspondences.Unary.All

open import Interlude
open import PCF.Ext.TyTerm

infix 9 _[_:=_]

-- substitution

_[_:=_] : Term → Id → Term → Term
(` x)          [ y := T ] = recᵈ (λ _ → T) (λ _ → ` x) (x ≟ y)
(ƛ x ⦂ A ⇒ S)  [ y := T ] = recᵈ (λ _ → ƛ x ⦂ A ⇒ S) (λ _ → ƛ x ⦂ A ⇒ (S [ y := T ])) (x ≟ y)
(R · S)        [ y := T ] = R [ y := T ] · S [ y := T ]
(Y S)          [ y := T ] = Y (S [ y := T ])
(＃ n)         [ y := T ] = ＃ n
𝓈 S            [ y := T ] = 𝓈 (S [ y := T ])
𝓅 S            [ y := T ] = 𝓅 (S [ y := T ])
(?⁰ N ↑ R ↓ S) [ y := T ] = ?⁰ N [ y := T ] ↑ R [ y := T ] ↓ S [ y := T ]

vacuous-subst : ∀ M x
              → ¬ afi x M
              → ∀ N → M [ x := N ] ＝ M
vacuous-subst (` x) y nafi N with x ≟ y
... | yes prf = absurd (nafi (subst (afi y ∘ `_) (sym prf) afi-`))
... | no ctra = refl
vacuous-subst (ƛ x ⦂ A ⇒ M) y nafi N with x ≟ y
... | yes prf = refl
... | no ctra = ap (ƛ x ⦂ A ⇒_) (vacuous-subst M y (nafi ∘ afi-ƛ (ctra ∘ sym)) N)
vacuous-subst (L · M) y nafi N =
  ap² _·_ (vacuous-subst L y (nafi ∘ afi-·-l) N)
          (vacuous-subst M y (nafi ∘ afi-·-r) N)
vacuous-subst (Y M) y nafi N = ap Y_ (vacuous-subst M y (nafi ∘ afi-Y) N)
vacuous-subst (＃ n) y nafi N = refl
vacuous-subst (𝓈 M) y nafi N = ap 𝓈 (vacuous-subst M y (nafi ∘ afi-𝓈) N)
vacuous-subst (𝓅 M) y nafi N = ap 𝓅 (vacuous-subst M y (nafi ∘ afi-𝓅) N)
vacuous-subst (?⁰ L ↑ M ↓ N) y nafi T =
  ap³-simple ?⁰_↑_↓_ (vacuous-subst L y (nafi ∘ afi-?-b) T)
                     (vacuous-subst M y (nafi ∘ afi-?-t) T)
                     (vacuous-subst N y (nafi ∘ afi-?-f) T)

subst-closed : ∀ {M}
             → closed M
             → ∀ x N → M [ x := N ] ＝ M
subst-closed {M} c x = vacuous-subst M x (c x)

subst-not-afi : ∀ T x V
              → closed V
              → ¬ afi x (T [ x := V ])
subst-not-afi (` x)          y  V cV a     with x ≟ y
...                                       | yes prf = cV y a
subst-not-afi (` x)         .x V cV afi-` | no ctra = ctra refl
subst-not-afi (ƛ x ⦂ A ⇒ T)  y  V cV a with x ≟ y
subst-not-afi (ƛ x ⦂ A ⇒ T)  y  V cV (afi-ƛ ne a) | yes prf = ne (sym prf)
subst-not-afi (ƛ x ⦂ A ⇒ T)  y  V cV (afi-ƛ ne a) | no ctra =
  subst-not-afi T y V cV a
subst-not-afi (M · N)        x  V cV (afi-·-l a) =
  subst-not-afi M x V cV a
subst-not-afi (M · N)        x  V cV (afi-·-r a) =
  subst-not-afi N x V cV a
subst-not-afi (Y T)          x  V cV (afi-Y a) =
  subst-not-afi T x V cV a
subst-not-afi (𝓈 T)          x  V cV (afi-𝓈 a) =
  subst-not-afi T x V cV a
subst-not-afi (𝓅 T)          x  V cV (afi-𝓅 a) =
  subst-not-afi T x V cV a
subst-not-afi (?⁰ L ↑ M ↓ N) x  V cV (afi-?-b a) =
  subst-not-afi L x V cV a
subst-not-afi (?⁰ L ↑ M ↓ N) x  V cV (afi-?-t a) =
  subst-not-afi M x V cV a
subst-not-afi (?⁰ L ↑ M ↓ N) x  V cV (afi-?-f a) =
  subst-not-afi N x V cV a

duplicate-subst : ∀ t x v w
                → closed v
                → t [ x := v ] [ x := w ] ＝ t [ x := v ]
duplicate-subst t x v w cv = vacuous-subst (t [ x := v ]) x (subst-not-afi t x v cv) w

swap-subst : ∀ T x y V W
           → x ≠ y
           → closed V → closed W
           → T [ x := V ] [ y := W ] ＝ T [ y := W ] [ x := V ]
swap-subst (` x)          y z V W y≠z cV cW with x ≟ y | x ≟ z
swap-subst (` x)          y z V W y≠z cV cW | yes xy | yes xz = absurd (y≠z (sym xy ∙ xz))
swap-subst (` x)          y z V W y≠z cV cW | yes xy | no x≠z with x ≟ y
swap-subst (` x)          y z V W y≠z cV cW | yes xy | no x≠z | yes _ = subst-closed cV z W
swap-subst (` x)          y z V W y≠z cV cW | yes xy | no x≠z | no x≠y = absurd (x≠y xy)
swap-subst (` x)          y z V W y≠z cV cW | no x≠y | yes xz with x ≟ z
swap-subst (` x)          y z V W y≠z cV cW | no x≠y | yes xz | yes _ = sym (subst-closed cW y V)
swap-subst (` x)          y z V W y≠z cV cW | no x≠y | yes xz | no x≠z = absurd (x≠z xz)
swap-subst (` x)          y z V W y≠z cV cW | no x≠y | no x≠z with x ≟ z
swap-subst (` x)          y z V W y≠z cV cW | no x≠y | no x≠z | yes xz = absurd (x≠z xz)
swap-subst (` x)          y z V W y≠z cV cW | no x≠y | no x≠z | no _ with x ≟ y
swap-subst (` x)          y z V W y≠z cV cW | no x≠y | no x≠z | no _ | yes xy = absurd (x≠y xy)
swap-subst (` x)          y z V W y≠z cV cW | no x≠y | no x≠z | no _ | no _ = refl
swap-subst (ƛ x ⦂ A ⇒ T)  y z V W y≠z cV cW with x ≟ y | x ≟ z
swap-subst (ƛ x ⦂ A ⇒ T)  y z V W y≠z cV cW | yes xy | yes xz = absurd (y≠z (sym xy ∙ xz))
swap-subst (ƛ x ⦂ A ⇒ T)  y z V W y≠z cV cW | yes xy | no x≠z with x ≟ z
swap-subst (ƛ x ⦂ A ⇒ T)  y z V W y≠z cV cW | yes xy | no x≠z | yes xz = absurd (x≠z xz)
swap-subst (ƛ x ⦂ A ⇒ T)  y z V W y≠z cV cW | yes xy | no x≠z | no _ with x ≟ y
swap-subst (ƛ x ⦂ A ⇒ T)  y z V W y≠z cV cW | yes xy | no x≠z | no _ | yes _ = refl
swap-subst (ƛ x ⦂ A ⇒ T)  y z V W y≠z cV cW | yes xy | no x≠z | no _ | no x≠y = absurd (x≠y xy)
swap-subst (ƛ x ⦂ A ⇒ T)  y z V W y≠z cV cW | no x≠y | yes xz with x ≟ z
swap-subst (ƛ x ⦂ A ⇒ T)  y z V W y≠z cV cW | no x≠y | yes xz | yes _ with x ≟ y
swap-subst (ƛ x ⦂ A ⇒ T)  y z V W y≠z cV cW | no x≠y | yes xz | yes _ | yes xy = absurd (x≠y xy)
swap-subst (ƛ x ⦂ A ⇒ T)  y z V W y≠z cV cW | no x≠y | yes xz | yes _ | no _ = refl
swap-subst (ƛ x ⦂ A ⇒ T)  y z V W y≠z cV cW | no x≠y | yes xz | no x≠z = absurd (x≠z xz)
swap-subst (ƛ x ⦂ A ⇒ T)  y z V W y≠z cV cW | no x≠y | no x≠z with x ≟ z
swap-subst (ƛ x ⦂ A ⇒ T)  y z V W y≠z cV cW | no x≠y | no x≠z | yes xz = absurd (x≠z xz)
swap-subst (ƛ x ⦂ A ⇒ T)  y z V W y≠z cV cW | no x≠y | no x≠z | no _ with x ≟ y
swap-subst (ƛ x ⦂ A ⇒ T)  y z V W y≠z cV cW | no x≠y | no x≠z | no _ | yes xy = absurd (x≠y xy)
swap-subst (ƛ x ⦂ A ⇒ T)  y z V W y≠z cV cW | no x≠y | no x≠z | no _ | no _ =
  ap (ƛ x ⦂ A ⇒_) (swap-subst T y z V W y≠z cV cW)
swap-subst (M · N)        x y V W x≠y cV cW =
  ap² _·_ (swap-subst M x y V W x≠y cV cW)
          (swap-subst N x y V W x≠y cV cW)
swap-subst (Y T)          x y V W x≠y cV cW =
  ap Y_ (swap-subst T x y V W x≠y cV cW)
swap-subst (＃ n)         x y V W x≠y cV cW = refl
swap-subst (𝓈 T)          x y V W x≠y cV cW =
  ap 𝓈 (swap-subst T x y V W x≠y cV cW)
swap-subst (𝓅 T)          x y V W x≠y cV cW =
  ap 𝓅 (swap-subst T x y V W x≠y cV cW)
swap-subst (?⁰ L ↑ M ↓ N) x y V W x≠y cV cW =
  ap³-simple ?⁰_↑_↓_ (swap-subst L x y V W x≠y cV cW)
                     (swap-subst M x y V W x≠y cV cW)
                     (swap-subst N x y V W x≠y cV cW)

-- multisubstitution

Env : 𝒰
Env = List (Id × Term)

closed-env : (@0 e : Env) → 𝒰
closed-env = All (closed ∘ snd)

msubst : Env → Term → Term
msubst []            T = T
msubst ((x , S) ∷ E) T = msubst E (T [ x := S ])

-- lemmas

msubst-closed : ∀ {M}
              → closed M
              → ∀ E → msubst E M ＝ M
msubst-closed c []            = refl
msubst-closed c ((y , N) ∷ E) =
  ap (msubst E) (subst-closed c y N) ∙ msubst-closed c E

subst-msubst : ∀ {E V}
             → closed V → closed-env E
             → ∀ x T
             → msubst E (T [ x := V ]) ＝ (msubst (drp x E) T) [ x := V ]
subst-msubst {E = []}            cV []        x T = refl
subst-msubst {((y , P) ∷ E)} {V} cV (cp ∷ ce) x T with x ≟ y
... | yes prf = ap (msubst E) (ap (λ q → T [ x := V ] [ q := P ]) (sym prf)
                               ∙ duplicate-subst T x V P cV)
              ∙ subst-msubst cV ce x T
... | no ctra = ap (msubst E) (swap-subst T x y V P ctra cV cp)
              ∙ subst-msubst cV ce x (T [ y := P ])

msubst-` : ∀ {E}
         → closed-env E
         → ∀ x
         → msubst E (` x) ＝ extract (` x) (lup x E)
msubst-` {E = []}        []        x = refl
msubst-` {((y , t) ∷ E)} (ct ∷ cE) x with x ≟ y
... | yes prf = msubst-closed ct E
... | no ctra = msubst-` cE x

msubst-ƛ : ∀ E x A T
         → msubst E (ƛ x ⦂ A ⇒ T) ＝ ƛ x ⦂ A ⇒ msubst (drp x E) T
msubst-ƛ []            x A T = refl
msubst-ƛ ((y , S) ∷ E) x A T  with x ≟ y
... | yes prf = msubst-ƛ E x A T
... | no ctra = msubst-ƛ E x A (T [ y := S ])

msubst-· : ∀ E M N
         → msubst E (M · N) ＝ (msubst E M) · (msubst E N)
msubst-· []            M N = refl
msubst-· ((y , T) ∷ E) M N = msubst-· E (M [ y := T ]) (N [ y := T ])

msubst-Y : ∀ E M
         → msubst E (Y M) ＝ Y (msubst E M)
msubst-Y []            M = refl
msubst-Y ((x , T) ∷ E) M = msubst-Y E (M [ x := T ])

msubst-＃ : ∀ {E n}
          → msubst E (＃ n) ＝ ＃ n
msubst-＃ {E = []}    = refl
msubst-＃ {E = x ∷ E} = msubst-＃ {E}

msubst-𝓈 : ∀ {E M}
          → msubst E (𝓈 M) ＝ 𝓈 (msubst E M)
msubst-𝓈 {E = []}              = refl
msubst-𝓈 {E = (x , N) ∷ E} {M} = msubst-𝓈 {E} {M = M [ x := N ]}

msubst-𝓅 : ∀ {E M}
          → msubst E (𝓅 M) ＝ 𝓅 (msubst E M)
msubst-𝓅 {E = []}              = refl
msubst-𝓅 {E = (x , N) ∷ E} {M} = msubst-𝓅 {E} {M = M [ x := N ]}

msubst-? : ∀ E L M N
         → msubst E (?⁰ L ↑ M ↓ N) ＝ ?⁰ (msubst E L) ↑ (msubst E M) ↓ (msubst E N)
msubst-? []            L M N = refl
msubst-? ((x , T) ∷ E) L M N = msubst-? E (L [ x := T ]) (M [ x := T ]) (N [ x := T ])
