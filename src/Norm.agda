module Norm where

open import Prelude
open import Data.Empty

open import Data.Dec
open import Data.Bool
open import Data.String
open import Data.Maybe
open import Data.List

open import All
open import Term
open import Ty

-- TODO move
_↔_ : 𝒰 → 𝒰 → 𝒰
A ↔ B = (A → B) × (B → A)

halts : Term → 𝒰
halts t = Σ[ t′ ꞉ Term ] (t —↠ t′) × Value t′

value-halts : {v : Term} → Value v → halts v
value-halts {v} V = v , (v ∎ᵣ) , V

step-preserves-halting : {t t′ : Term}
                       → (t —→ t′) → (halts t ↔ halts t′)
step-preserves-halting {t} {t′} S =
  (λ where
      (t″ , (.t″ ∎ᵣ) , V) →
        absurd (value-nf V (t′ , S))
      (t″ , (.t —→⟨ TM ⟩ STM) , V) →
        t″ , subst (_—↠ t″) (step-det _ _ _ TM S) STM , V)
  ,
  (λ where
      (t₀ , STM , V) → t₀ , (t —→⟨ S ⟩ STM) , V) 

---

R : (T : Ty) → (t : Term) → 𝒰
R (T₁ ⇒ T₂) t = (∅ ⊢ t ⦂ (T₁ ⇒ T₂)) × halts t × (∀ s → R T₁ s → R T₂ (t · s))
R  𝟙        t = (∅ ⊢ t ⦂ 𝟙) × halts t

R-halts : (T : Ty) → (t : Term) → R T t → halts t
R-halts (T₁ ⇒ T₂) t (_ , h , _) = h
R-halts  𝟙        t (_ , h)     = h

R-typable-empty : (T : Ty) → (t : Term) → R T t → ∅ ⊢ t ⦂ T
R-typable-empty (T₁ ⇒ T₂) t (tp , _ , _) = tp
R-typable-empty  𝟙        t (tp , _)     = tp

step-preserves-R : ∀ T t t′
                 → (t —→ t′) → R T t → R T t′
step-preserves-R (T₁ ⇒ T₂) t t′ S (tp , h , Ri) =
  preserve tp S , step-preserves-halting S .fst h ,
    λ t″ R₁ → step-preserves-R T₂ (t · t″) (t′ · t″) (ξ-·₁ S) (Ri t″ R₁)
step-preserves-R  𝟙       t t′ S (tp , h)      =
  (preserve tp S) , (step-preserves-halting S .fst h)

multistep-preserves-R : ∀ T t t′
                      → (t —↠ t′) → R T t → R T t′
multistep-preserves-R T t .t  (.t ∎ᵣ)         Rt = Rt
multistep-preserves-R T t  t′ (.t —→⟨ TM ⟩ M) Rt =
  multistep-preserves-R _ _ _ M (step-preserves-R _ _ _ TM Rt)

step-preserves-R' : ∀ T t t′
                  → ∅ ⊢ t ⦂ T → (t —→ t′) → R T t′ → R T t
step-preserves-R' (T₁ ⇒ T₂) t t′ tp S (_ , h′ , Ri) =
  tp , step-preserves-halting S .snd h′ ,
    λ t″ R₁ → step-preserves-R' T₂ (t · t″) (t′ · t″)
                (tp ⊢· R-typable-empty T₁ t″ R₁)
                (ξ-·₁ S) (Ri t″ R₁)
step-preserves-R'  𝟙        t t′ tp S (_ , h′)      =
  tp , step-preserves-halting S .snd h′

multistep-preserves-R' : ∀ T t t′
                       → ∅ ⊢ t ⦂ T → (t —↠ t′) → R T t′ → R T t
multistep-preserves-R' T t .t  tp (.t ∎ᵣ)         Rt = Rt
multistep-preserves-R' T t  t′ tp (.t —→⟨ TM ⟩ S) Rt =
  step-preserves-R' _ _ _ tp TM (multistep-preserves-R' _ _ _ (preserve tp TM) S Rt)

-- Multisubstitutions, Multi-Extensions, and Instantiations

Env : 𝒰
Env = List (String × Term)

msubst : Env → Term → Term 
msubst []             t = t
msubst ((x , s) ∷ ss) t = msubst ss (t [ x := s ])

Tass : 𝒰
Tass = List (String × Ty)

mupdate : Tass → Context → Context
mupdate []              Γ = Γ
mupdate ((x , v) ∷ xts) Γ = (mupdate xts Γ) , x ⦂ v

lup : {X : 𝒰} → String → List (String × X) → Maybe X
lup k []            = nothing
lup k ((j , x) ∷ l) = if ⌊ k ≟ j ⌋ then just x else lup k l

-- TODO formulate with filter
drp : {X : 𝒰} → String → List (String × X) → List (String × X)
drp n []              = []
drp n ((m , x) ∷ nxs) = if ⌊ n ≟ m ⌋ then drp n nxs else (m , x) ∷ drp n nxs

data Inst : Tass → Env → 𝒰 where
  V-nil : Inst [] []
  V-cons : ∀ {x T v c e}
         → Value v → R T v → Inst c e
         → Inst ((x , T) ∷ c) ((x , v) ∷ e)

-- substitution redux

vacuous-subst : ∀ t x
              → ¬ afi x t → ∀ t′ → t [ x := t′ ] ＝ t
vacuous-subst (` y)     x nafi t′ with y ≟ x
... | yes prf = absurd (nafi (subst (λ q → afi x (` q)) (sym prf) afi-var))
... | no ctra = refl
vacuous-subst (ƛ y ⇒ t) x nafi t′ with y ≟ x
... | yes prf = refl
... | no ctra = ap (ƛ y ⇒_) (vacuous-subst t x (nafi ∘ afi-abs (ctra ∘ sym)) t′)
vacuous-subst (t₁ · t₂) x nafi t′ =
  ap² _·_ (vacuous-subst t₁ x (nafi ∘ afi-appl) t′)
          (vacuous-subst t₂ x (nafi ∘ afi-appr) t′)

subst-closed : ∀ t
             → closed t → ∀ x t′ → t [ x := t′ ] ＝ t
subst-closed t c x t′ = vacuous-subst t x (c x) t′

subst-not-afi : ∀ t x v
              → closed v → ¬ afi x (t [ x := v ])
subst-not-afi (` y)      x v cv a with y ≟ x
...                                     | yes _   = cv x a
subst-not-afi (` y)     .y v cv afi-var | no ctra = ctra refl
subst-not-afi (ƛ y ⇒ t)  x v cv a with y ≟ x
subst-not-afi (ƛ y ⇒ t)  x v cv (afi-abs x≠y a) | yes prf = x≠y (sym prf)
subst-not-afi (ƛ y ⇒ t)  x v cv (afi-abs x≠y a) | no _    =
  subst-not-afi t x v cv a
subst-not-afi (t₁ · t₂)  x v cv (afi-appl a) = subst-not-afi t₁ x v cv a
subst-not-afi (t₁ · t₂)  x v cv (afi-appr a) = subst-not-afi t₂ x v cv a

duplicate-subst : ∀ t x v w → closed v → t [ x := v ] [ x := w ] ＝ t [ x := v ]
duplicate-subst t x v w cv = vacuous-subst (t [ x := v ]) x (subst-not-afi t x v cv) w

-- noisy because of repeated matching (can't backpropagate a match after a same redex has surfaced)
swap-subst : ∀ t x y v w
           → x ≠ y → closed v → closed w
           → t [ x := v ] [ y := w ] ＝ t [ y := w ] [ x := v ]
swap-subst (` z)     x y v w x≠y cv cw with z ≟ x | z ≟ y
swap-subst (` z)     x y v w x≠y cv cw | yes zx | yes zy  = absurd (x≠y (sym zx ∙ zy))
swap-subst (` z)     x y v w x≠y cv cw | yes zx | no z≠y with z ≟ x -- AARGH
swap-subst (` z)     x y v w x≠y cv cw | yes zx | no z≠y | yes _ = subst-closed v cv y w
swap-subst (` z)     x y v w x≠y cv cw | yes zx | no z≠y | no ctra = absurd (ctra zx)
swap-subst (` z)     x y v w x≠y cv cw | no z≠x | yes zy with z ≟ y -- AARGH
swap-subst (` z)     x y v w x≠y cv cw | no z≠x | yes zy | yes _ = sym (subst-closed w cw x v) 
swap-subst (` z)     x y v w x≠y cv cw | no z≠x | yes zy | no ctra = absurd (ctra zy)
swap-subst (` z)     x y v w x≠y cv cw | no z≠x | no z≠y with z ≟ x  -- AAAARGGH
swap-subst (` z)     x y v w x≠y cv cw | no z≠x | no z≠y | yes prf = absurd (z≠x prf)
swap-subst (` z)     x y v w x≠y cv cw | no z≠x | no z≠y | no _ with z ≟ y
swap-subst (` z)     x y v w x≠y cv cw | no z≠x | no z≠y | no _ | yes prf = absurd (z≠y prf)
swap-subst (` z)     x y v w x≠y cv cw | no z≠x | no z≠y | no _ | no _ = refl
swap-subst (ƛ z ⇒ t) x y v w x≠y cv cw with z ≟ x | z ≟ y
swap-subst (ƛ z ⇒ t) x y v w x≠y cv cw | yes zx | yes zy = absurd (x≠y (sym zx ∙ zy))
swap-subst (ƛ z ⇒ t) x y v w x≠y cv cw | yes zx | no z≠y with z ≟ x -- AARGH
swap-subst (ƛ z ⇒ t) x y v w x≠y cv cw | yes zx | no z≠y | yes _ with z ≟ y
swap-subst (ƛ z ⇒ t) x y v w x≠y cv cw | yes zx | no z≠y | yes _ | yes prf = absurd (z≠y prf)
swap-subst (ƛ z ⇒ t) x y v w x≠y cv cw | yes zx | no z≠y | yes _ | no _ = refl
swap-subst (ƛ z ⇒ t) x y v w x≠y cv cw | yes zx | no z≠y | no ctra = absurd (ctra zx)
swap-subst (ƛ z ⇒ t) x y v w x≠y cv cw | no z≠x | yes zy with z ≟ x -- AARGH 
swap-subst (ƛ z ⇒ t) x y v w x≠y cv cw | no z≠x | yes zy | yes prf = absurd (z≠x prf)
swap-subst (ƛ z ⇒ t) x y v w x≠y cv cw | no z≠x | yes zy | no _ with z ≟ y
swap-subst (ƛ z ⇒ t) x y v w x≠y cv cw | no z≠x | yes zy | no _ | yes _ = refl
swap-subst (ƛ z ⇒ t) x y v w x≠y cv cw | no z≠x | yes zy | no _ | no ctra = absurd (ctra zy)
swap-subst (ƛ z ⇒ t) x y v w x≠y cv cw | no z≠x | no z≠y with z ≟ x -- AARGH
swap-subst (ƛ z ⇒ t) x y v w x≠y cv cw | no z≠x | no z≠y | yes prf = absurd (z≠x prf)
swap-subst (ƛ z ⇒ t) x y v w x≠y cv cw | no z≠x | no z≠y | no _ with z ≟ y
swap-subst (ƛ z ⇒ t) x y v w x≠y cv cw | no z≠x | no z≠y | no _ | yes prf = absurd (z≠y prf)
swap-subst (ƛ z ⇒ t) x y v w x≠y cv cw | no z≠x | no z≠y | no _ | no _ =
  ap (ƛ z ⇒_) (swap-subst t x y v w x≠y cv cw)
swap-subst (t₁ · t₂) x y v w x≠y cv cw =
  ap² (_·_) (swap-subst t₁ x y v w x≠y cv cw)
            (swap-subst t₂ x y v w x≠y cv cw)

msubst-closed : ∀ t → closed t → ∀ ss → msubst ss t ＝ t
msubst-closed t ct []             = refl
msubst-closed t ct ((y , s) ∷ ss) =
  ap (msubst ss) (subst-closed t ct y s) ∙ msubst-closed t ct ss

closed-env : (@0 e : Env) → 𝒰
closed-env = All (closed ∘ snd) 

subst-msubst : ∀ env x v t
             → closed v → closed-env env
             → msubst env (t [ x := v ]) ＝ (msubst (drp x env) t) [ x := v ] 
subst-msubst []              x v t cv []        = refl
subst-msubst ((y , p) ∷ env) x v t cv (cp ∷ ce) with x ≟ y
... | yes prf = ap (msubst env) (ap (λ q → t [ x := v ] [ q := p ]) (sym prf)
                                 ∙ duplicate-subst t x v p cv)
              ∙ subst-msubst env x v t cv ce 
... | no ctra = ap (msubst env) (swap-subst t x y v p ctra cv cp)
              ∙ subst-msubst env x v (t [ y := p ]) cv ce

msubst-var : ∀ ss x
           → closed-env ss
           → msubst ss (` x) ＝ Data.Maybe.rec (` x) id (lup x ss)
msubst-var []             x []         = refl
msubst-var ((y , t) ∷ ss) x (ct ∷ css) with x ≟ y
... | yes prf = msubst-closed t ct ss
... | no ctra = msubst-var ss x css

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

mupdate-lookup : ∀ c x T
               → mupdate c ∅ ∋ x ⦂ T
               → lup x c ＝ just T
mupdate-lookup ((y , S) ∷ c) .y .S  here         with y ≟ y  -- wtf
... | yes _   = refl
... | no ctra = absurd (ctra refl)
mupdate-lookup ((y , S) ∷ c)  x  T (there x≠y l) with x ≟ y
... | yes prf = absurd (x≠y prf)
... | no _    = mupdate-lookup c x T l

instantiation-domains-match : ∀ {c e}
                            → Inst c e
                            → ∀ {x T}
                            → lup x c ＝ just T
                            → Σ[ t ꞉ Term ] (lup x e ＝ just t)
instantiation-domains-match  V-nil                         eq =
  absurd (nothing≠just eq)
instantiation-domains-match (V-cons {x = y} {v} V r i) {x} eq with x ≟ y 
... | yes prf = v , refl
... | no ctra = instantiation-domains-match i eq

instantiation-env-closed : ∀ c e
                         → Inst c e
                         → closed-env e
instantiation-env-closed .[]            .[]             V-nil                             = []
instantiation-env-closed .((x , T) ∷ c) .((x , v) ∷ e) (V-cons {x} {T} {v} {c} {e} V r i) =
  ∅⊢-closed (R-typable-empty T v r) ∷ instantiation-env-closed c e i

instantiation-R : ∀ c e
                → Inst c e
                → ∀ x t T
                → lup x c ＝ just T
                → lup x e ＝ just t
                → R T t
instantiation-R .[]            .[]             V-nil                                     x t T ec ee =
  absurd (nothing≠just ee)
instantiation-R .((y , S) ∷ c) .((y , v) ∷ e) (V-cons {x = y} {T = S} {v} {c} {e} V r i) x t T ec ee with x ≟ y 
... | yes prf = subst (λ q → R q t) (just-inj ec) (subst (R S) (just-inj ee) r)
... | no ctra = instantiation-R c e i x t T ec ee

instantiation-drop : ∀ c e
                   → Inst c e
                   → ∀ x → Inst (drp x c) (drp x e)
instantiation-drop .[]            .[]             V-nil                                 x = V-nil
instantiation-drop .((y , T) ∷ c) .((y , v) ∷ e) (V-cons {x = y} {T} {v} {c} {e} V r i) x with x ≟ y 
... | yes prf = instantiation-drop c e i x
... | no ctra = V-cons V r (instantiation-drop c e i x)

-- Congruence Lemmas on Multistep

multistep-appr : ∀ v t t′
               → Value v
               → (t —↠ t′)
               → (v · t) —↠ (v · t′)
multistep-appr v t .t  V (.t ∎ᵣ)        = v · t ∎ᵣ
multistep-appr v t  t′ V (.t —→⟨ T ⟩ S) = v · t —→⟨ ξ-·₂ V T ⟩ multistep-appr _ _ _ V S

-- The R Lemma

msubst-preserves-typing : ∀ c e
                        → Inst c e
                        → ∀ Γ t S
                        → (mupdate c Γ) ⊢ t ⦂ S
                        → Γ ⊢ (msubst e t) ⦂ S
msubst-preserves-typing .[]            .[]             V-nil                             Γ t S ty = ty
msubst-preserves-typing .((x , T) ∷ c) .((x , v) ∷ e) (V-cons {x} {T} {v} {c} {e} V r i) Γ t S ty =
  msubst-preserves-typing c e i Γ (t [ x := v ]) S (subst-ty (R-typable-empty T v r) ty)

msubst-R : ∀ c e t T
         → (mupdate c ∅) ⊢ t ⦂ T
         → Inst c e
         → R T (msubst e t)
msubst-R c e .(` x)      T       (⊢` {x} l)              i =
  let lupc = mupdate-lookup c x T l
      t′ , P = instantiation-domains-match i lupc
    in 
  instantiation-R c e i x (msubst e (` x)) T lupc
    (P ∙ ap just (sym (ap (Data.Maybe.rec (` x) id) P)
                       ∙ sym (msubst-var e x (instantiation-env-closed c e i))))
msubst-R c e .(ƛ x ⇒ N) .(A ⇒ B) (⊢ƛ {x} {N} {A} {B} ty) i =
  let mabs = msubst-abs e x N 
      WT : ∅ ⊢ ƛ x ⇒ msubst (drp x e) N ⦂ A ⇒ B
      WT = ⊢ƛ $ msubst-preserves-typing (drp x c) (drp x e)
                    (instantiation-drop c e i x)
                    (∅ , x ⦂ A) N B
                    (weaken (go c x A) ty)
      in
    subst (λ q → ∅ ⊢ q ⦂ A ⇒ B) (sym mabs) WT  
  , value-halts (subst Value (sym mabs) V-ƛ) 
  , λ s Rs →
      let v , P , Q  = R-halts A s Rs
          Rv = multistep-preserves-R A s v P Rs
       in
      subst (λ q → R B (q · s)) (sym mabs) $
      multistep-preserves-R' B ((ƛ x ⇒ msubst (drp x e) N) · s) (msubst ((x , v) ∷ e) N)
        (WT ⊢· (R-typable-empty A s Rs))
        (multistep-appr (ƛ x ⇒ msubst (drp x e) N) s v V-ƛ P
          —↠∘
         (((ƛ x ⇒ msubst (drp x e) N) · v)
              —→⟨  subst (λ q → (ƛ x ⇒ msubst (drp x e) N) · v —→ q)
                         (sym (subst-msubst e x v N (∅⊢-closed (R-typable-empty A v Rv))
                                                    (instantiation-env-closed c e i)))
                         (β-ƛ Q) ⟩
                (msubst e (N [ x := v ]) ∎ᵣ)))
        (msubst-R ((x , A) ∷ c) ((x , v) ∷ e) N B ty (V-cons Q Rv i))
  where
  go : ∀ c x A → (mupdate c ∅ , x ⦂ A) ⊆ mupdate (drp x c) (∅ , x ⦂ A)
  go []            x A T i l = l
  go ((y , p) ∷ c) x A T i l with x ≟ y
  ... | yes prf = go c x A T i (⊆-shadow T i (subst (λ q → mupdate c ∅ , q ⦂ p , x ⦂ A ∋ i ⦂ T) (sym prf) l))
  go ((y , p) ∷ c) x A .A .x  here                     | no ctra = there ctra (go c x A A x here)
  go ((y , p) ∷ c) x A .p .y (there _    here)         | no ctra = here
  go ((y , p) ∷ c) x A  T  i (there i≠x (there i≠y l)) | no ctra = there i≠y (go c x A T i (there i≠x l))
msubst-R c e .(L · M)    T       (_⊢·_ {L} {M} {A} ty₁ ty₂) i =
  subst (R T) (sym (msubst-app e L M)) $
  msubst-R c e L (A ⇒ T) ty₁ i .snd .snd _ $
  msubst-R c e M A ty₂ i 

normalization : ∀ t T
              → ∅ ⊢ t ⦂ T → halts t
normalization t T ty = R-halts T t (msubst-R [] [] t T ty V-nil)
