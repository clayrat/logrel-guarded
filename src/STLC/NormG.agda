{-# OPTIONS --guarded #-}
module STLC.NormG where

open import Prelude
open import Data.Empty
open import Data.Dec
open import Data.String
open import Data.Maybe

open import LaterG
open import PartialG

open import Interlude
open import All
open import STLC.Term
open import STLC.Ty
open import STLC.Multi

--- guarded version of the R logical relation as data

{-
data R : Ty → Term → 𝒰 where

  R𝟙 : ∀ {t}
     → ∅ ⊢ t ⦂ 𝟙
     → halts t
     → R 𝟙 t

  R⇒ : ∀ {T₁ T₂ t}
     → ∅ ⊢ t ⦂ (T₁ ⇒ T₂)
     → halts t
     → (∀ s → Part (▹ (R T₁ s)) → Part (▹ (R T₂ (t · s))))
     → R (T₁ ⇒ T₂) t
-}

R-case : (Ty → Term → ▹ 𝒰) → Ty → Term → 𝒰
R-case R▹ (T₁ ⇒ T₂) t = (∅ ⊢ t ⦂ (T₁ ⇒ T₂))
                      × halts t
                      × (∀ s → Part (▸ (R▹ T₁ s)) → Part (▸ (R▹ T₂ (t · s))))
R-case R▹  𝟙        t = (∅ ⊢ t ⦂ 𝟙)
                      × halts t

R-body : ▹ (Ty → Term → 𝒰) → Ty → Term → 𝒰
R-body f = R-case (λ T t → f ⊛ next T ⊛ next t)

R : Ty → Term → 𝒰
R = fix R-body

-- constructors

R𝟙 : ∀ {t}
   → ∅ ⊢ t ⦂ 𝟙 → halts t
   → R 𝟙 t
R𝟙 ty h = ty , h

R⇒ : ∀ {T₁ T₂ t}
   → ∅ ⊢ t ⦂ (T₁ ⇒ T₂) → halts t
   → (∀ s → Part (▹ (R T₁ s)) → Part (▹ (R T₂ (t · s))))
   → R (T₁ ⇒ T₂) t
R⇒ {T₁} {T₂} {t} ty h r =
  ty , h , λ s → transport (λ i → Part (▹[ α ] (pfix R-body (~ i) α T₁ s))
                                → Part (▹[ α ] (pfix R-body (~ i) α T₂ (t · s))))
                           (r s)

-- destructors

R𝟙-match : ∀ {t}
   → R 𝟙 t
   → (∅ ⊢ t ⦂ 𝟙) × halts t
R𝟙-match = id

R⇒-match : ∀ {T₁ T₂ t}
         → R (T₁ ⇒ T₂) t
         → (∅ ⊢ t ⦂ (T₁ ⇒ T₂)) × halts t × (∀ s → Part (▹ R T₁ s) → Part (▹ R T₂ (t · s)))
R⇒-match {T₁} {T₂} {t} (ty , h , r) =
  ty , h , λ s → transport (λ i → Part (▹[ α ] (pfix R-body i α T₁ s))
                                → Part (▹[ α ] (pfix R-body i α T₂ (t · s))))
                           (r s)

-- projections

R-halts : (T : Ty) → (t : Term) → R T t → halts t
R-halts (T₁ ⇒ T₂) t (_ , h , _) = h
R-halts  𝟙        t (_ , h)     = h

R-typable-empty : (T : Ty) → (t : Term) → R T t → ∅ ⊢ t ⦂ T
R-typable-empty (T₁ ⇒ T₂) t (tp , _ , _) = tp
R-typable-empty  𝟙        t (tp , _)     = tp

-- R properties

step-preserves-R : ∀ T t t′
                 → (t —→ t′) → R T t → R T t′
step-preserves-R (T₁ ⇒ T₂) t t′ S r = let tp , h , Ri = R⇒-match r in
  R⇒ (preserve tp S)
     (step-preserves-halting S .fst h)
     (λ t″ R₁ → mapᵖ (▹map (step-preserves-R T₂ (t · t″) (t′ · t″) (ξ-·₁ S)))
                     (Ri t″ R₁))
step-preserves-R  𝟙        t t′ S r = let tp , h = R𝟙-match r in
  R𝟙 (preserve tp S)
     (step-preserves-halting S .fst h)

multistep-preserves-R : ∀ T t t′
                      → (t —↠ t′) → R T t → R T t′
multistep-preserves-R T t .t  (.t ∎ᵣ)         Rt = Rt
multistep-preserves-R T t  t′ (.t —→⟨ TM ⟩ M) Rt =
  multistep-preserves-R _ _ _ M (step-preserves-R _ _ _ TM Rt)

step-preserves-R' : ∀ T t t′
                  → ∅ ⊢ t ⦂ T → (t —→ t′) → R T t′ → R T t
step-preserves-R' (T₁ ⇒ T₂) t t′ tp S r = let (_ , h′ , Ri) = R⇒-match r in
  R⇒ tp (step-preserves-halting S .snd h′)
     (λ t″ R₁ → map²ᵖ (▹map² ((λ x → step-preserves-R' T₂ (t · t″) (t′ · t″)
                                   (tp ⊢· R-typable-empty T₁ t″ x) (ξ-·₁ S))))
                       R₁ (Ri t″ R₁))
step-preserves-R'  𝟙        t t′ tp S r = let (_ , h′) = R𝟙-match r in
  R𝟙 tp (step-preserves-halting S .snd h′)

multistep-preserves-R' : ∀ T t t′
                       → ∅ ⊢ t ⦂ T → (t —↠ t′) → R T t′ → R T t
multistep-preserves-R' T t .t  tp (.t ∎ᵣ)         Rt = Rt
multistep-preserves-R' T t  t′ tp (.t —→⟨ TM ⟩ S) Rt =
  step-preserves-R' _ _ _ tp TM (multistep-preserves-R' _ _ _ (preserve tp TM) S Rt)

-- instantiations

data Inst : Tass → Env → 𝒰 where
  V-nil : Inst [] []
  V-cons : ∀ {x T v c e}
         → Value v → R T v → Inst c e
         → Inst ((x , T) ∷ c) ((x , v) ∷ e)

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
         → Part (R T (msubst e t))
msubst-R c e .(` x)      T       (⊢` {x} l)              i =
  let lupc = mupdate-lookup c x T l
      t′ , P = instantiation-domains-match i lupc
    in
  now $
  instantiation-R c e i x (msubst e (` x)) T lupc
    (P ∙ ap just (sym (ap (extract (` x)) P)
                       ∙ sym (msubst-var e x (instantiation-env-closed c e i))))
msubst-R c e .(ƛ x ⇒ N) .(A ⇒ B) (⊢ƛ {x} {N} {A} {B} ty) i =
  let mabs = msubst-abs e x N
      WT : ∅ ⊢ ƛ x ⇒ msubst (drp x e) N ⦂ A ⇒ B
      WT = ⊢ƛ $ msubst-preserves-typing (drp x c) (drp x e)
                    (instantiation-drop c e i x)
                    (∅ , x ⦂ A) N B
                    (weaken (go c x A) ty)
      in
   now $
   R⇒ (subst (λ q → ∅ ⊢ q ⦂ A ⇒ B) (sym mabs) WT)
      (value-halts (subst Value (sym mabs) V-ƛ))
      (λ s Rp → Rp >>=ᵖ λ R▹ →
         ▹Part $
         ▹map (λ Rs →
               let v , P , Q = R-halts A s Rs
                   Rv = multistep-preserves-R A s v P Rs
                in
                mapᵖ (λ R2 →
                       subst (λ q → R B (q · s)) (sym mabs) $
                       multistep-preserves-R' B
                         ((ƛ x ⇒ msubst (drp x e) N) · s)
                         (msubst ((x , v) ∷ e) N)
                         (WT ⊢· (R-typable-empty A s Rs))
                         (multistep-appr (ƛ x ⇒ msubst (drp x e) N) s v V-ƛ P
                                          —↠∘
                                         (((ƛ x ⇒ msubst (drp x e) N) · v)
                                              —→⟨ subst (λ q → (ƛ x ⇒ msubst (drp x e) N) · v —→ q)
                                                        (sym $ subst-msubst e x v N
                                                                 (∅⊢-closed (R-typable-empty A v Rv))
                                                                 (instantiation-env-closed c e i))
                                                        (β-ƛ Q) ⟩
                                                (msubst e (N [ x := v ]) ∎ᵣ)))
                          R2)
                     (msubst-R ((x , A) ∷ c) ((x , v) ∷ e) N B ty (V-cons Q Rv i)))
              R▹)
  where
  go : ∀ c x A → (mupdate c ∅ , x ⦂ A) ⊆ mupdate (drp x c) (∅ , x ⦂ A)
  go []            x A  T  i  l = l
  go ((y , p) ∷ c) x A  T  i  l with x ≟ y
  ... | yes prf = go c x A T i (⊆-shadow T i (subst (λ q → mupdate c ∅ , q ⦂ p , x ⦂ A ∋ i ⦂ T) (sym prf) l))
  go ((y , p) ∷ c) x A .A .x  here                     | no ctra = there ctra (go c x A A x here)
  go ((y , p) ∷ c) x A .p .y (there _    here)         | no ctra = here
  go ((y , p) ∷ c) x A  T  i (there i≠x (there i≠y l)) | no ctra = there i≠y (go c x A T i (there i≠x l))
msubst-R c e .(L · M)    T       (_⊢·_ {L} {M} {A} ty₁ ty₂) i =
  (msubst-R c e L (A ⇒ T) ty₁ i) >>=ᵖ λ R1 →
  let (_ , _ , R1→) = R⇒-match R1 in
  (msubst-R c e M A ty₂ i) >>=ᵖ λ R2 →
  let Rapp = R1→ (msubst e M) (now (next R2)) in
  later (Part▹ (subst (λ q → ▹ R T q) (sym $ msubst-app e L M)) Rapp)

normalization : ∀ t T
              → ∅ ⊢ t ⦂ T
              → Part (halts t)
normalization t T ty = mapᵖ (R-halts T t) (msubst-R [] [] t T ty V-nil)
