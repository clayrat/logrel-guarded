module STLC.Norm where

open import Prelude
open import Data.Empty
open import Data.Dec
open import Data.String
open import Data.Maybe
open import Data.List.Correspondences.Unary.All

open import Interlude
open import STLC.Term
open import STLC.Ty
open import STLC.Multi

--- R logical relation

R : Ty → Term → 𝒰
R  𝟙        t = (∅ ⊢ t ⦂ 𝟙)
              × halts t
R (T₁ ⇒ T₂) t = (∅ ⊢ t ⦂ T₁ ⇒ T₂)
              × halts t
              × (∀ s → R T₁ s → R T₂ (t · s))

R-halts : ∀ {T t} → R T t → halts t
R-halts {T = 𝟙}       (_ , h)     = h
R-halts {T = T₁ ⇒ T₂} (_ , h , _) = h

R-typable-empty : ∀ {T t} → R T t → ∅ ⊢ t ⦂ T
R-typable-empty {T = 𝟙}       (tp , _)     = tp
R-typable-empty {T = T₁ ⇒ T₂} (tp , _ , _) = tp

step-preserves-R : ∀ {T t t′}
                 → (t —→ t′) → R T t → R T t′
step-preserves-R {T = 𝟙}       {t} {t′} S (tp , h)              =
  (preserve tp S) , (step-preserves-halting S .fst h)
step-preserves-R {T = T₁ ⇒ T₂} {t} {t′} S (tp , h , Ri)         =
  preserve tp S , step-preserves-halting S .fst h ,
    λ t″ R₁ → step-preserves-R (ξ-·₁ S) (Ri t″ R₁)

multistep-preserves-R : ∀ {T t t′}
                      → (t —↠ t′) → R T t → R T t′
multistep-preserves-R {T} {t} {.t} (.t ∎ᵣ)         Rt = Rt
multistep-preserves-R {T} {t} {t′} (.t —→⟨ TM ⟩ M) Rt =
  multistep-preserves-R M (step-preserves-R TM Rt)

step-preserves-R' : ∀ {T t t′}
                  → ∅ ⊢ t ⦂ T → (t —→ t′) → R T t′ → R T t
step-preserves-R' {T = 𝟙}       {t} {t′} tp S (_ , h′)             =
  tp , step-preserves-halting S .snd h′
step-preserves-R' {T = T₁ ⇒ T₂} {t} {t′} tp S (_ , h′ , Ri)        =
  tp , step-preserves-halting S .snd h′ ,
    λ t″ R₁ → step-preserves-R' (tp ⊢· R-typable-empty R₁)
                                (ξ-·₁ S) (Ri t″ R₁)

multistep-preserves-R' : ∀ {T t t′}
                       → ∅ ⊢ t ⦂ T → (t —↠ t′) → R T t′ → R T t
multistep-preserves-R' {T} {t} {.t} tp (.t ∎ᵣ)         Rt = Rt
multistep-preserves-R' {T} {t} {t′} tp (.t —→⟨ TM ⟩ S) Rt =
  step-preserves-R' tp TM (multistep-preserves-R' (preserve tp TM) S Rt)

-- instantiations

data Inst : Tass → Env → 𝒰 where
  V-nil  : Inst [] []
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

instantiation-env-closed : ∀ {c e}
                         → Inst c e
                         → closed-env e
instantiation-env-closed {.[]}            {.[]}             V-nil                             = []
instantiation-env-closed {.((x , T) ∷ c)} {.((x , v) ∷ e)} (V-cons {x} {T} {v} {c} {e} V r i) =
  ∅⊢-closed (R-typable-empty r) ∷ instantiation-env-closed i

instantiation-R : ∀ {c e t T}
                → Inst c e
                → ∀ x
                → lup x c ＝ just T
                → lup x e ＝ just t
                → R T t
instantiation-R {.[]}            {.[]}                     V-nil                                 _ ec _  =
  absurd (nothing≠just ec)
instantiation-R {.((y , S) ∷ c)} {.((y , v) ∷ e)} {t} (V-cons {x = y} {T = S} {v} {c} {e} V r i) x ec ee with x ≟ y
... | yes prf = subst (λ q → R q t) (just-inj ec) (subst (R S) (just-inj ee) r)
... | no ctra = instantiation-R i x ec ee

instantiation-drop : ∀ {c e}
                   → Inst c e
                   → ∀ x → Inst (drp x c) (drp x e)
instantiation-drop {.[]}            {.[]}             V-nil                                 x = V-nil
instantiation-drop {.((y , T) ∷ c)} {.((y , v) ∷ e)} (V-cons {x = y} {T} {v} {c} {e} V r i) x with x ≟ y
... | yes prf = instantiation-drop i x
... | no ctra = V-cons V r (instantiation-drop i x)

-- The R Lemma

msubst-preserves-typing : ∀ {c e Γ t S}
                        → Inst c e
                        → mupdate c Γ ⊢ t ⦂ S
                        → Γ ⊢ msubst e t ⦂ S
msubst-preserves-typing {.[]}            {.[]}             V-nil                             ty = ty
msubst-preserves-typing {.((x , T) ∷ c)} {.((x , v) ∷ e)} (V-cons {x} {T} {v} {c} {e} V r i) ty =
  msubst-preserves-typing i (subst-ty (R-typable-empty r) ty)

msubst-R : ∀ {c e t T}
         → mupdate c ∅ ⊢ t ⦂ T
         → Inst c e
         → R T (msubst e t)
msubst-R {c} {e} {.𝓉𝓉}         {.𝟙}       ⊢𝓉𝓉                         i =
  let mu = sym $ msubst-unit e in
    subst (λ q → ∅ ⊢ q ⦂ 𝟙) mu ⊢𝓉𝓉
  , (subst halts mu $ value-halts V-𝓉𝓉)
msubst-R {c} {e} {.(` x)}      {T}       (⊢` {x} l)                       i =
  let lupc = mupdate-lookup l
      t′ , P = instantiation-domains-match i lupc
    in
  instantiation-R i x lupc
    (P ∙ ap just (sym (ap (extract (` x)) P)
                  ∙ sym (msubst-var (instantiation-env-closed i) x)))
msubst-R {c} {e} {.(ƛ x ⇒ N)} {.(A ⇒ B)} (⊢ƛ {x} {N} {A} {B} ⊢N)         i =
  let mabs = msubst-abs e x N
      WT : ∅ ⊢ ƛ x ⇒ msubst (drp x e) N ⦂ A ⇒ B
      WT = ⊢ƛ $ msubst-preserves-typing (instantiation-drop i x)
                                         (weaken (go c x A) ⊢N)
      in
    subst (λ q → ∅ ⊢ q ⦂ A ⇒ B) (sym mabs) WT
  , value-halts (subst Value (sym mabs) V-ƛ)
  , λ s Rs →
      let v , P , Q  = R-halts Rs
          Rv = multistep-preserves-R P Rs
       in
      subst (λ q → R B (q · s)) (sym mabs) $
      multistep-preserves-R'
        (WT ⊢· R-typable-empty Rs)
        (multistep-appr V-ƛ P
          —↠+
         subst (λ q → (ƛ x ⇒ msubst (drp x e) N) · v —→ q)
               (sym $ subst-msubst (∅⊢-closed (R-typable-empty Rv))
                                   (instantiation-env-closed i)
                                   x N)
               (β-ƛ Q))
        (msubst-R ⊢N (V-cons Q Rv i))
  where
  go : ∀ c x A → (mupdate c ∅ , x ⦂ A) ⊆ mupdate (drp x c) (∅ , x ⦂ A)
  go []            x A T i l = l
  go ((y , p) ∷ c) x A T i l with x ≟ y
  ... | yes prf = go c x A T i (⊆-shadow T i (subst (λ q → mupdate c ∅ , q ⦂ p , x ⦂ A ∋ i ⦂ T) (sym prf) l))
  go ((y , p) ∷ c) x A .A .x  here                     | no ctra = there ctra (go c x A A x here)
  go ((y , p) ∷ c) x A .p .y (there _    here)         | no ctra = here
  go ((y , p) ∷ c) x A  T  i (there i≠x (there i≠y l)) | no ctra = there i≠y (go c x A T i (there i≠x l))
msubst-R {c} {e} {.(L · M)}    {T}       (_⊢·_ {L} {M} {A} ⊢L ⊢M)        i =
  subst (R T) (sym (msubst-app e L M)) $
  msubst-R ⊢L i .snd .snd _ $
  msubst-R ⊢M i

normalization : ∀ {t T}
              → ∅ ⊢ t ⦂ T
              → halts t
normalization ⊢t = R-halts $ msubst-R ⊢t V-nil
