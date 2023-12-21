{-# OPTIONS --guarded #-}
module STLC.Int.NbE.Terminate where

open import Prelude hiding (apply)
open import Data.Unit
open import Later
open import Guarded.Partial
open import Guarded.Partial.Converges

open import STLC.Ty
open import STLC.Int.TyTerm
open import STLC.Int.NbE.OPE
open import STLC.Int.NbE.Norm

mutual
  V⟦_⟧ : ∀ {Γ} → (A : Ty) → Val Γ A → 𝒰
  V⟦ 𝟙 ⟧           (v-ne w) = nereadback w ⇓
  V⟦_⟧ {Γ} (A ⇒ B)  f       = ∀ {Δ} (η : Δ ≤ Γ) (u : Val Δ A) → V⟦ A ⟧ u → C⟦ B ⟧ (apply (val≤ η f) u)

  C⟦_⟧ : ∀ {Γ} → (A : Ty) → Part (Val Γ A) → 𝒰
  C⟦_⟧ {Γ} A p = Σ[ v ꞉ Val Γ A ] (p ⇓ᵖ v) × V⟦ A ⟧ v

E⟦_⟧ : ∀ {Δ} Γ → Env Δ Γ → 𝒰
E⟦ ∅ ⟧      ε       = ⊤
E⟦ Γ ﹐ A ⟧ (e 、 v) = E⟦ Γ ⟧ e × V⟦ A ⟧ v

mutual
  val≤-id : ∀ {Δ A} → (v : Val Δ A) → val≤ id≤ v ＝ v
  val≤-id (v-ƛ t e) = ap (v-ƛ t) (env≤-id e)
  val≤-id (v-ne n)  = ap v-ne (nev≤-id n)

  env≤-id : ∀ {Γ Δ} → (ρ : Env Δ Γ) → env≤ id≤ ρ ＝ ρ
  env≤-id  ε       = refl
  env≤-id (ρ 、 v) = ap² _、_ (env≤-id ρ) (val≤-id v)

  nev≤-id : ∀ {Δ A} → (t : Ne Val Δ A) → nev≤ id≤ t ＝ t
  nev≤-id (ne-` x)   = refl
  nev≤-id (ne-· n v) = ap² ne-· (nev≤-id n) (val≤-id v)

var≤-● : ∀ {Γ Δ Η A}
       → (η : Γ ≤ Δ) (θ : Δ ≤ Η) (x : Η ∋ A)
       → var≤ η (var≤ θ x) ＝ var≤ (η ● θ) x
var≤-●  id≤       θ         x        = refl
var≤-● (weak≤ η)  θ         x        = ap there (var≤-● η θ x)
var≤-● (lift≤ η)  id≤       x        = refl
var≤-● (lift≤ η) (weak≤ θ)  x        = ap there (var≤-● η θ x)
var≤-● (lift≤ η) (lift≤ θ)  here     = refl
var≤-● (lift≤ η) (lift≤ θ) (there x) = ap there (var≤-● η θ x)

mutual
  val≤-● : ∀ {Γ Δ Η A}
         → (η : Γ ≤ Δ) (θ : Δ ≤ Η) (v : Val Η A)
         → val≤ η (val≤ θ v) ＝ val≤ (η ● θ) v
  val≤-● η θ (v-ƛ t e) = ap (v-ƛ t) (env≤-● η θ e)
  val≤-● η θ (v-ne n)  = ap v-ne (nev≤-● η θ n)

  env≤-● : ∀ {Γ Δ Η Ξ}
         → (η : Γ ≤ Δ) (θ : Δ ≤ Η) (ρ : Env Η Ξ)
         → env≤ η (env≤ θ ρ) ＝ env≤ (η ● θ) ρ
  env≤-● η θ  ε       = refl
  env≤-● η θ (ρ 、 v) = ap² _、_ (env≤-● η θ ρ) (val≤-● η θ v)

  nev≤-● : ∀ {Γ Δ Η A}
         → (η : Γ ≤ Δ) (θ : Δ ≤ Η) (t : Ne Val Η A)
         → nev≤ η (nev≤ θ t) ＝ nev≤ (η ● θ) t
  nev≤-● η θ (ne-` x)   = ap ne-` (var≤-● η θ x)
  nev≤-● η θ (ne-· n v) = ap² ne-· (nev≤-● η θ n) (val≤-● η θ v)

lookup≤ : ∀ {Γ Δ Η A} (x : Γ ∋ A) (ρ : Env Δ Γ) (η : Η ≤ Δ)
        → val≤ η (lookup x ρ) ＝ lookup x (env≤ η ρ)
lookup≤ here      (ρ 、 v) η = refl
lookup≤ (there x) (ρ 、 v) η = lookup≤ x ρ η

mutual
  eval≤-body : ▹ (∀ Γ Δ Η A → (t : Γ ⊢ A) (ρ : Env Δ Γ) (η : Η ≤ Δ) → mapᵖ (val≤ η) (eval t ρ) ＝ eval t (env≤ η ρ))
             → ∀ Γ Δ Η A → (t : Γ ⊢ A) (ρ : Env Δ Γ) (η : Η ≤ Δ) → mapᵖ (val≤ η) (eval t ρ) ＝ eval t (env≤ η ρ)
  eval≤-body e▹ Γ Δ Η A        (` x)   ρ η = ap now (lookup≤ x ρ η)
  eval≤-body e▹ Γ Δ Η .(_ ⇒ _) (ƛ M)   ρ η = refl
  eval≤-body e▹ Γ Δ Η A        (M · N) ρ η =
    mapᵖ (val≤ η) (eval (M · N) ρ)
      ＝⟨⟩
    mapᵖ (val≤ η) (eval M ρ >>=ᵖ λ f → eval N ρ >>=ᵖ λ v → apply f v)
      ＝⟨ sym (bind-map (eval M ρ >>=ᵖ λ f → eval N ρ >>=ᵖ λ v → apply f v)) ⟩
    (eval M ρ >>=ᵖ λ f → eval N ρ >>=ᵖ λ v → apply f v) >>=ᵖ (now ∘ val≤ η)
      ＝⟨ bind-assoc (eval M ρ) ⟩
    (eval M ρ >>=ᵖ λ f → (eval N ρ >>=ᵖ λ v → apply f v) >>=ᵖ (now ∘ val≤ η))
      ＝⟨ ap (eval M ρ >>=ᵖ_) (fun-ext λ f → bind-assoc (eval N ρ)) ⟩
    (eval M ρ >>=ᵖ λ f → eval N ρ >>=ᵖ λ x → apply f x >>=ᵖ (now ∘ val≤ η))
      ＝⟨ ap (eval M ρ >>=ᵖ_) (fun-ext λ f → ap (eval N ρ >>=ᵖ_) (fun-ext λ x → bind-map (apply f x))) ⟩
    (eval M ρ >>=ᵖ λ f → eval N ρ >>=ᵖ λ x → mapᵖ (val≤ η) (apply f x))
      ＝⟨ ap (eval M ρ >>=ᵖ_) (fun-ext λ f → ap (eval N ρ >>=ᵖ_) (fun-ext λ x → apply≤-body f x η e▹)) ⟩
    (eval M ρ >>=ᵖ λ f → eval N ρ >>=ᵖ λ x → apply (val≤ η f) (val≤ η x))
      ＝⟨⟩
    (eval M ρ >>=ᵖ λ f → eval N ρ >>=ᵖ λ x → now (val≤ η x) >>=ᵖ λ v → apply (val≤ η f) v)
      ＝⟨ ap (eval M ρ >>=ᵖ_) (fun-ext λ f → sym (bind-assoc (eval N ρ))) ⟩
    (eval M ρ >>=ᵖ λ f → (eval N ρ >>=ᵖ λ x → now (val≤ η x)) >>=ᵖ λ v → apply (val≤ η f) v)
      ＝⟨ ap (eval M ρ >>=ᵖ_) (fun-ext λ f → ap (_>>=ᵖ (λ v → apply (val≤ η f) v)) (bind-map (eval N ρ))) ⟩
    (eval M ρ >>=ᵖ λ f → (mapᵖ (val≤ η) (eval N ρ)) >>=ᵖ λ v → apply (val≤ η f) v)
      ＝⟨ ap (eval M ρ >>=ᵖ_) (fun-ext λ f → ap (_>>=ᵖ (λ v → apply (val≤ η f) v)) (eval≤-body e▹ Γ Δ Η _ N ρ η)) ⟩
    (eval M ρ >>=ᵖ λ f → eval N (env≤ η ρ) >>=ᵖ λ v → apply (val≤ η f) v)
      ＝⟨⟩
    (eval M ρ >>=ᵖ λ f → now (val≤ η f) >>=ᵖ λ f′ → eval N (env≤ η ρ) >>=ᵖ λ v → apply f′ v)
      ＝⟨ sym (bind-assoc (eval M ρ)) ⟩
    ((eval M ρ >>=ᵖ λ f → now (val≤ η f)) >>=ᵖ λ f′ → eval N (env≤ η ρ) >>=ᵖ λ v → apply f′ v)
      ＝⟨ ap (_>>=ᵖ (λ f′ → eval N (env≤ η ρ) >>=ᵖ λ v → apply f′ v)) (bind-map (eval M ρ)) ⟩
    (mapᵖ (val≤ η) (eval M ρ) >>=ᵖ λ f → eval N (env≤ η ρ) >>=ᵖ λ v → apply f v)
      ＝⟨ ap (_>>=ᵖ (λ f′ → eval N (env≤ η ρ) >>=ᵖ λ v → apply f′ v)) (eval≤-body e▹ Γ Δ Η (_ ⇒ A) M ρ η) ⟩
    (eval M (env≤ η ρ) >>=ᵖ λ f → eval N (env≤ η ρ) >>=ᵖ λ v → apply f v)
      ＝⟨⟩
    eval (M · N) (env≤ η ρ)
      ∎

  apply≤-body : ∀ {Γ Δ A B} (f : Val Γ (A ⇒ B)) (v : Val Γ A) (η : Δ ≤ Γ)
              → ▹ (∀ Γ Δ Η A → (t : Γ ⊢ A) (ρ : Env Δ Γ) (η : Η ≤ Δ) → mapᵖ (val≤ η) (eval t ρ) ＝ eval t (env≤ η ρ))
              → mapᵖ (val≤ η) (apply f v) ＝ apply (val≤ η f) (val≤ η v)
  apply≤-body (v-ƛ t e) v η e▹ = ap later (beta≤-body t e v η e▹)
  apply≤-body (v-ne n)  v η e▹ = refl

  beta≤-body : ∀ {Γ Δ Η A B} (t : (Γ ﹐ A) ⊢ B)(ρ : Env Δ Γ) (v : Val Δ A) (η : Η ≤ Δ)
             → ▹ (∀ Γ Δ Η A → (t : Γ ⊢ A) (ρ : Env Δ Γ) (η : Η ≤ Δ) → mapᵖ (val≤ η) (eval t ρ) ＝ eval t (env≤ η ρ))
             → (▹map (mapᵖ (val≤ η)) (beta t ρ v)) ＝ beta t (env≤ η ρ) (val≤ η v)
  beta≤-body {Γ} {Δ} {Η} {A} {B} t ρ v η e▹ = ▹-ext λ α →
    ap (mapᵖ (val≤ η)) (λ i → pfix eval-body i α (Γ ﹐ A) Δ B t (ρ 、 v))
    ∙ e▹ α (Γ ﹐ A) Δ Η B t (ρ 、 v) η
    ∙ λ i → pfix eval-body (~ i) α (Γ ﹐ A) Η B t (env≤ η ρ 、 val≤ η v)

-- TODO unused?
eval≤ : ∀ {Γ Δ Η A} (t : Γ ⊢ A) (ρ : Env Δ Γ) (η : Η ≤ Δ)
      → mapᵖ (val≤ η) (eval t ρ) ＝ eval t (env≤ η ρ)
eval≤ {Γ} {Δ} {Η} {A} = fix eval≤-body Γ Δ Η A

apply≤ : ∀ {Γ Δ A B} (f : Val Γ (A ⇒ B)) (v : Val Γ A) (η : Δ ≤ Γ)
       → mapᵖ (val≤ η) (apply f v) ＝ apply (val≤ η f) (val≤ η v)
apply≤ f v η = apply≤-body f v η (dfix eval≤-body)
