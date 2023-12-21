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
             → ▹map (mapᵖ (val≤ η)) (beta t ρ v) ＝ beta t (env≤ η ρ) (val≤ η v)
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

mutual
  readback≤-body : ▹ (∀ Γ Δ A → (η : Δ ≤ Γ) (v : Val Γ A) → mapᵖ (nf≤ η) (readback v) ＝ readback (val≤ η v))
                 → ∀ Γ Δ A → (η : Δ ≤ Γ) (v : Val Γ A) → mapᵖ (nf≤ η) (readback v) ＝ readback (val≤ η v)
  readback≤-body r▹ Γ Δ  𝟙      η (v-ne n) =
    mapᵖ (nf≤ η) (readback (v-ne n))
      ＝⟨⟩
    mapᵖ (nf≤ η) (mapᵖ nf-ne (nereadback n))
      ＝⟨ mapᵖ-comp (nereadback n) ⟩
    mapᵖ (nf≤ η ∘ nf-ne) (nereadback n)
      ＝⟨⟩
    mapᵖ (nf-ne ∘ nen≤ η) (nereadback n)
      ＝⟨ sym (mapᵖ-comp (nereadback n) ) ⟩
    mapᵖ nf-ne (mapᵖ (nen≤ η) (nereadback n))
      ＝⟨ ap (mapᵖ nf-ne) (nereadback≤-body η n r▹) ⟩
    mapᵖ nf-ne (nereadback (nev≤ η n))
      ＝⟨⟩
    readback (v-ne (nev≤ η n))
      ∎
  readback≤-body r▹ Γ Δ (A ⇒ B) η  v       =
    mapᵖ (nf≤ η) (readback v)
      ＝⟨⟩
    mapᵖ (nf≤ η) (mapᵖ nf-ƛ (eta v))
      ＝⟨ mapᵖ-comp (eta v) ⟩
    mapᵖ (nf≤ η ∘ nf-ƛ) (eta v)
      ＝⟨⟩
    mapᵖ (nf-ƛ ∘ nf≤ (lift≤ η)) (eta v)
      ＝⟨ sym (mapᵖ-comp (eta v)) ⟩
    mapᵖ nf-ƛ (mapᵖ (nf≤ (lift≤ η)) (eta v))
      ＝⟨ ap (mapᵖ nf-ƛ) (eta≤-body η v r▹) ⟩
    mapᵖ nf-ƛ (eta (val≤ η v))
      ＝⟨⟩
    readback (val≤ η v)
      ∎

  nereadback≤-body : ∀ {Γ Δ A} (η : Δ ≤ Γ) (t : Ne Val Γ A)
                   → ▹ (∀ Γ Δ A → (η : Δ ≤ Γ) (v : Val Γ A) → mapᵖ (nf≤ η) (readback v) ＝ readback (val≤ η v))
                   → mapᵖ (nen≤ η) (nereadback t) ＝ nereadback (nev≤ η t)
  nereadback≤-body         η (ne-` x)       r▹ = refl
  nereadback≤-body {Γ} {Δ} η (ne-· {A} n v) r▹ =
    mapᵖ (nen≤ η) (nereadback (ne-· n v))
      ＝⟨⟩
    mapᵖ (nen≤ η) (nereadback n >>=ᵖ λ m → mapᵖ (ne-· m) (readback v))
      ＝⟨ sym (bind-map (nereadback n >>=ᵖ λ m → mapᵖ (ne-· m) (readback v))) ⟩
    (nereadback n >>=ᵖ λ m → mapᵖ (ne-· m) (readback v)) >>=ᵖ (now ∘ nen≤ η)
      ＝⟨ bind-assoc (nereadback n) ⟩
    (nereadback n >>=ᵖ λ m → mapᵖ (ne-· m) (readback v) >>=ᵖ (now ∘ nen≤ η))
      ＝⟨ ap (nereadback n >>=ᵖ_)
            (fun-ext λ m → bind-map (mapᵖ (ne-· m) (readback v))) ⟩
    (nereadback n >>=ᵖ λ m → mapᵖ (nen≤ η) (mapᵖ (ne-· m) (readback v)))
      ＝⟨ ap (nereadback n >>=ᵖ_)
            (fun-ext λ m → mapᵖ-comp (readback v) ) ⟩
    (nereadback n >>=ᵖ λ m → mapᵖ (nen≤ η ∘ ne-· m) (readback v))
      ＝⟨⟩
    (nereadback n >>=ᵖ λ m → mapᵖ (ne-· (nen≤ η m) ∘ nf≤ η) (readback v))
      ＝⟨ ap (nereadback n >>=ᵖ_)
            (fun-ext λ m → sym (mapᵖ-comp (readback v))) ⟩
    (nereadback n >>=ᵖ λ m → mapᵖ (ne-· (nen≤ η m)) (mapᵖ (nf≤ η) (readback v)))
      ＝⟨ sym (bind-assoc (nereadback n)) ⟩
    ((nereadback n >>=ᵖ (now ∘ nen≤ η)) >>=ᵖ λ m → mapᵖ (ne-· m) (mapᵖ (nf≤ η) (readback v)))
      ＝⟨ ap (_>>=ᵖ (λ m → mapᵖ (ne-· m) (mapᵖ (nf≤ η) (readback v)))) (bind-map (nereadback n)) ⟩
    (mapᵖ (nen≤ η) (nereadback n) >>=ᵖ λ m → mapᵖ (ne-· m) (mapᵖ (nf≤ η) (readback v)))
      ＝⟨ ap (mapᵖ (nen≤ η) (nereadback n) >>=ᵖ_)
            (fun-ext λ m → ap (mapᵖ (ne-· m)) (readback≤-body r▹ Γ Δ A η v)) ⟩
    (mapᵖ (nen≤ η) (nereadback n) >>=ᵖ λ m → mapᵖ (ne-· m) (readback (val≤ η v)))
      ＝⟨ ap (_>>=ᵖ (λ m → mapᵖ (ne-· m) (readback (val≤ η v)))) (nereadback≤-body η n r▹) ⟩
    (nereadback (nev≤ η n) >>=ᵖ λ m → mapᵖ (ne-· m) (readback (val≤ η v)))
      ＝⟨⟩
    nereadback (ne-· (nev≤ η n) (val≤ η v))
      ∎

  eta≤-body : ∀ {Γ Δ A B} (η : Δ ≤ Γ) (v : Val Γ (A ⇒ B))
            → ▹ (∀ Γ Δ A → (η : Δ ≤ Γ) (v : Val Γ A) → mapᵖ (nf≤ η) (readback v) ＝ readback (val≤ η v))
            → mapᵖ (nf≤ (lift≤ η)) (eta v) ＝ eta (val≤ η v)
  eta≤-body {Γ} {Δ} {A} {B} η v r▹ =
    mapᵖ (nf≤ (lift≤ η)) (eta v)
      ＝⟨⟩
    mapᵖ (nf≤ (lift≤ η)) (apply (weakVal v) (v-ne (ne-` here)) >>=ᵖ λ w → later (dfix readback-body ⊛ next (Γ ﹐ A) ⊛ next B ⊛ next w))
      ＝⟨ sym (bind-map (apply (val≤ wk v) (v-ne (ne-` here)) >>=ᵖ λ w → later (dfix readback-body ⊛ next (Γ ﹐ A) ⊛ next B ⊛ next w))) ⟩
    ((apply (val≤ wk v) (v-ne (ne-` here)) >>=ᵖ λ w → later (dfix readback-body ⊛ next (Γ ﹐ A) ⊛ next B ⊛ next w)) >>=ᵖ (now ∘ nf≤ (lift≤ η)))
      ＝⟨ bind-assoc (apply (val≤ wk v) (v-ne (ne-` here))) ⟩
    (apply (val≤ wk v) (v-ne (ne-` here)) >>=ᵖ λ w → later (dfix readback-body ⊛ next (Γ ﹐ A) ⊛ next B ⊛ next w) >>=ᵖ (now ∘ nf≤ (lift≤ η)))
      ＝⟨ ap (apply (val≤ wk v) (v-ne (ne-` here)) >>=ᵖ_) (fun-ext λ w → bind-map (later (dfix readback-body ⊛ next (Γ ﹐ A) ⊛ next B ⊛ next w))) ⟩
    (apply (val≤ wk v) (v-ne (ne-` here)) >>=ᵖ λ w → mapᵖ (nf≤ (lift≤ η)) (later (dfix readback-body ⊛ next (Γ ﹐ A) ⊛ next B ⊛ next w)))
      ＝⟨⟩
    (apply (val≤ wk v) (v-ne (ne-` here)) >>=ᵖ λ w → later λ α → mapᵖ (nf≤ (lift≤ η)) (dfix readback-body α (Γ ﹐ A) B w))
      ＝⟨ ap (apply (val≤ wk v) (v-ne (ne-` here)) >>=ᵖ_)
            (fun-ext λ w → ap later (▹-ext λ α i → mapᵖ (nf≤ (lift≤ η)) (pfix readback-body i α (Γ ﹐ A) B w))) ⟩
    (apply (val≤ wk v) (v-ne (ne-` here)) >>=ᵖ λ w → later (next (mapᵖ (nf≤ (lift≤ η)) (readback w))))
      ＝⟨ ap (apply (val≤ wk v) (v-ne (ne-` here)) >>=ᵖ_)
            (fun-ext λ w → ap later (▹-ext λ α → r▹ α (Γ ﹐ A) (Δ ﹐ A) B (lift≤ η) w )) ⟩
    (apply (val≤ wk v) (v-ne (ne-` here)) >>=ᵖ λ w → later (next (readback (val≤ (lift≤ η) w))))
      ＝⟨ ap (apply (val≤ wk v) (v-ne (ne-` here)) >>=ᵖ_)
            (fun-ext λ w → ap later (▹-ext λ α i → pfix readback-body (~ i) α (Δ ﹐ A) B (val≤ (lift≤ η) w))) ⟩
    (apply (val≤ wk v) (v-ne (ne-` here)) >>=ᵖ λ w → later (dfix readback-body ⊛ next (Δ ﹐ A) ⊛ next B ⊛ next (val≤ (lift≤ η) w)))
      ＝⟨⟩
    (apply (val≤ wk v) (v-ne (ne-` here)) >>=ᵖ (λ z → now (val≤ (lift≤ η) z) >>=ᵖ (λ w → later (dfix readback-body ⊛ next (Δ ﹐ A) ⊛ next B ⊛ next w))))
      ＝⟨ sym (bind-assoc (apply (val≤ wk v) (v-ne (ne-` here)))) ⟩
    ((apply (weakVal v) (v-ne (ne-` here)) >>=ᵖ (now ∘ val≤ (lift≤ η))) >>=ᵖ λ w → later (dfix readback-body ⊛ next (Δ ﹐ A) ⊛ next B ⊛ next w))
      ＝⟨ ap (_>>=ᵖ λ w → later (dfix readback-body ⊛ next (Δ ﹐ A) ⊛ next B ⊛ next w))
            (bind-map (apply (weakVal v) (v-ne (ne-` here)))) ⟩
    mapᵖ (val≤ (lift≤ η)) (apply (weakVal v) (v-ne (ne-` here))) >>=ᵖ (λ w → later (dfix readback-body ⊛ next (Δ ﹐ A) ⊛ next B ⊛ next w))
      ＝⟨ ap (_>>=ᵖ λ w → later (dfix readback-body ⊛ next (Δ ﹐ A) ⊛ next B ⊛ next w))
            (apply≤ (weakVal v) (v-ne (ne-` here)) (lift≤ η)) ⟩
    (apply (val≤ (lift≤ η) (val≤ wk v)) (v-ne (ne-` here)) >>=ᵖ λ w → later (dfix readback-body ⊛ next (Δ ﹐ A) ⊛ next B ⊛ next w))
      ＝⟨ ap (λ q → apply q (v-ne (ne-` here)) >>=ᵖ λ w → later (dfix readback-body ⊛ next (Δ ﹐ A) ⊛ next B ⊛ next w))
             (val≤-● (lift≤ η) wk v) ⟩
    (apply (val≤ (weak≤ (η ● id≤)) v) (v-ne (ne-` here)) >>=ᵖ λ w → later (dfix readback-body ⊛ next (Δ ﹐ A) ⊛ next B ⊛ next w))
      ＝⟨ ap (λ q → apply (val≤ (weak≤ q) v) (v-ne (ne-` here)) >>=ᵖ λ w → later (dfix readback-body ⊛ next (Δ ﹐ A) ⊛ next B ⊛ next w))
             (η●id η) ⟩
    (apply (val≤ (weak≤ η) v) (v-ne (ne-` here)) >>=ᵖ λ w → later (dfix readback-body ⊛ next (Δ ﹐ A) ⊛ next B ⊛ next w))
      ＝⟨ ap (λ q → apply q (v-ne (ne-` here)) >>=ᵖ λ w → later (dfix readback-body ⊛ next (Δ ﹐ A) ⊛ next B ⊛ next w))
             (sym (val≤-● wk η v)) ⟩
    (apply (weakVal (val≤ η v)) (v-ne (ne-` here)) >>=ᵖ λ w → later (dfix readback-body ⊛ next (Δ ﹐ A) ⊛ next B ⊛ next w))
     ＝⟨⟩
    eta (val≤ η v)
      ∎

readback≤ : ∀ {Γ Δ} A (η : Δ ≤ Γ) (v : Val Γ A)
          → mapᵖ (nf≤ η) (readback v) ＝ readback (val≤ η v)
readback≤ {Γ} {Δ} = fix readback≤-body Γ Δ

nereadback≤ : ∀ {Γ Δ A} (η : Δ ≤ Γ) (t : Ne Val Γ A)
            → mapᵖ (nen≤ η) (nereadback t) ＝ nereadback (nev≤ η t)
nereadback≤ η t = nereadback≤-body η t (dfix readback≤-body)

nereadback≤⇓ : ∀ {Γ Δ A} (η : Δ ≤ Γ) (t : Ne Val Γ A) {n : Ne Nf Γ A}
             → nereadback t ⇓ᵖ n → nereadback (nev≤ η t) ⇓ᵖ nen≤ η n
nereadback≤⇓ η t {n} p = subst (λ q → q ⇓ᵖ nen≤ η n) (nereadback≤ η t) (map⇓ (nen≤ η) p)

mutual
  V⟦⟧≤ : ∀ {Δ Η} A (η : Η ≤ Δ) (v : Val Δ A)
       → V⟦ A ⟧ v → V⟦ A ⟧ (val≤ η v)
  V⟦⟧≤  𝟙      η (v-ne t) (n , p)        = nen≤ η n , (nereadback≤⇓ η t p)
  V⟦⟧≤ (A ⇒ B) η  v        p      ζ u u⇓ =
    let v′ , av⇓ , p″ = p (ζ ● η) u u⇓ in
        v′ , subst (λ q → apply q u ⇓ᵖ v′)
                   (sym (val≤-● ζ η v))
                   av⇓
           , p″

  E⟦⟧≤ : ∀ {Γ Δ Η} (η : Η ≤ Δ) (ρ : Env Δ Γ)
       → E⟦ Γ ⟧ ρ → E⟦ Γ ⟧ (env≤ η ρ)
  E⟦⟧≤ η  ε       θ      = tt
  E⟦⟧≤ η (ρ 、 x) (θ , v) = E⟦⟧≤ η ρ θ , V⟦⟧≤ _ η x v
