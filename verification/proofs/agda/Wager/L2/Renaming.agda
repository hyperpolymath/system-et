{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- DESIGN-CHOICES.adoc, DC-0.3: matches on typing derivations.
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- T0, renaming: a typing derivation is stable under a renaming of the
-- term variables. The usage vector moves along the renaming.
open import Wager.L1.Signature
open import Wager.Grade.Algebra
import Wager.L2.Signature

module Wager.L2.Renaming
  (S : Sig) (TS : Wager.L2.Signature.TSig S) (R : GradeAlgebra (Sig.TG S)) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.FinData.Base using (Fin; zero; suc)

open import Wager.L1.Syntax S using (Ty; ★; []; TG)
open GradeAlgebra R
open import Wager.L2.Typing S TS ops
open import Wager.L2.UsageLaws R

private
  variable
    n m : ℕ

-- Transport of a derivation along a path of usage vectors or of types.
castU : {γ γ' : Usage n} {Γ : Cx n} {t : Tm n} {A : Ty [] ★} →
        γ ≡ γ' → γ ▸ Γ ⊢ t ∶ A → γ' ▸ Γ ⊢ t ∶ A
castU {Γ = Γ} {t} {A} p d = subst (λ z → z ▸ Γ ⊢ t ∶ A) p d

castT : {γ : Usage n} {Γ : Cx n} {t : Tm n} {A B : Ty [] ★} →
        A ≡ B → γ ▸ Γ ⊢ t ∶ A → γ ▸ Γ ⊢ t ∶ B
castT {γ = γ} {Γ} {t} p d = subst (λ z → γ ▸ Γ ⊢ t ∶ z) p d

private
  liftM-unit : (ρ : Fin n → Fin m) → liftM (λ i → unit (ρ i)) ≡ (λ i → unit (extᵗ ρ i))
  liftM-unit ρ = funExt λ { zero → refl ; (suc i) → refl }

  -- The matrix of a renaming under one more binder.
  ⊛-ext : (γ : Usage n) (q : TG) (ρ : Fin n → Fin m) →
          (γ ▹ q) ⊛ (λ i → unit (extᵗ ρ i)) ≡ (γ ⊛ (λ i → unit (ρ i))) ▹ q
  ⊛-ext γ q ρ = cong ((γ ▹ q) ⊛_) (sym (liftM-unit ρ)) ∙ ⊛-lift γ q (λ i → unit (ρ i))

  ext-cx : {Γ : Cx n} {Δ : Cx m} {A : Ty [] ★} (ρ : Fin n → Fin m) →
           (∀ i → Δ (ρ i) ≡ Γ i) → ∀ i → (Δ ▹ᶜ A) (extᵗ ρ i) ≡ (Γ ▹ᶜ A) i
  ext-cx ρ h zero    = refl
  ext-cx ρ h (suc i) = h i

ren-typing : {γ : Usage n} {Γ : Cx n} {t : Tm n} {A : Ty [] ★} →
             γ ▸ Γ ⊢ t ∶ A →
             (ρ : Fin n → Fin m) (Δ : Cx m) → (∀ i → Δ (ρ i) ≡ Γ i) →
             (γ ⊛ (λ i → unit (ρ i))) ▸ Δ ⊢ renᵗ ρ t ∶ A
ren-typing (t-var i) ρ Δ h =
  castU (sym (⊛-unit i (λ i → unit (ρ i)))) (castT (h i) (t-var (ρ i)))
ren-typing (t-lam {γ = γ} {q = q} d) ρ Δ h =
  t-lam (castU (⊛-ext γ q ρ) (ren-typing d (extᵗ ρ) (Δ ▹ᶜ _) (ext-cx ρ h)))
ren-typing (t-app {γ = γ} {δ = δ} {q = q} d e) ρ Δ h =
  castU (sym (⊛-+ᵘ γ (q ·ᵘ δ) _ ∙ cong ((γ ⊛ _) +ᵘ_) (⊛-·ᵘ q δ _)))
        (t-app (ren-typing d ρ Δ h) (ren-typing e ρ Δ h))
ren-typing (t-pair {γ = γ} {δ = δ} d e) ρ Δ h =
  castU (sym (⊛-+ᵘ γ δ _)) (t-pair (ren-typing d ρ Δ h) (ren-typing e ρ Δ h))
ren-typing (t-letp {γ = γ} {δ = δ} d e) ρ Δ h =
  castU (sym (⊛-+ᵘ γ δ _))
    (t-letp (ren-typing d ρ Δ h)
       (castU (⊛-ext (δ ▹ 𝟙) 𝟙 (extᵗ ρ) ∙ cong (_▹ 𝟙) (⊛-ext δ 𝟙 ρ))
              (ren-typing e (extᵗ (extᵗ ρ)) (Δ ▹ᶜ _ ▹ᶜ _) (ext-cx (extᵗ ρ) (ext-cx ρ h)))))
ren-typing (t-inj₁ d) ρ Δ h = t-inj₁ (ren-typing d ρ Δ h)
ren-typing (t-inj₂ d) ρ Δ h = t-inj₂ (ren-typing d ρ Δ h)
ren-typing (t-case {γ = γ} {δ = δ} d l r) ρ Δ h =
  castU (sym (⊛-+ᵘ γ δ _))
    (t-case (ren-typing d ρ Δ h)
       (castU (⊛-ext δ 𝟙 ρ) (ren-typing l (extᵗ ρ) (Δ ▹ᶜ _) (ext-cx ρ h)))
       (castU (⊛-ext δ 𝟙 ρ) (ren-typing r (extᵗ ρ) (Δ ▹ᶜ _) (ext-cx ρ h))))
ren-typing (t-lit ℓ) ρ Δ h = castU (sym (⊛-zero (λ i → unit (ρ i)))) (t-lit ℓ)
ren-typing (t-step o d) ρ Δ h = t-step o (ren-typing d ρ Δ h)
ren-typing (t-conv d e) ρ Δ h = t-conv (ren-typing d ρ Δ h) e
ren-typing (t-sub d le) ρ Δ h = t-sub (ren-typing d ρ Δ h) (⊛-mono _ le)

-- Weakening: a new variable that the term does not use has the grade 𝟘.
weaken : {γ : Usage n} {Γ : Cx n} {t : Tm n} {A B : Ty [] ★} →
         γ ▸ Γ ⊢ t ∶ A → (γ ▹ 𝟘) ▸ (Γ ▹ᶜ B) ⊢ renᵗ suc t ∶ A
weaken {γ = γ} {Γ} {B = B} d = castU (⊛-wk γ) (ren-typing d suc (Γ ▹ᶜ B) (λ i → refl))
