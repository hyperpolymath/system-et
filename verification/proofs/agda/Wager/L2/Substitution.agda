{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- DESIGN-CHOICES.adoc, DC-0.3: matches on typing derivations.
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- T0, graded substitution, for an arbitrary grade algebra.
--
-- The general lemma is for a parallel substitution σ with a usage
-- matrix Ψ: the row `Ψ i` is the usage vector of the term `σ i`.
-- The usage of the result is the vector-matrix product `γ ⊛ Ψ`.
open import Wager.L1.Signature
open import Wager.Grade.Algebra
import Wager.L2.Signature

module Wager.L2.Substitution
  (S : Sig) (TS : Wager.L2.Signature.TSig S) (R : GradeAlgebra (Sig.TG S)) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.FinData.Base using (Fin; zero; suc)

open import Wager.L1.Syntax S using (Ty; ★; []; TG)
open GradeAlgebra R
open import Wager.L2.Typing S TS ops
open import Wager.L2.UsageLaws R
open import Wager.L2.Renaming S TS R

private
  variable
    n m : ℕ

-- A substitution σ : Γ → Δ with the usage matrix Ψ.
SubTyping : (σ : Fin n → Tm m) (Ψ : Mat n m) (Γ : Cx n) (Δ : Cx m) → Type
SubTyping {n = n} σ Ψ Γ Δ = (i : Fin n) → Ψ i ▸ Δ ⊢ σ i ∶ Γ i

lift-typing : {σ : Fin n → Tm m} {Ψ : Mat n m} {Γ : Cx n} {Δ : Cx m} {A : Ty [] ★} →
              SubTyping σ Ψ Γ Δ → SubTyping (extsᵗ σ) (liftM Ψ) (Γ ▹ᶜ A) (Δ ▹ᶜ A)
lift-typing h zero    = t-var zero
lift-typing h (suc i) = weaken (h i)

sub-typing : {γ : Usage n} {Γ : Cx n} {t : Tm n} {A : Ty [] ★} →
             γ ▸ Γ ⊢ t ∶ A →
             (σ : Fin n → Tm m) (Ψ : Mat n m) (Δ : Cx m) → SubTyping σ Ψ Γ Δ →
             (γ ⊛ Ψ) ▸ Δ ⊢ subᵗ σ t ∶ A
sub-typing (t-var i) σ Ψ Δ h = castU (sym (⊛-unit i Ψ)) (h i)
sub-typing (t-lam {γ = γ} {q = q} d) σ Ψ Δ h =
  t-lam (castU (⊛-lift γ q Ψ) (sub-typing d (extsᵗ σ) (liftM Ψ) (Δ ▹ᶜ _) (lift-typing h)))
sub-typing (t-app {γ = γ} {δ = δ} {q = q} d e) σ Ψ Δ h =
  castU (sym (⊛-+ᵘ γ (q ·ᵘ δ) Ψ ∙ cong ((γ ⊛ Ψ) +ᵘ_) (⊛-·ᵘ q δ Ψ)))
        (t-app (sub-typing d σ Ψ Δ h) (sub-typing e σ Ψ Δ h))
sub-typing (t-pair {γ = γ} {δ = δ} d e) σ Ψ Δ h =
  castU (sym (⊛-+ᵘ γ δ Ψ)) (t-pair (sub-typing d σ Ψ Δ h) (sub-typing e σ Ψ Δ h))
sub-typing (t-letp {γ = γ} {δ = δ} d e) σ Ψ Δ h =
  castU (sym (⊛-+ᵘ γ δ Ψ))
    (t-letp (sub-typing d σ Ψ Δ h)
       (castU (⊛-lift (δ ▹ 𝟙) 𝟙 (liftM Ψ) ∙ cong (_▹ 𝟙) (⊛-lift δ 𝟙 Ψ))
              (sub-typing e (extsᵗ (extsᵗ σ)) (liftM (liftM Ψ)) (Δ ▹ᶜ _ ▹ᶜ _)
                          (lift-typing (lift-typing h)))))
sub-typing (t-inj₁ d) σ Ψ Δ h = t-inj₁ (sub-typing d σ Ψ Δ h)
sub-typing (t-inj₂ d) σ Ψ Δ h = t-inj₂ (sub-typing d σ Ψ Δ h)
sub-typing (t-case {γ = γ} {δ = δ} d l r) σ Ψ Δ h =
  castU (sym (⊛-+ᵘ γ δ Ψ))
    (t-case (sub-typing d σ Ψ Δ h)
       (castU (⊛-lift δ 𝟙 Ψ) (sub-typing l (extsᵗ σ) (liftM Ψ) (Δ ▹ᶜ _) (lift-typing h)))
       (castU (⊛-lift δ 𝟙 Ψ) (sub-typing r (extsᵗ σ) (liftM Ψ) (Δ ▹ᶜ _) (lift-typing h))))
sub-typing (t-lit ℓ) σ Ψ Δ h = castU (sym (⊛-zero Ψ)) (t-lit ℓ)
sub-typing (t-step o d) σ Ψ Δ h = t-step o (sub-typing d σ Ψ Δ h)
sub-typing (t-conv d e) σ Ψ Δ h = t-conv (sub-typing d σ Ψ Δ h) e
sub-typing (t-sub d le) σ Ψ Δ h = t-sub (sub-typing d σ Ψ Δ h) (⊛-mono Ψ le)

-- Substitution of the top variable (the statement T0-Substitution).
subst-lemma : {γ δ : Usage n} {Γ : Cx n} {q : TG} {A B : Ty [] ★}
              {t : Tm (suc n)} {u : Tm n} →
              (γ ▹ q) ▸ (Γ ▹ᶜ A) ⊢ t ∶ B →
              δ ▸ Γ ⊢ u ∶ A →
              (γ +ᵘ (q ·ᵘ δ)) ▸ Γ ⊢ t [ u ]ᵗ ∶ B
subst-lemma {γ = γ} {δ} {Γ} {q} {u = u} d e =
  castU (cong ((q ·ᵘ δ) +ᵘ_) (⊛-id γ) ∙ +ᵘ-comm (q ·ᵘ δ) γ)
        (sub-typing d (u ∷ᵗ tvar) (δ ∷ᵐ unit) Γ (λ { zero → e ; (suc i) → t-var i }))

-- Substitution of the top two variables (for pairs).
subst-lemma₂ : {γ δ₁ δ₂ : Usage n} {Γ : Cx n} {p q : TG} {A B C : Ty [] ★}
               {t : Tm (suc (suc n))} {u₁ u₂ : Tm n} →
               (γ ▹ p ▹ q) ▸ (Γ ▹ᶜ A ▹ᶜ B) ⊢ t ∶ C →
               δ₁ ▸ Γ ⊢ u₁ ∶ A →
               δ₂ ▸ Γ ⊢ u₂ ∶ B →
               ((q ·ᵘ δ₂) +ᵘ ((p ·ᵘ δ₁) +ᵘ γ)) ▸ Γ ⊢ t [ u₁ & u₂ ]ᵗ ∶ C
subst-lemma₂ {γ = γ} {δ₁} {δ₂} {Γ} {p} {q} {u₁ = u₁} {u₂} d e₁ e₂ =
  castU (cong (λ z → (q ·ᵘ δ₂) +ᵘ ((p ·ᵘ δ₁) +ᵘ z)) (⊛-id γ))
        (sub-typing d (u₂ ∷ᵗ u₁ ∷ᵗ tvar) (δ₂ ∷ᵐ δ₁ ∷ᵐ unit) Γ
           (λ { zero → e₂ ; (suc zero) → e₁ ; (suc (suc i)) → t-var i }))
