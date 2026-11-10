{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- DESIGN-CHOICES.adoc, DC-0.3: matches on typed terms.
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- Erasure preserves typing (Stage 3).
--
-- In a signature that passes the role check, the erasure of a source
-- term of the type τ has the erased type `er τ`. The case of a cast is
-- the soundness of the roles: the two types of the coercion have one
-- erased type, so the erased term needs no change.
open import Wager.FC.Signature

module Wager.FC.Erasure (SS : SSig) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.FinData.Base using (Fin; zero; suc)

open import Wager.Role.Role
open import Wager.FC.Types SS
open import Wager.FC.Coercion SS
open import Wager.FC.Term SS
open import Wager.FC.RoleSoundness SS
open import Wager.Erased.Untyped
open Typing litTy

private
  variable
    n : ℕ

  -- A context of erased types that agrees with a source context.
  Agree : ECx n → SCx n → Type
  Agree Δ Γ = ∀ i → Δ i ≡ er (Γ i)

  agree-ext : ∀ {Δ : ECx n} {Γ : SCx n} τ → Agree Δ Γ → Agree (Δ ▹ᵉ er τ) (Γ ▹ˢ τ)
  agree-ext τ h zero    = refl
  agree-ext τ h (suc i) = h i

module _ (wr : WellRoled) where

  erase-typing′ : ∀ {Γ : SCx n} {τ} (e : STm Γ τ) (Δ : ECx n) → Agree Δ Γ →
                  Δ ⊢ᵉ eraseTm e ∶ er τ
  erase-typing′ (svar i)      Δ h = u-var i (h i)
  erase-typing′ (slam {τ = τ} b) Δ h =
    u-lam (erase-typing′ b (Δ ▹ᵉ er τ) (agree-ext τ h))
  erase-typing′ (sapp f a)    Δ h = u-app (erase-typing′ f Δ h) (erase-typing′ a Δ h)
  erase-typing′ (spair s t)   Δ h = u-pair (erase-typing′ s Δ h) (erase-typing′ t Δ h)
  erase-typing′ (sletp {τ = τ} {σ = σ} s b) Δ h =
    u-letp (erase-typing′ s Δ h)
           (erase-typing′ b (Δ ▹ᵉ er τ ▹ᵉ er σ) (agree-ext σ (agree-ext τ h)))
  erase-typing′ (sinl t)      Δ h = u-inl (erase-typing′ t Δ h)
  erase-typing′ (sinr t)      Δ h = u-inr (erase-typing′ t Δ h)
  erase-typing′ (scase {τ = τ} {σ = σ} s l r) Δ h =
    u-case (erase-typing′ s Δ h)
           (erase-typing′ l (Δ ▹ᵉ er τ) (agree-ext τ h))
           (erase-typing′ r (Δ ▹ᵉ er σ) (agree-ext σ h))
  erase-typing′ (slit ℓ)      Δ h = u-lit ℓ refl
  -- The cast vanished in the term. The type changes along the equality
  -- of the two erased types.
  erase-typing′ (cast γ e)    Δ h =
    subst (λ a → Δ ⊢ᵉ eraseTm e ∶ a) (rep-sound wr γ) (erase-typing′ e Δ h)

  erase-typing : ∀ {Γ : SCx n} {τ} (e : STm Γ τ) →
                 (λ i → er (Γ i)) ⊢ᵉ eraseTm e ∶ er τ
  erase-typing {Γ = Γ} e = erase-typing′ e (λ i → er (Γ i)) (λ i → refl)
