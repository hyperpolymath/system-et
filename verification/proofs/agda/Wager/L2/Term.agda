{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- DESIGN-CHOICES.adoc, DC-0.3: matches on scoped terms.
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- L2 terms: a graded λ-calculus with pairs, sums, literals and trope
-- transitions. Terms are scoped (de Bruijn) and not typed. The types
-- in terms are closed L1 types of kind ★.
--
-- The kernel `anytype` has no `if`. This calculus has sums and `case`,
-- as the task asks.
open import Wager.L1.Signature
import Wager.L2.Signature

module Wager.L2.Term (S : Sig) (TS : Wager.L2.Signature.TSig S) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.FinData.Base using (Fin; zero; suc)

open import Wager.L1.Syntax S
open Wager.L2.Signature S public
open TSig TS public

private
  variable
    n m : ℕ

data Tm : ℕ → Type where
  tvar : Fin n → Tm n
  -- The binder has its declared grade and its type.
  tlam : TG → Ty [] ★ → Tm (suc n) → Tm n
  tapp : Tm n → Tm n → Tm n
  pair : Tm n → Tm n → Tm n
  -- The body sees the first component at index 1 and the second at index 0.
  letp : Tm n → Tm (suc (suc n)) → Tm n
  inj₁ : Tm n → Tm n
  inj₂ : Tm n → Tm n
  case : Tm n → Tm (suc n) → Tm (suc n) → Tm n
  lit  : Lit → Tm n
  -- A trope transition.
  step : Op → Tm n → Tm n

------------------------------------------------------------------------
-- Renaming and substitution.

extᵗ : (Fin n → Fin m) → Fin (suc n) → Fin (suc m)
extᵗ ρ zero    = zero
extᵗ ρ (suc i) = suc (ρ i)

renᵗ : (Fin n → Fin m) → Tm n → Tm m
renᵗ ρ (tvar i)     = tvar (ρ i)
renᵗ ρ (tlam q A b) = tlam q A (renᵗ (extᵗ ρ) b)
renᵗ ρ (tapp f a)   = tapp (renᵗ ρ f) (renᵗ ρ a)
renᵗ ρ (pair s t)   = pair (renᵗ ρ s) (renᵗ ρ t)
renᵗ ρ (letp s b)   = letp (renᵗ ρ s) (renᵗ (extᵗ (extᵗ ρ)) b)
renᵗ ρ (inj₁ t)     = inj₁ (renᵗ ρ t)
renᵗ ρ (inj₂ t)     = inj₂ (renᵗ ρ t)
renᵗ ρ (case s l r) = case (renᵗ ρ s) (renᵗ (extᵗ ρ) l) (renᵗ (extᵗ ρ) r)
renᵗ ρ (lit ℓ)      = lit ℓ
renᵗ ρ (step o t)   = step o (renᵗ ρ t)

extsᵗ : (Fin n → Tm m) → Fin (suc n) → Tm (suc m)
extsᵗ σ zero    = tvar zero
extsᵗ σ (suc i) = renᵗ suc (σ i)

subᵗ : (Fin n → Tm m) → Tm n → Tm m
subᵗ σ (tvar i)     = σ i
subᵗ σ (tlam q A b) = tlam q A (subᵗ (extsᵗ σ) b)
subᵗ σ (tapp f a)   = tapp (subᵗ σ f) (subᵗ σ a)
subᵗ σ (pair s t)   = pair (subᵗ σ s) (subᵗ σ t)
subᵗ σ (letp s b)   = letp (subᵗ σ s) (subᵗ (extsᵗ (extsᵗ σ)) b)
subᵗ σ (inj₁ t)     = inj₁ (subᵗ σ t)
subᵗ σ (inj₂ t)     = inj₂ (subᵗ σ t)
subᵗ σ (case s l r) = case (subᵗ σ s) (subᵗ (extsᵗ σ) l) (subᵗ (extsᵗ σ) r)
subᵗ σ (lit ℓ)      = lit ℓ
subᵗ σ (step o t)   = step o (subᵗ σ t)

infixr 5 _∷ᵗ_
_∷ᵗ_ : Tm m → (Fin n → Tm m) → Fin (suc n) → Tm m
(u ∷ᵗ σ) zero    = u
(u ∷ᵗ σ) (suc i) = σ i

-- Substitution of the top variable.
infix 25 _[_]ᵗ _[_&_]ᵗ
_[_]ᵗ : Tm (suc n) → Tm n → Tm n
b [ u ]ᵗ = subᵗ (u ∷ᵗ tvar) b

-- Substitution of the top two variables: v₁ for index 1, v₂ for index 0.
_[_&_]ᵗ : Tm (suc (suc n)) → Tm n → Tm n → Tm n
b [ v₁ & v₂ ]ᵗ = subᵗ (v₂ ∷ᵗ v₁ ∷ᵗ tvar) b

------------------------------------------------------------------------
-- Values and reduction (call by value, left to right).

data Value : Tm n → Type where
  v-lam  : ∀ {q A} {b : Tm (suc n)} → Value (tlam q A b)
  v-pair : {s t : Tm n} → Value s → Value t → Value (pair s t)
  v-inj₁ : {t : Tm n} → Value t → Value (inj₁ t)
  v-inj₂ : {t : Tm n} → Value t → Value (inj₂ t)
  v-lit  : ∀ {ℓ} → Value {n} (lit ℓ)
  -- A value in a trope state: the transition that led to the state,
  -- on a value. A transition to the raw state is not a value.
  v-step : ∀ {o s} {t : Tm n} → Value t → to o ≡ just s → Value (step o t)

-- The raw value under the transitions of a value in the state m.
peel : Maybe Con₁ → Tm n → Tm n
peel nothing  t          = t
peel (just s) (step o t) = peel (from o) t
peel (just s) t          = t

infix 4 _⟶_
data _⟶_ {n : ℕ} : Tm n → Tm n → Type where
  β-lam   : ∀ {q A b v} → Value v → tapp (tlam q A b) v ⟶ b [ v ]ᵗ
  β-pair  : ∀ {v₁ v₂ b} → Value v₁ → Value v₂ → letp (pair v₁ v₂) b ⟶ b [ v₁ & v₂ ]ᵗ
  β-inj₁  : ∀ {v l r} → Value v → case (inj₁ v) l r ⟶ l [ v ]ᵗ
  β-inj₂  : ∀ {v l r} → Value v → case (inj₂ v) l r ⟶ r [ v ]ᵗ
  -- A transition to the raw state gives back the raw value.
  β-strip : ∀ {o v} → Value v → to o ≡ nothing → step o v ⟶ peel (from o) v
  ξ-app₁  : ∀ {f f' a} → f ⟶ f' → tapp f a ⟶ tapp f' a
  ξ-app₂  : ∀ {f a a'} → Value f → a ⟶ a' → tapp f a ⟶ tapp f a'
  ξ-pair₁ : ∀ {s s' t} → s ⟶ s' → pair s t ⟶ pair s' t
  ξ-pair₂ : ∀ {s t t'} → Value s → t ⟶ t' → pair s t ⟶ pair s t'
  ξ-letp  : ∀ {s s' b} → s ⟶ s' → letp s b ⟶ letp s' b
  ξ-inj₁  : ∀ {t t'} → t ⟶ t' → inj₁ t ⟶ inj₁ t'
  ξ-inj₂  : ∀ {t t'} → t ⟶ t' → inj₂ t ⟶ inj₂ t'
  ξ-case  : ∀ {s s' l r} → s ⟶ s' → case s l r ⟶ case s' l r
  ξ-step  : ∀ {o t t'} → t ⟶ t' → step o t ⟶ step o t'
