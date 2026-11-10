{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- DESIGN-CHOICES.adoc, DC-0.3: matches on typed terms.
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- Terms of the source calculus, their typing and their erasure
-- (Stage 3).
--
-- A term is typed by construction: `STm Γ τ` is the set of the terms of
-- the type τ in the context Γ. The term `cast γ e` needs a coercion
-- `γ : Co rep τ σ`. A program that has no such coercion is not a term:
-- this is how the source calculus rejects a wrong `coerce`.
--
-- Erasure maps a term to an untyped term. A cast vanishes.
open import Wager.FC.Signature

module Wager.FC.Term (SS : SSig) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.FinData.Base using (Fin; zero; suc)

open import Wager.Role.Role
open import Wager.FC.Types SS
open import Wager.FC.Coercion SS
open import Wager.Erased.Untyped
open Terms Lit public

private
  variable
    n : ℕ
    τ σ υ : STy

-- A context: the (closed) type of each term variable.
SCx : ℕ → Type
SCx n = Fin n → STy

infixl 5 _▹ˢ_
_▹ˢ_ : SCx n → STy → SCx (suc n)
(Γ ▹ˢ τ) zero    = τ
(Γ ▹ˢ τ) (suc i) = Γ i

∅ˢ : SCx 0
∅ˢ ()

data STm : SCx n → STy → Type where
  svar  : ∀ {Γ : SCx n} i → STm Γ (Γ i)
  slam  : ∀ {Γ : SCx n} → STm (Γ ▹ˢ τ) σ → STm Γ (τ ⇒ˢ σ)
  sapp  : ∀ {Γ : SCx n} → STm Γ (τ ⇒ˢ σ) → STm Γ τ → STm Γ σ
  spair : ∀ {Γ : SCx n} → STm Γ τ → STm Γ σ → STm Γ (τ ×ˢ σ)
  -- The body sees the first component at index 1 and the second at index 0.
  sletp : ∀ {Γ : SCx n} → STm Γ (τ ×ˢ σ) → STm (Γ ▹ˢ τ ▹ˢ σ) υ → STm Γ υ
  sinl  : ∀ {Γ : SCx n} → STm Γ τ → STm Γ (τ +ˢ σ)
  sinr  : ∀ {Γ : SCx n} → STm Γ σ → STm Γ (τ +ˢ σ)
  scase : ∀ {Γ : SCx n} → STm Γ (τ +ˢ σ) → STm (Γ ▹ˢ τ) υ → STm (Γ ▹ˢ σ) υ → STm Γ υ
  slit  : ∀ {Γ : SCx n} ℓ → STm Γ (sbase (litTy ℓ))
  -- A cast along a representational coercion.
  cast  : ∀ {Γ : SCx n} → Co rep τ σ → STm Γ τ → STm Γ σ

-- `coerce`, at the two types of a representational coercion.
coerce : ∀ {Γ : SCx n} → Co rep τ σ → STm Γ (τ ⇒ˢ σ)
coerce γ = slam (cast γ (svar zero))

-- Erasure. The last clause is the point: a cast vanishes.
eraseTm : ∀ {Γ : SCx n} → STm Γ τ → UTm n
eraseTm (svar i)      = uvar i
eraseTm (slam b)      = ulam (eraseTm b)
eraseTm (sapp f a)    = uapp (eraseTm f) (eraseTm a)
eraseTm (spair s t)   = upair (eraseTm s) (eraseTm t)
eraseTm (sletp s b)   = uletp (eraseTm s) (eraseTm b)
eraseTm (sinl t)      = uinl (eraseTm t)
eraseTm (sinr t)      = uinr (eraseTm t)
eraseTm (scase s l r) = ucase (eraseTm s) (eraseTm l) (eraseTm r)
eraseTm (slit ℓ)      = ulit ℓ
eraseTm (cast γ e)    = eraseTm e
