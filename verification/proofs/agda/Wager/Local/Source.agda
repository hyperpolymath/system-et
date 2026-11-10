{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- DESIGN-CHOICES.adoc, DC-0.3: matches on typed terms.
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- The source calculus of Stage 6: local equality assumptions
-- (DESIGN-CHOICES.adoc, DC-6.2 and DC-6.3).
--
-- This is a new small calculus. It is not the calculus of Stage 3: it
-- has no newtype, no role and no type-level function.
--
--   LTy     types: a base type, a function, a sum, and `⟨ τ ~ σ ⟩ ρ`.
--           `⟨ τ ~ σ ⟩ ρ` is the type of a GADT constructor field in
--           System FC: a value of the type ρ, with evidence that the
--           types τ and σ are equal.
--   Eqs     a list of local equality assumptions.
--   Coˡ     equality of two types under assumptions (a nominal coercion).
--   LTm     typed terms. `lpack` builds a value with evidence. `lopen`
--           is the match: its body has the equality as an assumption.
--   erˡ     the erased type. Evidence has no erased type.
--   eraseˡ  the erased term. A cast and evidence leave no term.
--
-- A type is closed. The calculus has no type variable (DC-6.2).
open import Cubical.Foundations.Prelude

module Wager.Local.Source (B Lit : Type) (litTy : Lit → B) where

open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.FinData.Base using (Fin; zero; suc)

open import Wager.Erased.Untyped
open Terms Lit public

infixr 20 _⇒ˡ_
infixr 29 _+ˡ_
infix  31 ⟨_~_⟩_
infixl 4 _,_~_
infix  3 _∋_~_

------------------------------------------------------------------------
-- Types and local assumptions.

data LTy : Type where
  lbase  : B → LTy
  _⇒ˡ_   : LTy → LTy → LTy
  _+ˡ_   : LTy → LTy → LTy
  ⟨_~_⟩_ : LTy → LTy → LTy → LTy

private
  variable
    n : ℕ
    τ σ υ ρ τ' σ' : LTy

data Eqs : Type where
  ∅ᵃ    : Eqs
  _,_~_ : Eqs → LTy → LTy → Eqs

private
  variable
    Δ : Eqs

-- The assumption `τ ~ σ` is in the list.
data _∋_~_ : Eqs → LTy → LTy → Type where
  here  : (Δ , τ ~ σ) ∋ τ ~ σ
  there : Δ ∋ τ ~ σ → (Δ , τ' ~ σ') ∋ τ ~ σ

-- Equality of two types under the assumptions Δ.
data Coˡ (Δ : Eqs) : LTy → LTy → Type where
  l-hyp   : Δ ∋ τ ~ σ → Coˡ Δ τ σ
  l-refl  : Coˡ Δ τ τ
  l-sym   : Coˡ Δ τ σ → Coˡ Δ σ τ
  l-trans : Coˡ Δ τ σ → Coˡ Δ σ υ → Coˡ Δ τ υ
  l-arr   : Coˡ Δ τ τ' → Coˡ Δ σ σ' → Coˡ Δ (τ ⇒ˡ σ) (τ' ⇒ˡ σ')
  l-sum   : Coˡ Δ τ τ' → Coˡ Δ σ σ' → Coˡ Δ (τ +ˡ σ) (τ' +ˡ σ')

------------------------------------------------------------------------
-- Terms.

-- A context: the type of each term variable.
LCx : ℕ → Type
LCx n = Fin n → LTy

infixl 5 _▹ˡ_
_▹ˡ_ : LCx n → LTy → LCx (suc n)
(Γ ▹ˡ τ) zero    = τ
(Γ ▹ˡ τ) (suc i) = Γ i

∅ˡ : LCx 0
∅ˡ ()

data LTm : Eqs → LCx n → LTy → Type where
  lvar  : ∀ {Γ : LCx n} i → LTm Δ Γ (Γ i)
  llam  : ∀ {Γ : LCx n} → LTm Δ (Γ ▹ˡ τ) σ → LTm Δ Γ (τ ⇒ˡ σ)
  lapp  : ∀ {Γ : LCx n} → LTm Δ Γ (τ ⇒ˡ σ) → LTm Δ Γ τ → LTm Δ Γ σ
  linl  : ∀ {Γ : LCx n} → LTm Δ Γ τ → LTm Δ Γ (τ +ˡ σ)
  linr  : ∀ {Γ : LCx n} → LTm Δ Γ σ → LTm Δ Γ (τ +ˡ σ)
  lcase : ∀ {Γ : LCx n} → LTm Δ Γ (τ +ˡ σ) →
          LTm Δ (Γ ▹ˡ τ) υ → LTm Δ (Γ ▹ˡ σ) υ → LTm Δ Γ υ
  llit  : ∀ {Γ : LCx n} ℓ → LTm Δ Γ (lbase (litTy ℓ))
  -- A cast along an equality.
  lcast : ∀ {Γ : LCx n} → Coˡ Δ τ σ → LTm Δ Γ τ → LTm Δ Γ σ
  -- A value with evidence that τ and σ are equal.
  lpack : ∀ {Γ : LCx n} → Coˡ Δ τ σ → LTm Δ Γ ρ → LTm Δ Γ (⟨ τ ~ σ ⟩ ρ)
  -- The match: the body sees the value at index 0, and it has the
  -- equality `τ ~ σ` as a local assumption.
  lopen : ∀ {Γ : LCx n} → LTm Δ Γ (⟨ τ ~ σ ⟩ ρ) →
          LTm (Δ , τ ~ σ) (Γ ▹ˡ ρ) υ → LTm Δ Γ υ

------------------------------------------------------------------------
-- Erasure.

erˡ : LTy → ETy B
erˡ (lbase b)     = ebase b
erˡ (τ ⇒ˡ σ)      = earr (erˡ τ) (erˡ σ)
erˡ (τ +ˡ σ)      = esum (erˡ τ) (erˡ σ)
erˡ (⟨ τ ~ σ ⟩ ρ) = erˡ ρ

-- The match becomes a β-redex: the body is a function of the value.
eraseˡ : ∀ {Γ : LCx n} → LTm Δ Γ τ → UTm n
eraseˡ (lvar i)      = uvar i
eraseˡ (llam e)      = ulam (eraseˡ e)
eraseˡ (lapp f a)    = uapp (eraseˡ f) (eraseˡ a)
eraseˡ (linl e)      = uinl (eraseˡ e)
eraseˡ (linr e)      = uinr (eraseˡ e)
eraseˡ (lcase s l r) = ucase (eraseˡ s) (eraseˡ l) (eraseˡ r)
eraseˡ (llit ℓ)      = ulit ℓ
eraseˡ (lcast γ e)   = eraseˡ e
eraseˡ (lpack γ e)   = eraseˡ e
eraseˡ (lopen e b)   = uapp (ulam (eraseˡ b)) (eraseˡ e)
