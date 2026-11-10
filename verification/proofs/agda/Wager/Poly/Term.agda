{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- Stage 8. Terms of the target with open types.
-- The terms of `Wager.L2.Term` have closed types only (`Ty [] ★`). Here a
-- term is in a context Δ of type variables, and a type annotation is a type
-- in Δ. There is no quantifier: a polymorphic program is an open term.
open import Wager.L1.Signature
import Wager.L2.Signature

module Wager.Poly.Term (S : Sig) (TS : Wager.L2.Signature.TSig S) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.FinData.Base using (Fin; zero; suc)
open import Wager.L1.Syntax S
open import Wager.L2.Term S TS

private
  variable
    n m : ℕ
    Δ Δ' : Ctx

data Tmᵖ (Δ : Ctx) : ℕ → Type where
  tvar : Fin n → Tmᵖ Δ n
  tlam : TG → Ty Δ ★ → Tmᵖ Δ (suc n) → Tmᵖ Δ n
  tapp : Tmᵖ Δ n → Tmᵖ Δ n → Tmᵖ Δ n
  pair : Tmᵖ Δ n → Tmᵖ Δ n → Tmᵖ Δ n
  letp : Tmᵖ Δ n → Tmᵖ Δ (suc (suc n)) → Tmᵖ Δ n
  inj₁ : Tmᵖ Δ n → Tmᵖ Δ n
  inj₂ : Tmᵖ Δ n → Tmᵖ Δ n
  case : Tmᵖ Δ n → Tmᵖ Δ (suc n) → Tmᵖ Δ (suc n) → Tmᵖ Δ n
  lit  : Lit → Tmᵖ Δ n
  step : Op → Tmᵖ Δ n → Tmᵖ Δ n

-- Instantiation: a substitution of types for the type variables of a term.
inst : TySub Δ' Δ → Tmᵖ Δ n → Tmᵖ Δ' n
inst σ (tvar i)     = tvar i
inst σ (tlam q A b) = tlam q (sub σ A) (inst σ b)
inst σ (tapp f a)   = tapp (inst σ f) (inst σ a)
inst σ (pair s t)   = pair (inst σ s) (inst σ t)
inst σ (letp s b)   = letp (inst σ s) (inst σ b)
inst σ (inj₁ t)     = inj₁ (inst σ t)
inst σ (inj₂ t)     = inj₂ (inst σ t)
inst σ (case s l r) = case (inst σ s) (inst σ l) (inst σ r)
inst σ (lit ℓ)      = lit ℓ
inst σ (step o t)   = step o (inst σ t)

-- A term with no type variable is a term of `Wager.L2.Term`.
⌊_⌋ : Tmᵖ [] n → Tm n
⌊ tvar i ⌋     = tvar i
⌊ tlam q A b ⌋ = tlam q A ⌊ b ⌋
⌊ tapp f a ⌋   = tapp ⌊ f ⌋ ⌊ a ⌋
⌊ pair s t ⌋   = pair ⌊ s ⌋ ⌊ t ⌋
⌊ letp s b ⌋   = letp ⌊ s ⌋ ⌊ b ⌋
⌊ inj₁ t ⌋     = inj₁ ⌊ t ⌋
⌊ inj₂ t ⌋     = inj₂ ⌊ t ⌋
⌊ case s l r ⌋ = case ⌊ s ⌋ ⌊ l ⌋ ⌊ r ⌋
⌊ lit ℓ ⌋      = lit ℓ
⌊ step o t ⌋   = step o ⌊ t ⌋

-- A closed type in a context of type variables.
εᵣ : Ren Δ []
εᵣ k ()

⇑ : Ty [] ★ → Ty Δ ★
⇑ A = ren εᵣ A
