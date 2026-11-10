{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- Stage 8. The statements about coercions at open types, frozen before
-- their proofs. This file imports definitions and no proof.
open import Cubical.Foundations.Prelude
open import Wager.FC.Signature
open import Wager.Grade.Algebra
import Wager.Trans.Scheme

module Wager.Poly.CoercionStatements
  (SS : SSig) (Sc : Wager.Trans.Scheme.StateScheme SS)
  {R : Type} (ops : GradeOps R) where

open import Cubical.Data.Nat.Base using (ℕ)
open import Cubical.Data.Sigma using (_,_)
open import Cubical.Data.Sum.Base using (inr)

open import Wager.Role.Role using (rep)
open import Wager.FC.Types SS using (STy; N₁)
open import Wager.FC.Coercion SS using (Co; c-ax₁)
open SSig SS using (WellRoled)
open import Wager.Trans.Target SS Sc ops
open import Wager.Trans.Coercion SS Sc ops using (coerceT)
open import Wager.Poly.Coercion SS Sc ops
open import Wager.Poly.Typing tSig tTSig ops using (Cxᵖ; 0ᵘ; _▸_⊢ᵖ_∶_)
open GradeOps ops using (𝟙)

-- T8-Type-Instance. The translation of types commutes with
-- instantiation: the instance of the translation of an open source type
-- is the translation of the instance.
T8-Type-Instance : Type
T8-Type-Instance = ∀ {Δ} (θ : OTy Δ) (ρ : SInst Δ) (s : TySub [] Δ) →
                   Agrees s ρ → sub s (Tᵒ θ) ≡ T (θ ⟦ ρ ⟧)

-- T8-Coercion-Typed. ONE POLYMORPHIC COERCION. For a source signature
-- that passes the role check, and for the laws of a grade algebra, the
-- translation of an open coercion is one typed open function of the
-- target. It uses no term variable of the context.
T8-Coercion-Typed : Type
T8-Coercion-Typed = GradeLaws ops → WellRoled →
                    ∀ {Δ} {θ φ : OTy Δ} (c : Coᵒ θ φ) {n} (Γ : Cxᵖ Δ n) →
                    0ᵘ ▸ Γ ⊢ᵖ coerceᵒ c ∶ arr 𝟙 (Tᵒ θ) (Tᵒ φ)

-- T8-Coercion-Instance. Each closed instance of the open function is
-- the closed coercion function of `Wager.Trans.Coercion`, for the
-- instance of the coercion. The two terms are equal as terms.
T8-Coercion-Instance : Type
T8-Coercion-Instance = ∀ {Δ} {θ φ : OTy Δ} (c : Coᵒ θ φ) (ρ : SInst Δ)
                       (s : TySub [] Δ) → Agrees s ρ → ∀ {n} →
                       ⌊ inst s (coerceᵒ {n = n} c) ⌋ ≡ coerceT (c ⟦ ρ ⟧ᶜ)

-- T8-Ops-Rigid. Instantiation does not change a trope operation: each
-- closed instance of an open term has the operations of the open term.
T8-Ops-Rigid : Type
T8-Ops-Rigid = ∀ {Δ n} (s : TySub [] Δ) (t : Tmᵖ Δ n) →
               opsOf ⌊ inst s t ⌋ ≡ opsOfᵖ t

-- T8-No-Uniform-Unwrap. THE LIMIT. Let N be a newtype with a
-- parameter. If one open term has, at two instantiations, the two
-- closed coercion functions `N τ₁ → body` and `N τ₂ → body`, then τ₁
-- and τ₂ are one source type. So no open term is the coercion
-- `N a → body` at each instance of a type variable a.
T8-No-Uniform-Unwrap : Type
T8-No-Uniform-Unwrap = ∀ {Δ} (N : N₁) (τ₁ τ₂ : STy) (t : Tmᵖ Δ 0)
                       (s₁ s₂ : TySub [] Δ) →
                       ⌊ inst s₁ t ⌋ ≡ coerceT (c-ax₁ N τ₁) →
                       ⌊ inst s₂ t ⌋ ≡ coerceT (c-ax₁ N τ₂) →
                       τ₁ ≡ τ₂
