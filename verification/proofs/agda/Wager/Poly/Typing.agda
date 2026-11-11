{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- Stage 8. The typing judgement for terms with open types.
-- Each rule is the rule of `Wager.L2.Typing` with the types in Δ.
-- No rule is new, and no rule names a grade other than 𝟘 and 𝟙.
open import Wager.L1.Signature
open import Wager.Grade.Algebra
import Wager.L2.Signature

module Wager.Poly.Typing
  (S : Sig) (TS : Wager.L2.Signature.TSig S) (ops : GradeOps (Sig.TG S)) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.FinData.Base using (Fin; zero; suc)
open import Wager.L1.Syntax S
open import Wager.L1.Conversion S
open import Wager.L2.Term S TS using (Lit; litTy; Op; carrier; from; to; _at_)
open import Wager.L2.Usage ops public
open import Wager.Poly.Term S TS public
open GradeOps ops

private
  variable
    n : ℕ
    Δ : Ctx

Cxᵖ : Ctx → ℕ → Type
Cxᵖ Δ n = Fin n → Ty Δ ★

infixl 5 _▹ᵖ_
_▹ᵖ_ : Cxᵖ Δ n → Ty Δ ★ → Cxᵖ Δ (suc n)
(Γ ▹ᵖ A) zero    = A
(Γ ▹ᵖ A) (suc i) = Γ i

infix 3 _▸_⊢ᵖ_∶_
data _▸_⊢ᵖ_∶_ {Δ : Ctx} {n : ℕ} : Usage n → Cxᵖ Δ n → Tmᵖ Δ n → Ty Δ ★ → Type where
  t-var  : ∀ {Γ} i → unit i ▸ Γ ⊢ᵖ tvar i ∶ Γ i
  t-lam  : ∀ {γ Γ q A B b} →
           (γ ▹ q) ▸ (Γ ▹ᵖ A) ⊢ᵖ b ∶ B →
           γ ▸ Γ ⊢ᵖ tlam q A b ∶ arr q A B
  t-app  : ∀ {γ δ Γ q A B f a} →
           γ ▸ Γ ⊢ᵖ f ∶ arr q A B → δ ▸ Γ ⊢ᵖ a ∶ A →
           (γ +ᵘ (q ·ᵘ δ)) ▸ Γ ⊢ᵖ tapp f a ∶ B
  t-pair : ∀ {γ δ Γ A B s t} →
           γ ▸ Γ ⊢ᵖ s ∶ A → δ ▸ Γ ⊢ᵖ t ∶ B →
           (γ +ᵘ δ) ▸ Γ ⊢ᵖ pair s t ∶ A ⊗ B
  t-letp : ∀ {γ δ Γ A B C s b} →
           γ ▸ Γ ⊢ᵖ s ∶ A ⊗ B →
           (δ ▹ 𝟙 ▹ 𝟙) ▸ (Γ ▹ᵖ A ▹ᵖ B) ⊢ᵖ b ∶ C →
           (γ +ᵘ δ) ▸ Γ ⊢ᵖ letp s b ∶ C
  t-inj₁ : ∀ {γ Γ A B t} → γ ▸ Γ ⊢ᵖ t ∶ A → γ ▸ Γ ⊢ᵖ inj₁ t ∶ A ⊕ B
  t-inj₂ : ∀ {γ Γ A B t} → γ ▸ Γ ⊢ᵖ t ∶ B → γ ▸ Γ ⊢ᵖ inj₂ t ∶ A ⊕ B
  t-case : ∀ {γ δ Γ A B C s l r} →
           γ ▸ Γ ⊢ᵖ s ∶ A ⊕ B →
           (δ ▹ 𝟙) ▸ (Γ ▹ᵖ A) ⊢ᵖ l ∶ C →
           (δ ▹ 𝟙) ▸ (Γ ▹ᵖ B) ⊢ᵖ r ∶ C →
           (γ +ᵘ δ) ▸ Γ ⊢ᵖ case s l r ∶ C
  t-lit  : ∀ {Γ} ℓ → 0ᵘ ▸ Γ ⊢ᵖ lit ℓ ∶ base (litTy ℓ)
  t-step : ∀ {γ Γ t} o →
           γ ▸ Γ ⊢ᵖ t ∶ ⇑ (carrier o at from o) →
           γ ▸ Γ ⊢ᵖ step o t ∶ ⇑ (carrier o at to o)
  t-conv : ∀ {γ Γ A B t} → γ ▸ Γ ⊢ᵖ t ∶ A → DefEq A B → γ ▸ Γ ⊢ᵖ t ∶ B
  t-sub  : ∀ {γ δ Γ A t} → γ ▸ Γ ⊢ᵖ t ∶ A → γ ≤ᵘ δ → δ ▸ Γ ⊢ᵖ t ∶ A
