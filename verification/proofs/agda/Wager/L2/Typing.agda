{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- DESIGN-CHOICES.adoc, DC-0.3: matches on scoped terms.
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- The graded typing judgement `Γ ⊢ᵣ t : A` of 00-notation, written
-- `γ ▸ Γ ⊢ t ∶ A`: the term t has the type A in the context Γ and uses
-- the variables of Γ as the usage vector γ says.
--
-- The judgement is declarative and has a subusage rule (`t-sub`) and
-- a conversion rule (`t-conv`). It takes the operations of a grade
-- structure only. No rule names a grade other than 𝟘 and 𝟙, and no
-- rule has a side condition for one algebra.
--
-- The documents leave the L2 rule table open (03-l2-grades.adoc).
-- The rules follow the checker of the `anytype` kernel
-- (DESIGN-CHOICES.adoc, DC-1.5).
open import Wager.L1.Signature
open import Wager.Grade.Algebra
import Wager.L2.Signature

module Wager.L2.Typing
  (S : Sig) (TS : Wager.L2.Signature.TSig S) (ops : GradeOps (Sig.TG S)) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.FinData.Base using (Fin; zero; suc)

open import Wager.L1.Syntax S
open import Wager.L1.Conversion S
open import Wager.L2.Term S TS public
open import Wager.L2.Usage ops public
open GradeOps ops

private
  variable
    n : ℕ

-- A context: the (closed) type of each term variable.
Cx : ℕ → Type
Cx n = Fin n → Ty [] ★

infixl 5 _▹ᶜ_
_▹ᶜ_ : Cx n → Ty [] ★ → Cx (suc n)
(Γ ▹ᶜ A) zero    = A
(Γ ▹ᶜ A) (suc i) = Γ i

infix 3 _▸_⊢_∶_
data _▸_⊢_∶_ {n : ℕ} : Usage n → Cx n → Tm n → Ty [] ★ → Type where
  -- A variable is used once.
  t-var  : ∀ {Γ} i → unit i ▸ Γ ⊢ tvar i ∶ Γ i
  -- A binder is accepted when the body uses it at its declared grade.
  t-lam  : ∀ {γ Γ q A B b} →
           (γ ▹ q) ▸ (Γ ▹ᶜ A) ⊢ b ∶ B →
           γ ▸ Γ ⊢ tlam q A b ∶ arr q A B
  -- An application scales the usage of the argument by the arrow grade.
  t-app  : ∀ {γ δ Γ q A B f a} →
           γ ▸ Γ ⊢ f ∶ arr q A B → δ ▸ Γ ⊢ a ∶ A →
           (γ +ᵘ (q ·ᵘ δ)) ▸ Γ ⊢ tapp f a ∶ B
  t-pair : ∀ {γ δ Γ A B s t} →
           γ ▸ Γ ⊢ s ∶ A → δ ▸ Γ ⊢ t ∶ B →
           (γ +ᵘ δ) ▸ Γ ⊢ pair s t ∶ A ⊗ B
  -- Each component is bound at the grade 𝟙.
  t-letp : ∀ {γ δ Γ A B C s b} →
           γ ▸ Γ ⊢ s ∶ A ⊗ B →
           (δ ▹ 𝟙 ▹ 𝟙) ▸ (Γ ▹ᶜ A ▹ᶜ B) ⊢ b ∶ C →
           (γ +ᵘ δ) ▸ Γ ⊢ letp s b ∶ C
  t-inj₁ : ∀ {γ Γ A B t} → γ ▸ Γ ⊢ t ∶ A → γ ▸ Γ ⊢ inj₁ t ∶ A ⊕ B
  t-inj₂ : ∀ {γ Γ A B t} → γ ▸ Γ ⊢ t ∶ B → γ ▸ Γ ⊢ inj₂ t ∶ A ⊕ B
  -- The two branches have one usage vector δ. The rule needs no join:
  -- `t-sub` raises each branch to δ.
  t-case : ∀ {γ δ Γ A B C s l r} →
           γ ▸ Γ ⊢ s ∶ A ⊕ B →
           (δ ▹ 𝟙) ▸ (Γ ▹ᶜ A) ⊢ l ∶ C →
           (δ ▹ 𝟙) ▸ (Γ ▹ᶜ B) ⊢ r ∶ C →
           (γ +ᵘ δ) ▸ Γ ⊢ case s l r ∶ C
  t-lit  : ∀ {Γ} ℓ → 0ᵘ ▸ Γ ⊢ lit ℓ ∶ base (litTy ℓ)
  -- Trope transition: the carrier type stays, the state changes.
  t-step : ∀ {γ Γ t} o →
           γ ▸ Γ ⊢ t ∶ carrier o at from o →
           γ ▸ Γ ⊢ step o t ∶ carrier o at to o
  -- Conversion: equality of types is `DefEq`, and no other relation.
  t-conv : ∀ {γ Γ A B t} → γ ▸ Γ ⊢ t ∶ A → DefEq A B → γ ▸ Γ ⊢ t ∶ B
  -- Subusage.
  t-sub  : ∀ {γ δ Γ A t} → γ ▸ Γ ⊢ t ∶ A → γ ≤ᵘ δ → δ ▸ Γ ⊢ t ∶ A
