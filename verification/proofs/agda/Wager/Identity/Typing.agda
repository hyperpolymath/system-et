{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- Typing of the target with the identity family (Stage 6, part 2).
--
-- The judgement `γ ▸ Γ ⊢ⁱ t ∶ A` has the 12 rules of the target
-- judgement (`Wager.L2.Typing`), with the same text, and ONE new rule:
-- `t-cast`. The judgement form is the form `Γ ⊢ᵣ t : A` of 00-notation.
--
-- `t-cast` uses the evidence at the grade 𝟘: the usage vector of the
-- evidence is scaled by 𝟘. The rule names no grade other than 𝟘, and
-- it has no side condition for one algebra.
--
-- There is no introduction rule: the evidence `rfl A` is a literal,
-- and `t-lit` types it.
open import Wager.L1.Signature
open import Wager.Grade.Algebra
import Wager.L2.Signature
import Wager.Identity.Family
module Wager.Identity.Typing
  (S : Sig) (TS : Wager.L2.Signature.TSig S) (ops : GradeOps (Sig.TG S))
  (F : Wager.Identity.Family.IdFamily S TS) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.FinData.Base using (Fin; zero; suc)

open import Wager.L1.Syntax S
open import Wager.L1.Conversion S
open import Wager.L2.Typing S TS ops using (Cx; _▹ᶜ_) public
open import Wager.L2.Term S TS using (Lit; litTy; Op; carrier; from; to; _at_) public
open import Wager.L2.Usage ops public
open import Wager.Identity.Term S TS public
open Wager.Identity.Family.IdFamily F public
open GradeOps ops

private
  variable
    n : ℕ

infix 3 _▸_⊢ⁱ_∶_

data _▸_⊢ⁱ_∶_ {n : ℕ} : Usage n → Cx n → ITm n → Ty [] ★ → Type where
  -- The 12 rules of the target.
  t-var  : ∀ {Γ} i → unit i ▸ Γ ⊢ⁱ ivar i ∶ Γ i
  t-lam  : ∀ {γ Γ q A B b} →
           (γ ▹ q) ▸ (Γ ▹ᶜ A) ⊢ⁱ b ∶ B →
           γ ▸ Γ ⊢ⁱ ilam q A b ∶ arr q A B
  t-app  : ∀ {γ δ Γ q A B f a} →
           γ ▸ Γ ⊢ⁱ f ∶ arr q A B → δ ▸ Γ ⊢ⁱ a ∶ A →
           (γ +ᵘ (q ·ᵘ δ)) ▸ Γ ⊢ⁱ iapp f a ∶ B
  t-pair : ∀ {γ δ Γ A B s t} →
           γ ▸ Γ ⊢ⁱ s ∶ A → δ ▸ Γ ⊢ⁱ t ∶ B →
           (γ +ᵘ δ) ▸ Γ ⊢ⁱ ipair s t ∶ A ⊗ B
  t-letp : ∀ {γ δ Γ A B C s b} →
           γ ▸ Γ ⊢ⁱ s ∶ A ⊗ B →
           (δ ▹ 𝟙 ▹ 𝟙) ▸ (Γ ▹ᶜ A ▹ᶜ B) ⊢ⁱ b ∶ C →
           (γ +ᵘ δ) ▸ Γ ⊢ⁱ iletp s b ∶ C
  t-inj₁ : ∀ {γ Γ A B t} → γ ▸ Γ ⊢ⁱ t ∶ A → γ ▸ Γ ⊢ⁱ iinj₁ t ∶ A ⊕ B
  t-inj₂ : ∀ {γ Γ A B t} → γ ▸ Γ ⊢ⁱ t ∶ B → γ ▸ Γ ⊢ⁱ iinj₂ t ∶ A ⊕ B
  t-case : ∀ {γ δ Γ A B C s l r} →
           γ ▸ Γ ⊢ⁱ s ∶ A ⊕ B →
           (δ ▹ 𝟙) ▸ (Γ ▹ᶜ A) ⊢ⁱ l ∶ C →
           (δ ▹ 𝟙) ▸ (Γ ▹ᶜ B) ⊢ⁱ r ∶ C →
           (γ +ᵘ δ) ▸ Γ ⊢ⁱ icase s l r ∶ C
  t-lit  : ∀ {Γ} ℓ → 0ᵘ ▸ Γ ⊢ⁱ ilit ℓ ∶ base (litTy ℓ)
  t-step : ∀ {γ Γ t} o →
           γ ▸ Γ ⊢ⁱ t ∶ carrier o at from o →
           γ ▸ Γ ⊢ⁱ istep o t ∶ carrier o at to o
  t-conv : ∀ {γ Γ A B t} → γ ▸ Γ ⊢ⁱ t ∶ A → DefEq A B → γ ▸ Γ ⊢ⁱ t ∶ B
  t-sub  : ∀ {γ δ Γ A t} → γ ▸ Γ ⊢ⁱ t ∶ A → γ ≤ᵘ δ → δ ▸ Γ ⊢ⁱ t ∶ A
  -- THE NEW RULE. Evidence that A and B are equal moves a term from A
  -- to B. The evidence is used at the grade 𝟘.
  t-cast : ∀ {γ δ Γ A B e t} →
           γ ▸ Γ ⊢ⁱ e ∶ base (Id A B) →
           δ ▸ Γ ⊢ⁱ t ∶ A →
           ((𝟘 ·ᵘ γ) +ᵘ δ) ▸ Γ ⊢ⁱ cast e t ∶ B

-- A local equality assumption is a variable. The function takes
-- evidence that A and B are equal, at the grade 𝟘, then a term of the
-- type A, and gives the term at the type B.
use-assumption : Ty [] ★ → Ty [] ★ → ITm 0
use-assumption A B =
  ilam 𝟘 (base (Id A B)) (ilam 𝟙 A (cast (ivar (suc zero)) (ivar zero)))
