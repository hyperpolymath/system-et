{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- DESIGN-CHOICES.adoc, DC-0.3: matches on kinded syntax.
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- Graded kinding: the judgement `Γ ⊢ A : k` of 00-notation with a
-- graded context. `γ ⊢ᵏ A` says: the type A uses its type variables
-- as the usage vector γ says. The simple kind of A is intrinsic.
--
-- The current kernel grades term binders only. Grades on kind arrows
-- are a design choice that the task asks for (DESIGN-CHOICES.adoc,
-- DC-1.3).
--
-- No rule names a grade other than 𝟘 and 𝟙. The grade of a constant
-- or of a primitive comes from the signature (`cgrade`, `pgrade`).
-- The module takes the operations only, not the laws: Stage 2
-- examines structures that fail a law.
open import Wager.L1.Signature
open import Wager.Grade.Algebra

module Wager.L1.Kinding (S : Sig) (K : GradeOps (Sig.KG S)) where

open import Cubical.Foundations.Prelude

open import Wager.L1.Syntax S
open GradeOps K

private
  variable
    Γ   : Ctx
    k j : Kind
    g   : KG

-- A usage vector: one grade for each type variable of the context.
KUsage : Ctx → Type
KUsage Γ = ∀ k → Var Γ k → KG

0ᵏ : KUsage Γ
0ᵏ k x = 𝟘

infixl 6 _⊕ᵏ_
infixl 7 _⊙ᵏ_
infixl 5 _▹ᵏ_
infix  4 _≼ᵏ_ _⊢ᵏ_

_⊕ᵏ_ : KUsage Γ → KUsage Γ → KUsage Γ
(γ ⊕ᵏ δ) k x = γ k x + δ k x

_⊙ᵏ_ : KG → KUsage Γ → KUsage Γ
(g ⊙ᵏ γ) k x = g · γ k x

_≼ᵏ_ : KUsage Γ → KUsage Γ → Type
_≼ᵏ_ {Γ} γ δ = ∀ k (x : Var Γ k) → γ k x ≤ δ k x

_▹ᵏ_ : KUsage Γ → KG → KUsage (j ∷ Γ)
(γ ▹ᵏ g) k vz     = g
(γ ▹ᵏ g) k (vs x) = γ k x

-- 𝟙 at the variable x and 𝟘 at each other variable.
unitᵏ : Var Γ j → KUsage Γ
unitᵏ vz     = 0ᵏ ▹ᵏ 𝟙
unitᵏ (vs x) = unitᵏ x ▹ᵏ 𝟘

data _⊢ᵏ_ {Γ : Ctx} : {k : Kind} → KUsage Γ → Ty Γ k → Type where
  k-var  : (x : Var Γ k) → unitᵏ x ⊢ᵏ var x
  k-base : ∀ b → 0ᵏ ⊢ᵏ base b
  -- The parameter grade of a constant or primitive is its signature entry.
  k-capp : ∀ {γ} c {A : Ty Γ ★} → γ ⊢ᵏ A → (cgrade c ⊙ᵏ γ) ⊢ᵏ capp c A
  k-papp : ∀ {γ} p {A : Ty Γ ★} → γ ⊢ᵏ A → (pgrade p ⊙ᵏ γ) ⊢ᵏ papp p A
  k-arr  : ∀ {γ δ q} {A B : Ty Γ ★} → γ ⊢ᵏ A → δ ⊢ᵏ B → (γ ⊕ᵏ δ) ⊢ᵏ arr q A B
  k-prod : ∀ {γ δ} {A B : Ty Γ ★} → γ ⊢ᵏ A → δ ⊢ᵏ B → (γ ⊕ᵏ δ) ⊢ᵏ (A ⊗ B)
  k-sum  : ∀ {γ δ} {A B : Ty Γ ★} → γ ⊢ᵏ A → δ ⊢ᵏ B → (γ ⊕ᵏ δ) ⊢ᵏ (A ⊕ B)
  -- A binder is accepted when the body uses it at its declared grade.
  k-lam  : ∀ {γ} {b : Ty (k ∷ Γ) j} → (γ ▹ᵏ g) ⊢ᵏ b → γ ⊢ᵏ lam {g = g} b
  -- An application scales the usage of the argument by the grade.
  k-app  : ∀ {γ δ} {f : Ty Γ (k ⇒[ g ] j)} {a : Ty Γ k} →
           γ ⊢ᵏ f → δ ⊢ᵏ a → (γ ⊕ᵏ (g ⊙ᵏ δ)) ⊢ᵏ app f a
  -- Subusage.
  k-sub  : ∀ {γ δ} {A : Ty Γ k} → γ ⊢ᵏ A → γ ≼ᵏ δ → δ ⊢ᵏ A
