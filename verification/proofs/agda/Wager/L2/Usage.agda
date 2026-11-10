{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- DESIGN-CHOICES.adoc, DC-0.3: matches on `Fin`.
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- Usage vectors: one grade for each term variable.
-- A usage vector is a function on `Fin n`, so that the semiring laws
-- lift to vectors by function extensionality.
open import Cubical.Foundations.Prelude
open import Wager.Grade.Algebra

module Wager.L2.Usage {R : Type} (ops : GradeOps R) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.FinData.Base using (Fin; zero; suc)

open GradeOps ops

private
  variable
    n m : ℕ

Usage : ℕ → Type
Usage n = Fin n → R

infixl 6 _+ᵘ_
infixl 7 _·ᵘ_
infixl 5 _▹_
infix  4 _≤ᵘ_

0ᵘ : Usage n
0ᵘ _ = 𝟘

_+ᵘ_ : Usage n → Usage n → Usage n
(γ +ᵘ δ) i = γ i + δ i

_·ᵘ_ : R → Usage n → Usage n
(r ·ᵘ γ) i = r · γ i

_≤ᵘ_ : Usage n → Usage n → Type
γ ≤ᵘ δ = ∀ i → γ i ≤ δ i

-- Extension by the grade of a new variable (index zero).
_▹_ : Usage n → R → Usage (suc n)
(γ ▹ r) zero    = r
(γ ▹ r) (suc i) = γ i

-- 𝟙 at the variable i and 𝟘 at each other variable.
unit : Fin n → Usage n
unit zero    = 0ᵘ ▹ 𝟙
unit (suc i) = unit i ▹ 𝟘

-- A usage matrix: one row of usage for each variable of a source
-- context. `γ ⊛ Ψ` is the vector-matrix product.
Mat : ℕ → ℕ → Type
Mat n m = Fin n → Usage m

infixl 7 _⊛_
_⊛_ : Usage n → Mat n m → Usage m
_⊛_ {n = zero}  γ Ψ = 0ᵘ
_⊛_ {n = suc n} γ Ψ = (γ zero ·ᵘ Ψ zero) +ᵘ ((λ i → γ (suc i)) ⊛ (λ i → Ψ (suc i)))

-- The matrix of a substitution under one more binder.
liftM : Mat n m → Mat (suc n) (suc m)
liftM Ψ zero    = unit zero
liftM Ψ (suc i) = Ψ i ▹ 𝟘

-- The matrix of a substitution of the top variable.
infixr 5 _∷ᵐ_
_∷ᵐ_ : Usage m → Mat n m → Mat (suc n) m
(δ ∷ᵐ Ψ) zero    = δ
(δ ∷ᵐ Ψ) (suc i) = Ψ i
