{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- The L2 grade-algebra contract (ET-4), after
-- verification/proofs/lean4/Systemet/L2/GradeAlgebra.lean.
--
-- The Lean class has 5 operations and 15 law fields, and it derives
-- `zero_add`. The documents count 16 laws. This file has the same
-- 15 fields and the same derived law.
--
-- The operations and the laws are separate records. A structure that
-- has the operations but fails a law is thus a value that Agda can
-- examine (Stage 2 needs this for the role tables).
module Wager.Grade.Algebra where

open import Cubical.Foundations.Prelude

-- The operations of a grade structure on the carrier R.
--   𝟘    the grade of an assumption that is not used
--   𝟙    the grade of one direct use
--   _+_  the join of two uses of one assumption
--   _·_  scaling
--   _≤_  subusage: a computed grade r is accepted where s is declared
record GradeOps (R : Type) : Type₁ where
  infixl 6 _+_
  infixl 7 _·_
  infix  4 _≤_
  field
    _+_ : R → R → R
    _·_ : R → R → R
    𝟘   : R
    𝟙   : R
    _≤_ : R → R → Type

-- The laws of an ordered semiring. Field order follows the Lean class.
record GradeLaws {R : Type} (ops : GradeOps R) : Type where
  open GradeOps ops
  field
    -- `+` is a commutative monoid with unit 𝟘.
    add-assoc     : ∀ a b c → (a + b) + c ≡ a + (b + c)
    add-comm      : ∀ a b → a + b ≡ b + a
    add-zero      : ∀ a → a + 𝟘 ≡ a
    -- `·` is a monoid with unit 𝟙, and 𝟘 absorbs.
    mul-assoc     : ∀ a b c → (a · b) · c ≡ a · (b · c)
    one-mul       : ∀ a → 𝟙 · a ≡ a
    mul-one       : ∀ a → a · 𝟙 ≡ a
    zero-mul      : ∀ a → 𝟘 · a ≡ 𝟘
    mul-zero      : ∀ a → a · 𝟘 ≡ 𝟘
    -- `·` distributes over `+` on both sides.
    left-distrib  : ∀ a b c → a · (b + c) ≡ (a · b) + (a · c)
    right-distrib : ∀ a b c → (a + b) · c ≡ (a · c) + (b · c)
    -- `≤` is a partial order.
    le-refl       : ∀ a → a ≤ a
    le-trans      : ∀ a b c → a ≤ b → b ≤ c → a ≤ c
    le-antisym    : ∀ a b → a ≤ b → b ≤ a → a ≡ b
    -- The operations are monotone.
    add-mono      : ∀ a b c d → a ≤ b → c ≤ d → (a + c) ≤ (b + d)
    mul-mono      : ∀ a b c d → a ≤ b → c ≤ d → (a · c) ≤ (b · d)

  -- Derived, as in the Lean file.
  zero-add : ∀ a → 𝟘 + a ≡ a
  zero-add a = add-comm 𝟘 a ∙ add-zero a

-- A grade algebra: operations that satisfy the laws.
record GradeAlgebra (R : Type) : Type₁ where
  field
    ops  : GradeOps R
    laws : GradeLaws ops
  open GradeOps ops public
  open GradeLaws laws public

-- The laws without `mul-zero` (a · 𝟘 ≡ 𝟘). Stage 2 examines a
-- structure that has these 14 laws and fails `mul-zero`.
record GradeLawsExceptMulZero {R : Type} (ops : GradeOps R) : Type where
  open GradeOps ops
  field
    add-assoc     : ∀ a b c → (a + b) + c ≡ a + (b + c)
    add-comm      : ∀ a b → a + b ≡ b + a
    add-zero      : ∀ a → a + 𝟘 ≡ a
    mul-assoc     : ∀ a b c → (a · b) · c ≡ a · (b · c)
    one-mul       : ∀ a → 𝟙 · a ≡ a
    mul-one       : ∀ a → a · 𝟙 ≡ a
    zero-mul      : ∀ a → 𝟘 · a ≡ 𝟘
    left-distrib  : ∀ a b c → a · (b + c) ≡ (a · b) + (a · c)
    right-distrib : ∀ a b c → (a + b) · c ≡ (a · c) + (b · c)
    le-refl       : ∀ a → a ≤ a
    le-trans      : ∀ a b c → a ≤ b → b ≤ c → a ≤ c
    le-antisym    : ∀ a b → a ≤ b → b ≤ a → a ≡ b
    add-mono      : ∀ a b c d → a ≤ b → c ≤ d → (a + c) ≤ (b + d)
    mul-mono      : ∀ a b c d → a ≤ b → c ≤ d → (a · c) ≤ (b · d)

-- The 14 laws and `mul-zero` together are exactly the 15 laws.
withMulZero : {R : Type} {ops : GradeOps R} → GradeLawsExceptMulZero ops →
              (∀ a → GradeOps._·_ ops a (GradeOps.𝟘 ops) ≡ GradeOps.𝟘 ops) → GradeLaws ops
withMulZero L mz = record
  { add-assoc = add-assoc ; add-comm = add-comm ; add-zero = add-zero
  ; mul-assoc = mul-assoc ; one-mul = one-mul ; mul-one = mul-one
  ; zero-mul = zero-mul ; mul-zero = mz
  ; left-distrib = left-distrib ; right-distrib = right-distrib
  ; le-refl = le-refl ; le-trans = le-trans ; le-antisym = le-antisym
  ; add-mono = add-mono ; mul-mono = mul-mono }
  where open GradeLawsExceptMulZero L
