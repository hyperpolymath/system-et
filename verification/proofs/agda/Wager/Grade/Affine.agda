{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- The Affine grade algebra {0, 1, ω}, after
-- verification/proofs/lean4/Systemet/L2/Instances/Affine.lean.
--
-- The order is the systemet order: 0 ≤ ω and 1 ≤ ω, and 0 and 1 are
-- not comparable. The anytype kernel uses a different order
-- (0 ≤ 1 ≤ ω). systemet is the authority for this file.
module Wager.Grade.Affine where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool.Base using (Bool; true; false)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.List.Base using (List; []; _∷_)

open import Wager.Grade.Algebra
open import Wager.Grade.Finite

data Affine : Type where
  a0 a1 aω : Affine

-- Context join: a second use of anything makes it unrestricted.
addA : Affine → Affine → Affine
addA a0 b  = b
addA a1 a0 = a1
addA a1 a1 = aω
addA a1 aω = aω
addA aω _  = aω

-- Scaling: a0 absorbs, a1 is neutral, ω·ω = ω.
mulA : Affine → Affine → Affine
mulA a0 _  = a0
mulA a1 b  = b
mulA aω a0 = a0
mulA aω a1 = aω
mulA aω aω = aω

-- Subusage: ω accepts anything, otherwise the grades are equal.
leA : Affine → Affine → Bool
leA a0 a0 = true
leA a1 a1 = true
leA _  aω = true
leA _  _  = false

private
  eqA : Affine → Affine → Bool
  eqA a0 a0 = true
  eqA a1 a1 = true
  eqA aω aω = true
  eqA _  _  = false

  eqA-sound : ∀ a b → eqA a b ≡ true → a ≡ b
  eqA-sound a0 a0 _ = refl
  eqA-sound a1 a1 _ = refl
  eqA-sound aω aω _ = refl
  eqA-sound a0 a1 p = ⊥.rec (false≢true p)
  eqA-sound a0 aω p = ⊥.rec (false≢true p)
  eqA-sound a1 a0 p = ⊥.rec (false≢true p)
  eqA-sound a1 aω p = ⊥.rec (false≢true p)
  eqA-sound aω a0 p = ⊥.rec (false≢true p)
  eqA-sound aω a1 p = ⊥.rec (false≢true p)

finAffine : Finite Affine
finAffine = record
  { elems    = a0 ∷ a1 ∷ aω ∷ []
  ; complete = λ { P h a0 → &&-l (P a0) h
                 ; P h a1 → &&-l (P a1) (&&-r (P a0) h)
                 ; P h aω → &&-l (P aω) (&&-r (P a1) (&&-r (P a0) h)) }
  ; _==_     = eqA
  ; ==-sound = eqA-sound }

affineB : BoolOps Affine
affineB = record { add = addA ; mul = mulA ; zero = a0 ; one = a1 ; leB = leA }

affineOps : GradeOps Affine
affineOps = toOps affineB

-- Each law holds by computation over the 3 elements.
affineLaws : GradeLaws affineOps
affineLaws = Check.mkLaws finAffine affineB
  refl refl refl refl refl refl refl refl refl refl refl refl refl refl refl

affine : GradeAlgebra Affine
affine = record { ops = affineOps ; laws = affineLaws }
