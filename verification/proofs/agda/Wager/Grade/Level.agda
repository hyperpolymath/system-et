{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- The two-point information-flow lattice Low ≤ High as a grade
-- algebra, after the `Level` instance of
-- verification/proofs/lean4/Systemet/L2/Instances/Lattice.lean:
--   +  = meet      ·  = join      𝟘 = High (top)      𝟙 = Low (bottom)
--   a ≤ b  means  meet a b = a
module Wager.Grade.Level where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool.Base using (Bool; true; false)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.List.Base using (List; []; _∷_)

open import Wager.Grade.Algebra
open import Wager.Grade.Finite

data Sec : Type where
  low high : Sec

meet : Sec → Sec → Sec
meet high b = b
meet low  _ = low

join : Sec → Sec → Sec
join low  b = b
join high _ = high

private
  eqL : Sec → Sec → Bool
  eqL low  low  = true
  eqL high high = true
  eqL _    _    = false

  eqL-sound : ∀ a b → eqL a b ≡ true → a ≡ b
  eqL-sound low  low  _ = refl
  eqL-sound high high _ = refl
  eqL-sound low  high p = ⊥.rec (false≢true p)
  eqL-sound high low  p = ⊥.rec (false≢true p)

finLevel : Finite Sec
finLevel = record
  { elems    = low ∷ high ∷ []
  ; complete = λ { P h low → &&-l (P low) h ; P h high → &&-l (P high) (&&-r (P low) h) }
  ; _==_     = eqL
  ; ==-sound = eqL-sound }

-- The lattice order as a Boolean: meet a b = a.
levelB : BoolOps Sec
levelB = record
  { add = meet ; mul = join ; zero = high ; one = low
  ; leB = λ a b → eqL (meet a b) a }

levelOps : GradeOps Sec
levelOps = toOps levelB

levelLaws : GradeLaws levelOps
levelLaws = Check.mkLaws finLevel levelB
  refl refl refl refl refl refl refl refl refl refl refl refl refl refl refl

level : GradeAlgebra Sec
level = record { ops = levelOps ; laws = levelLaws }
