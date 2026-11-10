{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- A finding of Stage 2, outside T1: a 4-point role structure.
--
-- The 3-point structures use one grade, `phantom`, for two notions:
-- "the variable does not occur" and "the variable occurs, and its
-- representation does not matter". This structure has two grades:
--   absent   the variable does not occur         (this is 𝟘)
--   phantom  it occurs in phantom positions only
-- With `absent` as 𝟘, the GHC rule `nominal · phantom = nominal` and
-- all 15 law fields hold together.
module Wager.Role.Role4 where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool.Base using (Bool; true; false)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.List.Base using (List; []; _∷_)

open import Wager.Grade.Algebra
open import Wager.Grade.Finite

data Role4 : Type where
  ab ph4 rep4 nom4 : Role4

-- The order: ab ≤ ph4 ≤ rep4 ≤ nom4.
le4 : Role4 → Role4 → Bool
le4 ab   _    = true
le4 ph4  ab   = false
le4 ph4  _    = true
le4 rep4 ab   = false
le4 rep4 ph4  = false
le4 rep4 _    = true
le4 nom4 nom4 = true
le4 nom4 _    = false

max4 : Role4 → Role4 → Role4
max4 ab   b    = b
max4 ph4  ab   = ph4
max4 ph4  b    = b
max4 rep4 ab   = rep4
max4 rep4 ph4  = rep4
max4 rep4 b    = b
max4 nom4 _    = nom4

-- Composition: `absent` absorbs on both sides. On the other grades it
-- is the GHC table.
mul4 : Role4 → Role4 → Role4
mul4 ab   _  = ab
mul4 _    ab = ab
mul4 ph4  _  = ph4
mul4 rep4 b  = b
mul4 nom4 _  = nom4

private
  eq4 : Role4 → Role4 → Bool
  eq4 ab   ab   = true
  eq4 ph4  ph4  = true
  eq4 rep4 rep4 = true
  eq4 nom4 nom4 = true
  eq4 _    _    = false

  eq4-sound : ∀ a b → eq4 a b ≡ true → a ≡ b
  eq4-sound ab   ab   _ = refl
  eq4-sound ph4  ph4  _ = refl
  eq4-sound rep4 rep4 _ = refl
  eq4-sound nom4 nom4 _ = refl
  eq4-sound ab   ph4  p = ⊥.rec (false≢true p)
  eq4-sound ab   rep4 p = ⊥.rec (false≢true p)
  eq4-sound ab   nom4 p = ⊥.rec (false≢true p)
  eq4-sound ph4  ab   p = ⊥.rec (false≢true p)
  eq4-sound ph4  rep4 p = ⊥.rec (false≢true p)
  eq4-sound ph4  nom4 p = ⊥.rec (false≢true p)
  eq4-sound rep4 ab   p = ⊥.rec (false≢true p)
  eq4-sound rep4 ph4  p = ⊥.rec (false≢true p)
  eq4-sound rep4 nom4 p = ⊥.rec (false≢true p)
  eq4-sound nom4 ab   p = ⊥.rec (false≢true p)
  eq4-sound nom4 ph4  p = ⊥.rec (false≢true p)
  eq4-sound nom4 rep4 p = ⊥.rec (false≢true p)

finRole4 : Finite Role4
finRole4 = record
  { elems    = ab ∷ ph4 ∷ rep4 ∷ nom4 ∷ []
  ; complete = λ { P h ab   → &&-l (P ab) h
                 ; P h ph4  → &&-l (P ph4) (&&-r (P ab) h)
                 ; P h rep4 → &&-l (P rep4) (&&-r (P ph4) (&&-r (P ab) h))
                 ; P h nom4 → &&-l (P nom4) (&&-r (P rep4) (&&-r (P ph4) (&&-r (P ab) h))) }
  ; _==_     = eq4
  ; ==-sound = eq4-sound }

role4B : BoolOps Role4
role4B = record { add = max4 ; mul = mul4 ; zero = ab ; one = rep4 ; leB = le4 }

role4Ops : GradeOps Role4
role4Ops = toOps role4B

-- All 15 law fields hold.
role4Laws : GradeLaws role4Ops
role4Laws = Check.mkLaws finRole4 role4B
  refl refl refl refl refl refl refl refl refl refl refl refl refl refl refl

role4 : GradeAlgebra Role4
role4 = record { ops = role4Ops ; laws = role4Laws }

-- The GHC rule holds: a nominal position makes a phantom use nominal.
role4-ghc-rule : mul4 nom4 ph4 ≡ nom4
role4-ghc-rule = refl
