{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- Roles as a grade structure (theorem T1).
--
--   Role = { phantom, representational, nominal }
--   𝟘 = phantom        𝟙 = representational
--   +  = maximum in the order  phantom < representational < nominal
--   ·  = role composition (outer · inner)
--
-- There are two composition tables. They differ in one entry:
--   GHC table      nominal · phantom = nominal
--                  ("a nominal position makes everything below it nominal")
--   lawful table   nominal · phantom = phantom
module Wager.Role.Role where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool.Base using (Bool; true; false)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.List.Base using (List; []; _∷_)
open import Cubical.Relation.Nullary using (¬_)

open import Wager.Grade.Algebra
open import Wager.Grade.Finite

data Role : Type where
  ph rep nom : Role

-- The order: ph ≤ rep ≤ nom.
leR : Role → Role → Bool
leR ph  _   = true
leR rep ph  = false
leR rep _   = true
leR nom nom = true
leR nom _   = false

-- The join of two uses: the maximum.
maxR : Role → Role → Role
maxR ph  b   = b
maxR rep ph  = rep
maxR rep b   = b
maxR nom _   = nom

-- Composition, GHC table: an outer phantom gives phantom, an outer
-- representational gives the inner role, an outer nominal gives nominal.
mulG : Role → Role → Role
mulG ph  _ = ph
mulG rep b = b
mulG nom _ = nom

-- Composition, lawful table: the same, but nominal · phantom = phantom.
mulZ : Role → Role → Role
mulZ ph  _   = ph
mulZ rep b   = b
mulZ nom ph  = ph
mulZ nom _   = nom

private
  eqR : Role → Role → Bool
  eqR ph  ph  = true
  eqR rep rep = true
  eqR nom nom = true
  eqR _   _   = false

  eqR-sound : ∀ a b → eqR a b ≡ true → a ≡ b
  eqR-sound ph  ph  _ = refl
  eqR-sound rep rep _ = refl
  eqR-sound nom nom _ = refl
  eqR-sound ph  rep p = ⊥.rec (false≢true p)
  eqR-sound ph  nom p = ⊥.rec (false≢true p)
  eqR-sound rep ph  p = ⊥.rec (false≢true p)
  eqR-sound rep nom p = ⊥.rec (false≢true p)
  eqR-sound nom ph  p = ⊥.rec (false≢true p)
  eqR-sound nom rep p = ⊥.rec (false≢true p)

  IsNom : Role → Type
  IsNom nom = Unit
  IsNom _   = ⊥

nom≢ph : ¬ (nom ≡ ph)
nom≢ph p = subst IsNom p tt

nom≢rep : ¬ (nom ≡ rep)
nom≢rep p = subst IsNom p tt

finRole : Finite Role
finRole = record
  { elems    = ph ∷ rep ∷ nom ∷ []
  ; complete = λ { P h ph  → &&-l (P ph) h
                 ; P h rep → &&-l (P rep) (&&-r (P ph) h)
                 ; P h nom → &&-l (P nom) (&&-r (P rep) (&&-r (P ph) h)) }
  ; _==_     = eqR
  ; ==-sound = eqR-sound }

roleGB roleZB : BoolOps Role
roleGB = record { add = maxR ; mul = mulG ; zero = ph ; one = rep ; leB = leR }
roleZB = record { add = maxR ; mul = mulZ ; zero = ph ; one = rep ; leB = leR }

roleGOps roleZOps : GradeOps Role
roleGOps = toOps roleGB
roleZOps = toOps roleZB

------------------------------------------------------------------------
-- T1, lawful table: all 15 law fields hold.

roleZLaws : GradeLaws roleZOps
roleZLaws = Check.mkLaws finRole roleZB
  refl refl refl refl refl refl refl refl refl refl refl refl refl refl refl

roleZ : GradeAlgebra Role
roleZ = record { ops = roleZOps ; laws = roleZLaws }

------------------------------------------------------------------------
-- T1, GHC table: 14 law fields hold, and `mul-zero` fails.

roleGLaws14 : GradeLawsExceptMulZero roleGOps
roleGLaws14 = Check.mkLaws14 finRole roleGB
  refl refl refl refl refl refl refl refl refl refl refl refl refl refl

-- The Boolean check of `a · 𝟘 = 𝟘` computes to `false`.
roleG-mul-zero-check : Check.mul-zero? finRole roleGB ≡ false
roleG-mul-zero-check = refl

-- The law fails, and it fails at `nom` only.
roleG-mul-zero-fails : ¬ (∀ a → mulG a ph ≡ ph)
roleG-mul-zero-fails h = nom≢ph (h nom)

roleG-mul-zero-ph : mulG ph ph ≡ ph
roleG-mul-zero-ph = refl

roleG-mul-zero-rep : mulG rep ph ≡ ph
roleG-mul-zero-rep = refl

roleG-mul-zero-nom : ¬ (mulG nom ph ≡ ph)
roleG-mul-zero-nom = nom≢ph

------------------------------------------------------------------------
-- Facts about the order that do not depend on the composition table.

leR-refl : ∀ a → leR a a ≡ true
leR-refl = GradeLaws.le-refl roleZLaws

leR-trans : ∀ a b c → leR a b ≡ true → leR b c ≡ true → leR a c ≡ true
leR-trans = GradeLaws.le-trans roleZLaws

-- A use is below the join of two uses. This is NOT one of the 15 laws.
-- It holds because `+` is the maximum.
max-upper-l : ∀ a b → leR a (maxR a b) ≡ true
max-upper-l ph  b   = refl
max-upper-l rep ph  = refl
max-upper-l rep rep = refl
max-upper-l rep nom = refl
max-upper-l nom b   = refl

max-upper-r : ∀ a b → leR b (maxR a b) ≡ true
max-upper-r ph  b   = leR-refl b
max-upper-r rep ph  = refl
max-upper-r rep rep = refl
max-upper-r rep nom = refl
max-upper-r nom ph  = refl
max-upper-r nom rep = refl
max-upper-r nom nom = refl
