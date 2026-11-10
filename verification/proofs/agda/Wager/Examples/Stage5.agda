{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- DESIGN-CHOICES.adoc, DC-0.3: matches on kinded syntax.
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- Stage 5 anti-vacuity examples for T6. The source signature is
-- `taggedS rep` of Wager.FC.Tagged, the state scheme is the row scheme,
-- and the term grades are the one-point algebra.
--
--   type family F a where { F Int = Bool ; F Age = Char ; F (Tag a) = G a }
--   type family G a where { G Int = Bool ; G Bool = Char }
module Wager.Examples.Stage5 where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Sigma using (_×_; _,_)
open import Cubical.Data.Sum.Base using (inl; inr)
open import Cubical.Relation.Nullary using (¬_)

open import Wager.Grade.Trivial
open import Wager.Role.Role
open import Wager.FC.Tagged
import Wager.FC.Types
import Wager.FC.Coercion
import Wager.FC.Term
import Wager.Trans.Scheme
import Wager.Trans.Target
import Wager.Trans.Coercion
import Wager.L1.Normal
import Wager.L1.Eval
import Wager.L1.Conversion
import Wager.L2.Typing
open import Wager.Examples.Stage3 using (module Role-Check)
open import Wager.Proofs

private
  SS = taggedS rep
  Sc = Wager.Trans.Scheme.rowScheme SS

open Wager.FC.Types SS
open Wager.FC.Coercion SS
open Wager.FC.Term SS
open TTypes rep
open Role-Check using (wr-rep)
open Wager.Trans.Target SS Sc trivialOps using (tSig; tTSig; T; idx; Idx; Ty; ★; []; capp; base)
open Wager.Trans.Coercion SS Sc trivialOps using (tr; lit)
open Wager.L1.Normal tSig using (Nf; nbase; ncapp)
open Wager.L1.Eval tSig using (nf)
open Wager.L1.Conversion tSig using (DefEq)
open Wager.L2.Typing tSig tTSig trivialOps using (_▸_⊢_∶_)

private
  sUnit : STy
  sUnit = sbase bUnit

------------------------------------------------------------------------
-- Accepted: one nominal coercion for each kind of equation, and the
-- instance of T6 for it.

-- F Int = Bool (a base type).
f-int : Co nom (F sInt) sBool
f-int = c-fbase fE bInt

f-int-nf : nf (T (F sInt)) ≡ nf (T sBool)
f-int-nf = t6 SS Sc trivialOps f-int

-- F Age = Char (a newtype with no parameter).
f-age : Co nom (F sAge) sChar
f-age = c-fnt₀ fE ageE

f-age-nf : nf (T (F sAge)) ≡ nf (T sChar)
f-age-nf = t6 SS Sc trivialOps f-age

-- F (Tag Int) = G Int = Bool (the function looks at the argument of Tag).
f-tag-int : Co nom (F (Tag sInt)) sBool
f-tag-int = c-trans (c-fnt₁ fE tagE sInt) (c-fbase gE bInt)

f-tag-int-nf : nf (T (F (Tag sInt))) ≡ nf (T sBool)
f-tag-int-nf = t6 SS Sc trivialOps f-tag-int

-- F (Int → Int) = Unit (a function type).
f-arr : Co nom (F (sInt ⇒ˢ sInt)) sUnit
f-arr = c-farr fE sInt sInt

f-arr-nf : nf (T (F (sInt ⇒ˢ sInt))) ≡ nf (T sUnit)
f-arr-nf = t6 SS Sc trivialOps f-arr

-- Congruence: T (F Age) ~N T Char, below the nominal newtype T.
tee-cong : Co nom (Tee (F sAge)) (Tee sChar)
tee-cong = c-nt₁ teeE f-age

tee-cong-defeq : DefEq (T (Tee (F sAge))) (T (Tee sChar))
tee-cong-defeq = t6-conversion SS Sc trivialOps tee-cong

-- The normal form is the value that the source function computes.
f-tag-int-value : nf (T (F (Tag sInt))) ≡ nbase bBool
f-tag-int-value = refl

------------------------------------------------------------------------
-- Accepted (T6-No-Term): a cast along a nominal coercion leaves no
-- term. The literal 'c' : Char, cast to the type `F Age`, translates to
-- the literal. The translation is typed at the translated type `F Age`:
-- the type changes by conversion.

charAsFAge : STm ∅ˢ (F sAge)
charAsFAge = cast (c-sub (c-sym f-age)) (slit ℓchar)

no-term : tr charAsFAge ≡ lit ℓchar
no-term = t6-no-term SS Sc trivialOps {Γ = ∅ˢ} (c-sym f-age) (slit ℓchar)

typed-by-conversion : (λ _ → tt) ▸ (λ i → T (∅ˢ i)) ⊢ tr charAsFAge ∶ T (F sAge)
typed-by-conversion = t5-typing SS Sc trivial wr-rep tt tt charAsFAge

------------------------------------------------------------------------
-- Rejected: types with no nominal coercion, and their translations
-- have different normal forms. T6 is thus not true for an empty reason.

private
  IsCapp : Nf [] ★ → Type
  IsCapp (ncapp c a) = Unit
  IsCapp _           = ⊥

  IsBoolNf : Nf [] ★ → Type
  IsBoolNf (nbase bBool) = Unit
  IsBoolNf _             = ⊥

  IsAgeV : VTy → Type
  IsAgeV (vnt₀ ageE) = Unit
  IsAgeV _           = ⊥

  IsTagCharV : VTy → Type
  IsTagCharV (vnt₁ tagE (vbase bChar)) = Unit
  IsTagCharV _                         = ⊥

-- Age and Int: no nominal coercion in the source ...
age-int-rejected : ¬ Co nom sAge sInt
age-int-rejected γ = subst IsAgeV (source-nominal-soundness SS _ _ γ) tt

-- ... and two different normal forms in the target.
age-int-nf-differ : ¬ (nf (T sAge) ≡ nf (T sInt))
age-int-nf-differ p = subst IsCapp p tt

-- F Int is Bool and F Age is Char.
f-int-age-nf-differ : ¬ (nf (T (F sInt)) ≡ nf (T (F sAge)))
f-int-age-nf-differ p = subst IsBoolNf p tt

------------------------------------------------------------------------
-- A finding: the converse of T6 is false for the row scheme. `Tag Char`
-- and `Tag Unit` have no nominal coercion in the source. No type-level
-- function tells them apart, so they have one row, one state and one
-- target type.

tag-char-unit-rejected : ¬ Co nom (Tag sChar) (Tag sUnit)
tag-char-unit-rejected γ = subst IsTagCharV (source-nominal-soundness SS _ _ γ) tt

private
  same-row : idx tagE (vbase bChar) ≡ idx tagE (vbase bUnit)
  same-row = funExt λ { fE → refl ; gE → refl }

  tagAt : Idx → Ty [] ★
  tagAt i = capp (inr (tagE , i)) (base bInt)

tag-char-unit-one-type : T (Tag sChar) ≡ T (Tag sUnit)
tag-char-unit-one-type =
  cong tagAt same-row

-- The two source types do have a representational coercion: the
-- parameter of Tag is phantom.
tag-char-unit-rep : Co rep (Tag sChar) (Tag sUnit)
tag-char-unit-rep = c-nt₁ tagE c-ph
