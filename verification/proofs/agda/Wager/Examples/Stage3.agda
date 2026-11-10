{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- DESIGN-CHOICES.adoc, DC-0.3: matches on typing derivations.
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- Stage 3 anti-vacuity examples. Each theorem of Stage 3 has one closed
-- example that satisfies the hypotheses, and one closed example that
-- the source calculus rejects. The examples for the classic program are
-- statements, and they are in Wager.Proofs. This file has the others.
--
-- The signature of this file:
--
--   newtype Age   = MkAge Int
--   newtype Box a = MkBox (a, Int)      -- inferred role: representational
--   newtype Tag a = MkTag Int           -- inferred role: phantom
--   newtype T a   = MkT (F a)           -- inferred role: nominal
--   type family F a where { F Int = Bool ; F Age = Char ; F (Tag a) = G a }
--   type family G a where { G Int = Bool ; G Bool = Char }
--
-- The signature is `taggedS d` of Wager.FC.Tagged: d is the declared role
-- of the parameter of Box. Tag is declared phantom and T is declared nominal.
module Wager.Examples.Stage3 where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool.Base using (true; false)
open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.FinData.Base using (Fin; zero; suc)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Sum.Base using (_⊎_; inl; inr)
open import Cubical.Relation.Nullary using (¬_)

open import Wager.Grade.Finite using (false≢true)
open import Wager.Role.Role
open import Wager.FC.Signature
open import Wager.FC.Tagged
open import Wager.Erased.Untyped
import Wager.FC.Types
import Wager.FC.Coercion
import Wager.FC.Term
import Wager.FC.RoleSoundness
import Wager.FC.Erasure
open import Wager.Proofs


------------------------------------------------------------------------
-- The role check.

module Role-Check where

  -- Accepted: Box declared representational (the inferred role).
  wr-rep : SSig.WellRoled (taggedS rep)
  wr-rep boxE = refl
  wr-rep tagE = refl
  wr-rep teeE = refl

  -- Accepted: Box declared nominal (a declared role above the inferred role).
  wr-nom : SSig.WellRoled (taggedS nom)
  wr-nom boxE = refl
  wr-nom tagE = refl
  wr-nom teeE = refl

  -- Rejected: Box declared phantom.
  wr-ph-rejected : ¬ SSig.WellRoled (taggedS ph)
  wr-ph-rejected wr = false≢true (wr boxE)

------------------------------------------------------------------------
-- Coercions, in the signature with Box declared representational.

private
  SS = taggedS rep

open Wager.FC.Types SS
open Wager.FC.Coercion SS
open Wager.FC.Term SS
open Wager.FC.RoleSoundness SS
open Typing litTy
open Role-Check using (wr-rep)
open TTypes rep renaming (Tee to T)


private
  IsInt : BaseName → Type
  IsInt bInt = Unit
  IsInt _    = ⊥

  IsBool : BaseName → Type
  IsBool bBool = Unit
  IsBool _     = ⊥

  IsEInt : ETy BaseName → Type
  IsEInt (ebase b) = IsInt b
  IsEInt _         = ⊥

  IsEChar : ETy BaseName → Type
  IsEChar (ebase bChar) = Unit
  IsEChar _             = ⊥

  IsVBool : VTy → Type
  IsVBool (vbase b) = IsBool b
  IsVBool _         = ⊥

  IsTagInt : VTy → Type
  IsTagInt (vnt₁ tagE (vbase b)) = IsInt b
  IsTagInt _                     = ⊥

module Role-Soundness-Examples where

  -- Accepted: Box Age ~R Box Int, by congruence at the role
  -- representational and the newtype rule for Age.
  box-co : Co rep (Box sAge) (Box sInt)
  box-co = c-nt₁ boxE (c-ax₀ ageE)

  -- The instance of Source-Role-Soundness for this coercion.
  box-er : er (Box sAge) ≡ er (Box sInt)
  box-er = source-role-soundness SS wr-rep _ _ box-co

  -- Accepted: Tag Int ~R Tag Bool, because the parameter of Tag is phantom.
  tag-co : Co rep (Tag sInt) (Tag sBool)
  tag-co = c-nt₁ tagE c-ph

  -- Rejected: there is no coercion Int ~R Bool.
  int-bool-rejected : ¬ Co rep sInt sBool
  int-bool-rejected γ = subst IsEInt (source-role-soundness SS wr-rep _ _ γ) tt

  -- Rejected: there is no coercion T Age ~R T Int. The erased types are
  -- Char and Bool.
  tee-rejected : ¬ Co rep (T sAge) (T sInt)
  tee-rejected γ = subst IsEChar (source-role-soundness SS wr-rep _ _ γ) tt

module Nominal-Soundness-Examples where

  -- Accepted: F (Tag Int) ~N Bool, with the equations F (Tag a) = G a
  -- and G Int = Bool.
  f-tag-int : Co nom (F (Tag sInt)) sBool
  f-tag-int = c-trans (c-fnt₁ fE tagE sInt) (c-fbase gE bInt)

  f-tag-bool : Co nom (F (Tag sBool)) sChar
  f-tag-bool = c-trans (c-fnt₁ fE tagE sBool) (c-fbase gE bBool)

  -- The instance of Source-Nominal-Soundness.
  f-tag-int-ev : ev (F (Tag sInt)) ≡ ev sBool
  f-tag-int-ev = source-nominal-soundness SS _ _ f-tag-int

  -- Rejected: Tag Int and Tag Bool are NOT nominally equal. The
  -- parameter of Tag is phantom, but a newtype is generative.
  tag-nominal-rejected : ¬ Co nom (Tag sInt) (Tag sBool)
  tag-nominal-rejected γ = subst IsTagInt (source-nominal-soundness SS _ _ γ) tt

  -- Rejected: F (Tag Int) and F (Tag Bool) are not nominally equal.
  -- A type-level function sees the argument of a phantom parameter.
  -- (Stage 4 uses this example.)
  f-sees-phantom : ¬ Co nom (F (Tag sInt)) (F (Tag sBool))
  f-sees-phantom γ = subst IsVBool (source-nominal-soundness SS _ _ γ) tt

------------------------------------------------------------------------
-- Terms, erasure and evaluation.

module Term-Examples where
  open Role-Soundness-Examples

  -- MkAge 5 : Age   (the constructor of a newtype is a cast)
  anAge : STm ∅ˢ sAge
  anAge = cast (c-sym (c-ax₀ ageE)) (slit ℓint)

  -- MkBox (MkAge 5, 7) : Box Age
  aBox : STm ∅ˢ (Box sAge)
  aBox = cast (c-sym (c-ax₁ boxE sAge)) (spair anAge (slit ℓint))

  -- coerce (MkBox (MkAge 5, 7)) : Box Int
  prog : STm ∅ˢ (Box sInt)
  prog = sapp (coerce box-co) aBox

  -- Accepted (Cast-Vanishes, Coerce-Erases-To-Identity): the erased
  -- program has no cast and no newtype constructor.
  prog-erased : eraseTm prog ≡ uapp (ulam (uvar zero)) (upair (ulit ℓint) (ulit ℓint))
  prog-erased = refl

  -- Rejected: a function that is not a coercion does not erase to the
  -- identity function.
  private
    IsId : ∀ {n} → UTm n → Type
    IsId (ulam (uvar zero)) = Unit
    IsId _                  = ⊥

  const-not-identity : ¬ (eraseTm (slam {τ = sInt} {Γ = ∅ˢ} (slit ℓint)) ≡ ulam (uvar zero))
  const-not-identity p = subst IsId (sym p) tt

  -- Accepted: the erased program evaluates to the pair of the two literals.
  prog-value : ∅ᵉ ⊢ eraseTm prog ⇓ vpair (vlit ℓint) (vlit ℓint)
  prog-value = ⇓-app ⇓-lam (⇓-pair ⇓-lit ⇓-lit) (⇓-var zero)

  -- Accepted (Erasure-Preserves-Typing): the erased program has the
  -- erased type of `Box Int`, the pair type (Int, Int).
  prog-typed : (λ i → er (∅ˢ i)) ⊢ᵉ eraseTm prog ∶ eprod (ebase bInt) (ebase bInt)
  prog-typed = erasure-preserves-typing SS wr-rep prog

  -- Rejected: an untyped term with no erased type (a literal in the
  -- position of a function).
  stuck-untyped : ∀ {a} → ¬ (∅ᶜ ⊢ᵉ uapp (ulit ℓint) (ulit ℓint) ∶ a)
  stuck-untyped (u-app () _)

  -- The binding order of `sletp` agrees in typing and in evaluation:
  -- index 1 is the first component.
  first : STm ∅ˢ sInt
  first = sletp (spair (slit ℓint) (slit ℓbool)) (svar (suc zero))

  first-value : ∅ᵉ ⊢ eraseTm first ⇓ vlit ℓint
  first-value = ⇓-letp (⇓-pair ⇓-lit ⇓-lit) (⇓-var (suc zero))

  -- A sum and a case: the left branch is taken.
  pick : STm ∅ˢ sInt
  pick = scase (sinl {σ = sBool} (slit ℓint)) (svar zero) (slit ℓint)

  pick-value : ∅ᵉ ⊢ eraseTm pick ⇓ vlit ℓint
  pick-value = ⇓-casel (⇓-inl ⇓-lit) (⇓-var zero)
