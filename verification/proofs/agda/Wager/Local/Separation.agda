{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- DESIGN-CHOICES.adoc, DC-0.3: matches on typing derivations of the
-- untyped calculus.
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- T7, the separation (Stage 6): the target cannot type the GADT
-- program `gadt-eval b α`.
--
-- The proof has two steps.
--
--   1. The erasure of the program has no simple type of the form
--      `(p + p) → b`, for a base type b (`no-simple-type`). The first
--      branch uses the value at the type b. The second branch uses the
--      same value at a sum type. A simple type cannot do the two.
--   2. A typed target term erases to a term with a simple type
--      (`Wager.L2.Erasure.erase-typed`).
--
-- In the source calculus the two branches have two local equality
-- assumptions, so each branch has its type.
open import Wager.L1.Signature
open import Wager.Grade.Algebra
import Wager.L2.Signature

module Wager.Local.Separation
  (S : Sig) (TS : Wager.L2.Signature.TSig S) (ops : GradeOps (Sig.TG S)) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.FinData.Base using (Fin; zero; suc)

open import Wager.L1.Syntax S
open import Wager.L2.Typing S TS ops
open import Wager.L2.Erasure S TS ops
open import Wager.Erased.Untyped
open Typing litTy
open import Wager.Local.Source Base Lit litTy
open import Wager.Local.Gadt Base Lit litTy

private
  variable
    n : ℕ

  -- The two sides of an erased sum type.
  lft rgt : ETy Base → ETy Base
  lft (esum a c)  = a
  lft (ebase x)   = ebase x
  lft (earr a c)  = earr a c
  lft (eprod a c) = eprod a c
  rgt (esum a c)  = c
  rgt (ebase x)   = ebase x
  rgt (earr a c)  = earr a c
  rgt (eprod a c) = eprod a c

  IsBase : ETy Base → Type
  IsBase (ebase x)   = Unit
  IsBase (earr a c)  = ⊥
  IsBase (eprod a c) = ⊥
  IsBase (esum a c)  = ⊥

-- The erased program, written out. Agda checks by computation that it
-- is the erasure of `gadt-eval b α`, for each b and each α.
gadt-evalᵘ : UTm 0
gadt-evalᵘ =
  ulam (ucase (uvar zero)
    (uapp (ulam (uvar zero)) (uvar zero))
    (uapp (ulam (ucase (uvar zero) (uvar zero) (uvar zero))) (uvar zero)))

erased-program : ∀ b α → eraseˡ (gadt-eval b α) ≡ gadt-evalᵘ
erased-program b α = refl

-- Step 1.
no-simple-type : ∀ {Δ : ECx 0} {p} b →
                 Δ ⊢ᵉ gadt-evalᵘ ∶ earr (esum p p) (ebase b) → ⊥
no-simple-type b
  (u-lam (u-case (u-var zero e₀)
    (u-app (u-lam (u-var zero f₁)) (u-var zero f₂))
    (u-app (u-lam (u-case (u-var zero e₁) _ _)) (u-var zero e₂)))) =
  subst IsBase
    -- the type b, read from the first branch, is a sum in the second
    (sym (f₂ ∙ f₁) ∙ sym (cong lft e₀) ∙ cong rgt e₀ ∙ e₂ ∙ e₁) tt

-- T7, THE SEPARATION.
separation :
  (b : Base) (α : LTy) {γ : Usage 0} {Γ : Cx 0} {t : Tm 0} {A : Ty [] ★} →
  γ ▸ Γ ⊢ t ∶ A →
  erT A ≡ erˡ (G b α ⇒ˡ lbase b) →
  eraseᵗ t ≡ eraseˡ (gadt-eval b α) →
  ⊥
separation b α d eA eT =
  no-simple-type b (subst2 (λ u a → _ ⊢ᵉ u ∶ a) eT eA (erase-typed d))
