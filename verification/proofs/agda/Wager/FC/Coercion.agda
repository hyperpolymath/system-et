{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- Coercions of the source calculus (Stage 3).
--
-- `Co r τ σ` is a proof term for the equality of τ and σ at the role r:
--   nom   nominal equality (the equality of the type checker);
--   rep   representational equality (the two types have one
--         representation), the equality that `coerce` uses;
--   ph    phantom equality (each two types are equal at this role).
--
-- The rules follow Breitner et al.: reflexivity, symmetry,
-- transitivity, the rule from nominal to representational, the phantom
-- rule, role-gated congruence, the newtype rules and the rules of the
-- type-level functions.
--
-- This relation belongs to the SOURCE calculus. The target calculus of
-- the wager has no such relation.
open import Wager.FC.Signature

module Wager.FC.Coercion (SS : SSig) where

open import Cubical.Foundations.Prelude

open import Wager.Role.Role
open import Wager.FC.Types SS

private
  variable
    r : Role
    τ τ' σ σ' υ : STy

data Co : Role → STy → STy → Type where
  c-refl  : Co nom τ τ
  c-sym   : Co r τ σ → Co r σ τ
  c-trans : Co r τ σ → Co r σ υ → Co r τ υ
  -- Nominal equality gives representational equality.
  c-sub   : Co nom τ σ → Co rep τ σ
  -- Each two types are equal at the role phantom.
  c-ph    : Co ph τ σ

  -- Role-gated congruence. The parameters of a function, a pair and a
  -- sum are representational.
  c-arr   : Co r τ τ' → Co r σ σ' → Co r (τ ⇒ˢ σ) (τ' ⇒ˢ σ')
  c-prod  : Co r τ τ' → Co r σ σ' → Co r (τ ×ˢ σ) (τ' ×ˢ σ')
  c-sum   : Co r τ τ' → Co r σ σ' → Co r (τ +ˢ σ) (τ' +ˢ σ')
  -- A newtype with the declared role `role N`. The premise has the
  -- role `mulG r (role N)`, with the composition table of GHC:
  --   at nom the arguments are equal at nom (also for a phantom parameter);
  --   at rep the arguments are equal at the declared role;
  --   at ph there is no condition.
  c-nt₁   : (N : N₁) → Co (mulG r (role N)) τ σ → Co r (nt₁ N τ) (nt₁ N σ)
  -- The parameter of a type-level function is nominal.
  c-fam   : (F : Fam) → Co nom τ σ → Co nom (fam F τ) (fam F σ)

  -- Newtype rules: a newtype is representationally equal to its
  -- representation.
  c-ax₀   : (N : N₀) → Co rep (nt₀ N) (embE (rep₀ N))
  c-ax₁   : (N : N₁) (τ : STy) → Co rep (nt₁ N τ) (inst (body N) τ)

  -- The equations of a type-level function, by the head of the argument.
  c-fbase : (F : Fam) (b : Base) → Co nom (fam F (sbase b)) (sbase (fBase F b))
  c-fnt₀  : (F : Fam) (N : N₀) → Co nom (fam F (nt₀ N)) (sbase (fNt₀ F N))
  c-fnt₁  : (F : Fam) (N : N₁) (τ : STy) →
            Co nom (fam F (nt₁ N τ)) (resS (fNt₁ F N) τ)
  c-farr  : (F : Fam) (τ σ : STy) → Co nom (fam F (τ ⇒ˢ σ)) (sbase (fOther F))
  c-fprod : (F : Fam) (τ σ : STy) → Co nom (fam F (τ ×ˢ σ)) (sbase (fOther F))
  c-fsum  : (F : Fam) (τ σ : STy) → Co nom (fam F (τ +ˢ σ)) (sbase (fOther F))
