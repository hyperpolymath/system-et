{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- Stage 8. The role of a type variable: proofs.
--
-- The fundamental lemma of Stage 2 (`Wager.Role.Noninterference.fund`)
-- is about a type in a context. Stage 2 used it at the empty context.
-- Here it is used at a context of type variables. The link between an
-- instance `sub s A` and the evaluation of A is the lemma `eval-sub`
-- of Stage 1.
open import Cubical.Foundations.Prelude
open import Wager.Role.Signature
open import Wager.Role.Table

module Wager.Poly.Role (RS : RoleSig) where

open import Cubical.Data.Unit using (tt)
open import Wager.Role.Role
open import Wager.L1.Syntax (toSig RS)
open import Wager.L1.Eval (toSig RS)
open import Wager.L1.Completeness (toSig RS) using (eval-sub; envExt)
import Wager.L1.Kinding
import Wager.Role.Noninterference
open import Wager.Poly.RoleStatements RS

private
  -- The instance of A is the value of A in the environment of the
  -- values of the substitution.
  nf-sub : ∀ {Δ} (A : Ty Δ ★) (s : TySub [] Δ) →
           nf (sub s A) ≡ eval A (λ k x → eval (s k x) idEnv)
  nf-sub A s = eval-sub A s {ρ = idEnv} {ρ' = idEnv} (λ k ())

module ForTableProofs (T : RoleTable) where
  open ForTable T
  open Wager.Role.Noninterference RS T
  open import Wager.Role.Validity RS (RoleTable.mul T) using (R★)

  t8-role : T8-Role
  t8-role V {A = A} d ρ s s' e =
    subst2 (R★ ρ) (sym (nf-sub A s)) (sym (nf-sub A s')) (fund V d ρ e)

module LawfulProofs where
  open Lawful
  open ForTableProofs tableZ
  open Wager.L1.Kinding (toSig RS) (tableOps tableZ)
  open Wager.Role.Noninterference RS tableZ using (LR; R★-anti)

  private
    -- The two instantiations of one type variable, as two environments
    -- that an observer cannot tell apart at the grade r.
    one-var : ∀ (ρ r : Role) (B C : Ty [] ★) → LR (mulZ ρ r) ★ (nf B) (nf C) →
              ∀ k (x : Var (★ ∷ []) k) →
              LR (mulZ ρ ((0ᵏ ▹ᵏ r) k x)) k
                 (eval ((B ∷ₛ ids) k x) idEnv) (eval ((C ∷ₛ ids) k x) idEnv)
    one-var ρ r B C h k vz = h

  t8-role-representational : T8-Role-Representational
  t8-role-representational V {r} d le B C h =
    t8-role V d rep (B ∷ₛ ids) (C ∷ₛ ids)
      (one-var rep r B C (R★-anti r rep le h))

  -- The proof uses the entry nominal · phantom = phantom of the lawful
  -- table.
  t8-role-phantom : T8-Role-Phantom
  t8-role-phantom V d B C =
    t8-role V d nom (B ∷ₛ ids) (C ∷ₛ ids) (one-var nom ph B C tt)

  t8-role-nominal : T8-Role-Nominal
  t8-role-nominal A B C h =
    nf-sub A (B ∷ₛ ids)
    ∙ cong (eval A) (envExt pt)
    ∙ sym (nf-sub A (C ∷ₛ ids))
    where
    pt : ∀ k (x : Var (★ ∷ []) k) →
         eval ((B ∷ₛ ids) k x) idEnv ≡ eval ((C ∷ₛ ids) k x) idEnv
    pt k vz = h
