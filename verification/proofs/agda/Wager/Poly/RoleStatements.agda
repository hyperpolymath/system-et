{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- Stage 8. The role of a type variable: the statements, frozen before
-- their proofs.
--
-- This file imports the definitions `LR` and `EnvLR` of the logical
-- relation from `Wager.Role.Noninterference`. It uses no lemma of that
-- module.
open import Cubical.Foundations.Prelude
open import Wager.Role.Signature
open import Wager.Role.Table

module Wager.Poly.RoleStatements (RS : RoleSig) where

open import Cubical.Data.Bool.Base using (true)
open import Wager.Role.Role
import Wager.L1.Syntax
import Wager.L1.Eval
import Wager.L1.Kinding
import Wager.Role.RepEq
import Wager.Role.Validity
import Wager.Role.Noninterference

-- For each composition table T.
module ForTable (T : RoleTable) where
  open RoleTable T using (mul)
  open Wager.L1.Syntax (toSig RS)
  open Wager.L1.Eval (toSig RS)
  open Wager.L1.Kinding (toSig RS) (tableOps T)
  open Wager.Role.Validity RS mul
  open Wager.Role.Noninterference RS T using (EnvLR)

  -- T8-Role. Noninterference for an open type. Let the signature
  -- respect its declared grades. Let A be a type in a context Δ of
  -- type variables, and let kinding accept the usage vector γ for A.
  -- Let two closed instantiations give each variable x two types that
  -- the observer `ρ · γ x` cannot tell apart. Then the observer ρ
  -- cannot tell the two instances of A apart.
  T8-Role : Type
  T8-Role =
    Valid →
    ∀ {Δ} {γ : KUsage Δ} {A : Ty Δ ★} → γ ⊢ᵏ A →
    (ρ : Role) (s s' : TySub [] Δ) →
    EnvLR ρ γ (λ k x → eval (s k x) idEnv) (λ k x → eval (s' k x) idEnv) →
    R★ ρ (nf (sub s A)) (nf (sub s' A))

-- The lawful table, and one type variable of the kind ★.
module Lawful where
  open Wager.L1.Syntax (toSig RS)
  open Wager.L1.Eval (toSig RS)
  open Wager.L1.Kinding (toSig RS) (tableOps tableZ)
  open Wager.Role.RepEq RS
  open Wager.Role.Validity RS mulZ

  -- T8-Role-Representational. A type variable at a grade that is at
  -- most representational: two instances at equivalent types are
  -- equivalent.
  T8-Role-Representational : Type
  T8-Role-Representational =
    Valid →
    ∀ {r : Role} {A : Ty (★ ∷ []) ★} → (0ᵏ ▹ᵏ r) ⊢ᵏ A →
    leR r rep ≡ true →
    (B C : Ty [] ★) → nf B ≈ nf C → nf (A [ B ]) ≈ nf (A [ C ])

  -- T8-Role-Phantom. A type variable at the grade phantom: each two
  -- instances have one normal form.
  T8-Role-Phantom : Type
  T8-Role-Phantom =
    Valid →
    ∀ {A : Ty (★ ∷ []) ★} → (0ᵏ ▹ᵏ ph) ⊢ᵏ A →
    (B C : Ty [] ★) → nf (A [ B ]) ≡ nf (A [ C ])

  -- T8-Role-Nominal. A type variable at the grade nominal: two
  -- instances at types with one normal form have one normal form. No
  -- kinding hypothesis is needed.
  T8-Role-Nominal : Type
  T8-Role-Nominal =
    ∀ (A : Ty (★ ∷ []) ★) (B C : Ty [] ★) →
    nf B ≡ nf C → nf (A [ B ]) ≡ nf (A [ C ])
