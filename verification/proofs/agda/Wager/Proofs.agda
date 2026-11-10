{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- One inhabitant for each statement of `Wager.Statements`.
-- The identifiers in this file are the identifiers that VERDICT.adoc
-- names.
module Wager.Proofs where

open import Cubical.Foundations.Prelude

open import Wager.Statements
open import Wager.Grade.Algebra
open import Wager.Grade.Affine using (affine)
open import Wager.Grade.Level using (level)
open import Wager.L1.Signature
import Wager.L1.Equality
import Wager.L2.Signature
import Wager.L2.Substitution
import Wager.L2.Preservation
import Wager.L2.Progress

------------------------------------------------------------------------
-- STAGE 1
------------------------------------------------------------------------

affine-is-grade-algebra : Affine-Is-Grade-Algebra
affine-is-grade-algebra = affine

level-is-grade-algebra : Level-Is-Grade-Algebra
level-is-grade-algebra = level

module _ (S : Sig) where
  open L1-Statements S
  open Wager.L1.Equality S

  l1-equality : L1-Equality
  l1-equality t u = defEq→nf , nf→defEq

module _ (S : Sig) (TS : Wager.L2.Signature.TSig S) (R : GradeAlgebra (Sig.TG S)) where
  open T0-Statements S TS R

  t0-substitution : T0-Substitution
  t0-substitution = Wager.L2.Substitution.subst-lemma S TS R

  t0-preservation : T0-Preservation
  t0-preservation = Wager.L2.Preservation.preservation S TS R

  -- Progress uses the operations only, and no law.
  t0-progress : T0-Progress
  t0-progress = Wager.L2.Progress.progress S TS (GradeAlgebra.ops R)

------------------------------------------------------------------------
-- STAGE 2
------------------------------------------------------------------------

open import Cubical.Data.Sigma using (_,_)
open import Wager.Role.Role
open import Wager.Role.Role4 using (role4Laws; role4-ghc-rule)
open import Wager.Role.Table
open import Wager.Role.Signature
import Wager.Role.Noninterference
import Wager.Role.Lawful
import Wager.Role.ClassicProofs as CP

module _ where
  open T1-Statements

  t1-lawful : T1-Lawful
  t1-lawful = roleZLaws

  t1-ghc-other-laws : T1-GHC-Other-Laws
  t1-ghc-other-laws = roleGLaws14

  t1-ghc-mul-zero-fails : T1-GHC-MulZero-Fails
  t1-ghc-mul-zero-fails = roleG-mul-zero-fails

  t1-ghc-fails-at-nominal-only : T1-GHC-Fails-At-Nominal-Only
  t1-ghc-fails-at-nominal-only =
    roleG-mul-zero-ph , roleG-mul-zero-rep , roleG-mul-zero-nom

module _ (RS : RoleSig) (T : RoleTable) where
  open Noninterference-Statements RS T

  noninterference : Noninterference
  noninterference = Wager.Role.Noninterference.noninterference RS T

module _ (RS : RoleSig) where
  open T2-Statements RS

  t2-representational : T2-Representational
  t2-representational = Wager.Role.Lawful.t2-representational RS

  t2-phantom : T2-Phantom
  t2-phantom = Wager.Role.Lawful.t2-phantom RS

module _ where
  open T4-Statements

  t4-kinding-rejects : T4-Kinding-Rejects
  t4-kinding-rejects = CP.T4.t4-kinding-rejects

  t4-not-equivalent : T4-Not-Equivalent
  t4-not-equivalent = CP.T4.t4-not-equivalent-1 , CP.T4.t4-not-equivalent-2

module _ where
  open Proxy-Statements

  lawful-unsound-with-phantom-constant : A.Lawful-Unsound-With-Phantom-Constant
  lawful-unsound-with-phantom-constant =
    (CP.LawfulKinding.ε ph , CP.ProxyA.deepF-phantom) , CP.Generic.deepF-separates ph ph

  t2-phantom-fails-without-valid : A.T2-Phantom-Fails-Without-Valid
  t2-phantom-fails-without-valid =
    (CP.LawfulKinding.ε ph , CP.ProxyA.proxyF-phantom) , CP.Generic.proxyF-separates ph ph

  phantom-constant-not-valid : A.Phantom-Constant-Not-Valid
  phantom-constant-not-valid = CP.ProxyA.not-valid

  rep-constant-valid : B.Rep-Constant-Valid
  rep-constant-valid = CP.ProxyB.valid

  no-phantom-coercion : B.No-Phantom-Coercion
  no-phantom-coercion = CP.ProxyB.no-phantom-coercion

  ghc-rejects-deep : C.GHC-Rejects-Deep
  ghc-rejects-deep = CP.ProxyC.ghc-rejects-deep

  ghc-rejects-unused-parameter : C.GHC-Rejects-Unused-Parameter
  ghc-rejects-unused-parameter =
    (CP.LawfulKinding.ε ph , CP.LawfulKinding.constF-phantom ph) , CP.ProxyC.ghc-rejects-unused

module _ where
  open Role4-Statements

  role4-lawful : Role4-Lawful
  role4-lawful = role4Laws

  role4-has-ghc-rule : Role4-Has-GHC-Rule
  role4-has-ghc-rule = role4-ghc-rule
