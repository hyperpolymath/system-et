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
open import Wager.FC.Signature
import Wager.FC.RoleSoundness
import Wager.FC.Erasure
import Wager.FC.ClassicProofs
import Wager.Trans.Scheme
import Wager.Trans.Typing
import Wager.Trans.Simulation
import Wager.Trans.RoleCorrespondence
import Wager.Trans.TwoStateProofs
import Wager.Trans.Nominal
import Wager.Local.Separation
import Wager.Identity.Family
import Wager.Identity.Soundness

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

------------------------------------------------------------------------
-- STAGE 3
------------------------------------------------------------------------

module _ (SS : SSig) where
  open Source-Statements SS
  private
    module RS = Wager.FC.RoleSoundness SS
    module ER = Wager.FC.Erasure SS

  source-nominal-soundness : Source-Nominal-Soundness
  source-nominal-soundness τ σ = RS.nom-sound

  source-role-soundness : Source-Role-Soundness
  source-role-soundness wr τ σ = RS.rep-sound wr

  cast-vanishes : Cast-Vanishes
  cast-vanishes γ e = refl

  coerce-erases-to-identity : Coerce-Erases-To-Identity
  coerce-erases-to-identity γ = refl

  erasure-preserves-typing : Erasure-Preserves-Typing
  erasure-preserves-typing wr = ER.erase-typing wr

module _ where
  open Classic-Source-Statements
  private module SP = Wager.FC.ClassicProofs

  classic-rejected : Classic-Rejected
  classic-rejected = SP.classic-rejected

  classic-bad-coercion : Bad.Classic-Bad-Coercion
  classic-bad-coercion = SP.Bad.tAge~tInt

  classic-unsound-if-accepted : Bad.Classic-Unsound-If-Accepted
  classic-unsound-if-accepted =
    SP.Bad.exploit , SP.Bad.exploit-erased , SP.Bad.exploit-value , SP.Bad.exploit-untyped

  classic-nominal-accepted : Good.Classic-Nominal-Accepted
  classic-nominal-accepted = SP.Good.accepted

  classic-nominal-no-coercion : Good.Classic-Nominal-No-Coercion
  classic-nominal-no-coercion = SP.Good.age~int , SP.Good.no-coercion

------------------------------------------------------------------------
-- STAGE 4
------------------------------------------------------------------------

module _ (SS : SSig) (Sc : Wager.Trans.Scheme.StateScheme SS)
         {R : Type} (A : GradeAlgebra R) where
  open Translation-Statements SS Sc A
  private
    module TY = Wager.Trans.Typing SS Sc A
    module SI = Wager.Trans.Simulation SS Sc (GradeAlgebra.ops A)
    module RC = Wager.Trans.RoleCorrespondence SS Sc (GradeAlgebra.ops A)

  coercion-is-a-term : Coercion-Is-A-Term
  coercion-is-a-term wr γ Γ = TY.coerce-typed wr γ Γ

  t3 : T3
  t3 wr γ = SI.coerce-identity wr γ

  t3-first-order : T3-First-Order
  t3-first-order wr γ = SI.coerce-identity-fo wr γ

  t5-typing : T5-Typing
  t5-typing wr u0 u2 e = TY.tr-typed wr u0 u2 e

  t5-behaviour : T5-Behaviour
  t5-behaviour wr e = SI.behaviour wr e

  t5-behaviour-first-order : T5-Behaviour-First-Order
  t5-behaviour-first-order wr e = SI.behaviour-fo wr e

  target-signature-valid : Target-Signature-Valid
  target-signature-valid = RC.target-valid

  role-correspondence : Role-Correspondence
  role-correspondence = RC.role-correspondence

  role-check-is-kinding : Role-Check-Is-Kinding
  role-check-is-kinding = RC.role-check-is-kinding

module _ where
  open Two-State-Statements
  private module TS = Wager.Trans.TwoStateProofs

  row-translation-exists : ∀ SS {R} (ops : GradeOps R) → Row-Translation-Exists SS ops
  row-translation-exists SS ops = TS.row-translation SS ops

  two-state-translation-exists : ∀ SS {R} (ops : GradeOps R) → Two-State-Translation-Exists SS ops
  two-state-translation-exists SS ops = TS.two-state-translation SS ops

  no-two-state-translation : No-Two-State-Translation
  no-two-state-translation = TS.no-two-state

------------------------------------------------------------------------
-- STAGE 5
------------------------------------------------------------------------

module _ (SS : SSig) (Sc : Wager.Trans.Scheme.StateScheme SS)
         {R : Type} (ops : GradeOps R) where
  open T6-Statements SS Sc ops
  private module NM = Wager.Trans.Nominal SS Sc ops

  t6 : T6
  t6 = NM.nominal-nf

  t6-conversion : T6-Conversion
  t6-conversion = NM.nominal-defeq

  -- By the definition of the translation: the transformer of a nominal
  -- coercion is the identity.
  t6-no-term : T6-No-Term
  t6-no-term γ e = refl

------------------------------------------------------------------------
-- STAGE 6
------------------------------------------------------------------------

module _ (S : Sig) (TS : Wager.L2.Signature.TSig S) (ops : GradeOps (Sig.TG S)) where
  open T7-Statements S TS ops
  private module Sep = Wager.Local.Separation S TS ops

  t7-separation : T7-Separation
  t7-separation = Sep.separation

------------------------------------------------------------------------
-- STAGE 6, PART 2
------------------------------------------------------------------------

module _ (S : Sig) (TS : Wager.L2.Signature.TSig S) (ops : GradeOps (Sig.TG S))
         (F : Wager.Identity.Family.IdFamily S TS) where
  open T7-Identity-Statements S TS ops F
  private module Snd = Wager.Identity.Soundness S TS ops F

  t7-conservative : T7-Conservative
  t7-conservative = Snd.emb-typed

  t7-conservative-erasure : T7-Conservative-Erasure
  t7-conservative-erasure t = Snd.emb-keep t , Snd.emb-erase t

  t7-intro : T7-Intro
  t7-intro = Snd.intro

  t7-canonicity : T7-Canonicity
  t7-canonicity = Snd.canonicity

  t7-erasure : T7-Erasure
  t7-erasure = Snd.erasure-sound

  t7-erasure-first-order : T7-Erasure-First-Order
  t7-erasure-first-order = Snd.erasure-sound-fo

  t7-grade : T7-Grade
  t7-grade laws = Snd.cast-free laws

  t7-assumption : T7-Assumption
  t7-assumption = Snd.assumption
