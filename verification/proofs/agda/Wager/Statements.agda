{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- THE HEADLINE THEOREMS OF THE WAGER EXPERIMENT, AS TYPES ONLY.
--
-- A reviewer reads this file. It imports definitions and no proof.
-- Each statement is a type with a plain-English reading. The module
-- `Wager.Proofs` gives one inhabitant for each statement.
--
-- A statement in this file is frozen when its stage starts. A change
-- to a frozen statement is recorded in VERDICT.adoc.
module Wager.Statements where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (_×_; Σ-syntax)
open import Cubical.Data.Sum.Base using (_⊎_)
open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.FinData.Base using (Fin)

open import Wager.Grade.Algebra
open import Wager.Grade.Affine using (Affine)
open import Wager.Grade.Level using (Sec)
open import Wager.L1.Signature
import Wager.L1.Syntax
import Wager.L1.Conversion
import Wager.L1.Eval
import Wager.L1.Normal
import Wager.L1.Kinding
import Wager.L2.Signature
import Wager.L2.Typing
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Data.Bool.Base using (true)
open import Wager.Role.Role
open import Wager.Role.Role4 using (Role4; role4Ops; mul4; nom4; ph4)
open import Wager.Role.Table
open import Wager.Role.Signature
import Wager.Role.RepEq
import Wager.Role.Validity
import Wager.Role.Classic

------------------------------------------------------------------------
-- STAGE 1
------------------------------------------------------------------------

-- The two instances that show that T0 is not empty.
--
-- English: the 3-point structure {0, 1, ω} with the systemet order is a
-- grade algebra. All 15 law fields of the Lean class hold.
Affine-Is-Grade-Algebra : Type₁
Affine-Is-Grade-Algebra = GradeAlgebra Affine

-- English: the 2-point lattice Low ≤ High is a grade algebra
-- (+ is meet, · is join, 𝟘 is High, 𝟙 is Low).
Level-Is-Grade-Algebra : Type₁
Level-Is-Grade-Algebra = GradeAlgebra Sec

module L1-Statements (S : Sig) where
  open Wager.L1.Syntax S
  open Wager.L1.Conversion S
  open Wager.L1.Normal S
  open Wager.L1.Eval S

  -- L1 (equality is conversion; ET-2 for this language).
  --
  -- English: for each signature, two type-level terms of the same kind
  -- are convertible if and only if the total normalizer `nf` gives the
  -- same normal form for both. `DefEq` is β, the δ-rules of the
  -- signature primitives, equivalence and congruence. There is no η.
  L1-Equality : Type
  L1-Equality =
    ∀ {Γ : Ctx} {k : Kind} (t u : Ty Γ k) →
      (DefEq t u → nf t ≡ nf u) × (nf t ≡ nf u → DefEq t u)

-- T0 holds for EACH signature S, EACH term signature TS, and EACH
-- grade algebra R on the term grades. The typing rules take the
-- operations of R only.
module T0-Statements
  (S : Sig) (TS : Wager.L2.Signature.TSig S) (R : GradeAlgebra (Sig.TG S)) where
  open Wager.L1.Syntax S using (Ty; ★; [])
  open Wager.L2.Typing S TS (GradeAlgebra.ops R)

  -- T0, part 1 (graded substitution).
  --
  -- English: let the term t have the type B in a context with one more
  -- variable of type A, and let t use that variable at the grade q and
  -- the other variables as γ says. Let u have the type A and use the
  -- variables as δ says. Then t with u for the variable has the type B
  -- and uses the variables as γ + q · δ says.
  T0-Substitution : Type
  T0-Substitution =
    ∀ {n : ℕ} {γ δ : Usage n} {Γ : Cx n} {q} {A B : Ty [] ★}
      {t : Tm (suc n)} {u : Tm n} →
      (γ ▹ q) ▸ (Γ ▹ᶜ A) ⊢ t ∶ B →
      δ ▸ Γ ⊢ u ∶ A →
      (γ +ᵘ (q ·ᵘ δ)) ▸ Γ ⊢ t [ u ]ᵗ ∶ B

  -- T0, part 2 (preservation).
  --
  -- English: if a term has a type with a usage vector, and the term
  -- makes one reduction step, then the result has the same type with
  -- the same usage vector, in the same context.
  T0-Preservation : Type
  T0-Preservation =
    ∀ {n : ℕ} {γ : Usage n} {Γ : Cx n} {t t' : Tm n} {A : Ty [] ★} →
      γ ▸ Γ ⊢ t ∶ A → t ⟶ t' → γ ▸ Γ ⊢ t' ∶ A

  -- T0, part 3 (progress).
  --
  -- English: a closed term that has a type is a value, or it can make
  -- one reduction step.
  T0-Progress : Type
  T0-Progress =
    ∀ {γ : Usage 0} {Γ : Cx 0} {t : Tm 0} {A : Ty [] ★} →
      γ ▸ Γ ⊢ t ∶ A → Value t ⊎ (Σ[ t' ∈ Tm 0 ] (t ⟶ t'))

------------------------------------------------------------------------
-- STAGE 2
------------------------------------------------------------------------

-- T1: roles as a grade structure. Role = {ph, rep, nom}, 𝟘 = ph,
-- 𝟙 = rep, + = maximum, · = composition (outer · inner). There are two
-- composition tables. They differ in the entry nominal · phantom.
module T1-Statements where

  -- English: with the lawful table (nominal · phantom = phantom), all
  -- 15 law fields hold.
  T1-Lawful : Type
  T1-Lawful = GradeLaws roleZOps

  -- English: with the GHC table (nominal · phantom = nominal), the 14
  -- law fields other than `a · 𝟘 = 𝟘` hold.
  T1-GHC-Other-Laws : Type
  T1-GHC-Other-Laws = GradeLawsExceptMulZero roleGOps

  -- English: with the GHC table, the law `a · 𝟘 = 𝟘` is false.
  T1-GHC-MulZero-Fails : Type
  T1-GHC-MulZero-Fails = ¬ (∀ a → mulG a ph ≡ ph)

  -- English: with the GHC table, `a · 𝟘 = 𝟘` holds at phantom and at
  -- representational, and it fails at nominal.
  T1-GHC-Fails-At-Nominal-Only : Type
  T1-GHC-Fails-At-Nominal-Only =
    (mulG ph ph ≡ ph) × (mulG rep ph ≡ ph) × (¬ (mulG nom ph ≡ ph))

-- Noninterference for a role signature RS and a composition table T.
-- The kinding judgement is the generic one, with the operations of T.
module Noninterference-Statements (RS : RoleSig) (T : RoleTable) where
  open RoleTable T using (mul)
  open Wager.L1.Syntax (toSig RS)
  open Wager.L1.Eval (toSig RS)
  open Wager.L1.Kinding (toSig RS) (tableOps T)
  open Wager.Role.Validity RS mul

  -- English: let each constant and each primitive of the signature
  -- respect its declared grade (`Valid`). Let F be a closed type
  -- function with the parameter grade r. Then, for each observer ρ:
  -- two arguments that the observer `ρ · r` cannot tell apart give
  -- results that the observer ρ cannot tell apart.
  Noninterference : Type
  Noninterference =
    Valid →
    ∀ {r : Role} (F : Ty [] (★ ⇒[ r ] ★)) {γ : KUsage []} → γ ⊢ᵏ F →
    (ρ : Role) (A B : Ty [] ★) →
    R★ (mul ρ r) (nf A) (nf B) → R★ ρ (nf (app F A)) (nf (app F B))

-- T2: role soundness as noninterference, with the lawful table.
module T2-Statements (RS : RoleSig) where
  open Wager.L1.Syntax (toSig RS)
  open Wager.L1.Eval (toSig RS)
  open Wager.L1.Kinding (toSig RS) (tableOps tableZ)
  open Wager.Role.RepEq RS
  open Wager.Role.Validity RS mulZ

  -- English: let the signature respect its declared grades. If F has a
  -- parameter grade r ≤ representational, and A ≈ B, then
  -- nf (F A) ≈ nf (F B).
  T2-Representational : Type
  T2-Representational =
    Valid →
    ∀ {r : Role} (F : Ty [] (★ ⇒[ r ] ★)) {γ : KUsage []} → γ ⊢ᵏ F →
    leR r rep ≡ true →
    (A B : Ty [] ★) → nf A ≈ nf B → nf (app F A) ≈ nf (app F B)

  -- English: let the signature respect its declared grades. If F has
  -- the parameter grade phantom, then nf (F A) ≡ nf (F B) for all
  -- A and B.
  T2-Phantom : Type
  T2-Phantom =
    Valid →
    (F : Ty [] (★ ⇒[ ph ] ★)) {γ : KUsage []} → γ ⊢ᵏ F →
    (A B : Ty [] ★) → nf (app F A) ≡ nf (app F B)

-- T4: the classic unsound program, at the type level. The signature is
-- `classicSig rep` of Wager.Role.Classic.
module T4-Statements where
  open Wager.Role.Classic
  open Types rep
  private S = toSig (classicSig rep)
  open Wager.L1.Syntax S
  open Wager.L1.Eval S
  open Wager.L1.Kinding S (tableOps tableZ)
  open Wager.Role.RepEq (classicSig rep)

  -- English: the function `classicF` (it maps Age to Char and Int to
  -- Bool) has no kinding derivation at the grade representational, and
  -- none at the grade phantom.
  T4-Kinding-Rejects : Type
  T4-Kinding-Rejects =
    (g : Role) → leR g rep ≡ true → (γ : KUsage []) → ¬ (γ ⊢ᵏ classicF g)

  -- English: Age ≈ Int, and the results of `classicF` on Age and on
  -- Int are not representationally equivalent.
  T4-Not-Equivalent : Type
  T4-Not-Equivalent =
    (nf {Γ = []} Age ≈ nf Int)
    × ((g : Role) → ¬ (nf (app (classicF g) Age) ≈ nf (app (classicF g) Int)))

-- The test of Stage 2, step 3: a generative constant with a parameter
-- that is declared phantom (`Proxy a`), below a type-level function that
-- inspects its argument.
module Proxy-Statements where
  open Wager.Role.Classic

  -- Part A. Lawful table, `proxy` declared phantom.
  module A where
    open Types ph
    private S = toSig (classicSig ph)
    open Wager.L1.Syntax S
    open Wager.L1.Eval S
    open Wager.L1.Kinding S (tableOps tableZ)
    open Wager.Role.RepEq (classicSig ph)
    open Wager.Role.Validity (classicSig ph) mulZ

    -- English: kinding accepts the grade phantom for
    -- `deepF = λa. deep (Proxy a)`, and the results of deepF on Age and
    -- on Int are not equivalent. The lawful table is thus NOT sound for
    -- a signature with a generative phantom constant.
    Lawful-Unsound-With-Phantom-Constant : Type
    Lawful-Unsound-With-Phantom-Constant =
      (Σ[ γ ∈ KUsage [] ] (γ ⊢ᵏ deepF ph))
      × (¬ (nf (app (deepF ph) Age) ≈ nf (app (deepF ph) Int)))

    -- English: the conclusion of T2-Phantom is false for `λa. Proxy a`.
    T2-Phantom-Fails-Without-Valid : Type
    T2-Phantom-Fails-Without-Valid =
      (Σ[ γ ∈ KUsage [] ] (γ ⊢ᵏ proxyF ph))
      × (¬ (nf (app (proxyF ph) Int) ≡ nf (app (proxyF ph) Bool')))

    -- English: this signature does not respect its declared grades.
    Phantom-Constant-Not-Valid : Type
    Phantom-Constant-Not-Valid = ¬ Valid

  -- Part B. Lawful table, `proxy` declared representational.
  module B where
    open Types rep
    private S = toSig (classicSig rep)
    open Wager.L1.Syntax S
    open Wager.L1.Eval S
    open Wager.Role.RepEq (classicSig rep)
    open Wager.Role.Validity (classicSig rep) mulZ

    -- English: this signature respects its declared grades, so T2
    -- holds for it.
    Rep-Constant-Valid : Type
    Rep-Constant-Valid = Valid

    -- English: `Proxy Int` and `Proxy Bool` are not representationally
    -- equivalent. A coercion between them (GHC accepts it, because the
    -- parameter of Proxy is phantom) has no counterpart here.
    No-Phantom-Coercion : Type
    No-Phantom-Coercion = ¬ (nf {Γ = []} (Proxy Int) ≈ nf (Proxy Bool'))

  -- Part C. GHC table, `proxy` declared phantom.
  module C where
    open Types ph
    private S = toSig (classicSig ph)
    open Wager.L1.Syntax S
    private
      module KZ = Wager.L1.Kinding S (tableOps tableZ)
      module KG = Wager.L1.Kinding S (tableOps tableG)

    -- English: the GHC table rejects each grade below nominal for
    -- `deepF`. On this program it is sound.
    GHC-Rejects-Deep : Type
    GHC-Rejects-Deep =
      (g : Role) → leR g rep ≡ true → (γ : KG.KUsage []) → ¬ (γ KG.⊢ᵏ deepF g)

    -- English: `constF = λa. isAge Int` does not use its parameter.
    -- The lawful table accepts the grade phantom for it. The GHC table
    -- rejects the grade phantom for it: with the GHC table as a grade
    -- structure, a nominal function makes each unused variable nominal.
    GHC-Rejects-Unused-Parameter : Type
    GHC-Rejects-Unused-Parameter =
      (Σ[ γ ∈ KZ.KUsage [] ] (γ KZ.⊢ᵏ constF ph))
      × ((γ : KG.KUsage []) → ¬ (γ KG.⊢ᵏ constF ph))

-- A finding outside T1: a 4-point structure with a separate grade
-- "absent" for 𝟘.
module Role4-Statements where

  -- English: the 4-point role structure satisfies all 15 law fields.
  Role4-Lawful : Type
  Role4-Lawful = GradeLaws role4Ops

  -- English: in the 4-point structure the GHC rule holds:
  -- nominal · phantom = nominal.
  Role4-Has-GHC-Rule : Type
  Role4-Has-GHC-Rule = mul4 nom4 ph4 ≡ nom4
