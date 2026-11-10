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
open import Cubical.Data.Sum.Base using (_⊎_; inl)
open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.FinData.Base using (Fin) renaming (zero to fzero)

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
open import Wager.FC.Signature
import Wager.FC.Types
import Wager.FC.Coercion
import Wager.FC.Term
import Wager.FC.Classic
import Wager.Erased.Untyped
import Wager.Erased.LogRel
import Wager.FC.Tagged
import Wager.Trans.Scheme
import Wager.Trans.Target
import Wager.Trans.Coercion
import Wager.Trans.TwoState
open import Cubical.Data.Empty using (⊥)
import Wager.L2.Erasure
import Wager.Local.Source
import Wager.Local.Gadt
import Wager.Identity.Family
import Wager.Identity.Typing
import Wager.Univalent.Model

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

------------------------------------------------------------------------
-- STAGE 3: the source calculus (a fragment of System FC with roles)
------------------------------------------------------------------------

-- The statements of this stage are about the SOURCE calculus only.
-- They have no T number. They show that the source calculus is the
-- calculus of Breitner et al. for this fragment: the role check makes
-- zero-cost coercions safe, and without the check the classic program
-- is unsound.
module Source-Statements (SS : SSig) where
  open Wager.FC.Types SS
  open Wager.FC.Coercion SS
  open Wager.FC.Term SS
  open Wager.Erased.Untyped.Typing litTy

  -- English: a nominal coercion relates two types with the same
  -- nominal value. (This part needs no role check.)
  Source-Nominal-Soundness : Type
  Source-Nominal-Soundness = (τ σ : STy) → Co nom τ σ → ev τ ≡ ev σ

  -- English: in a signature that passes the role check, a
  -- representational coercion relates two types with the same erased
  -- type.
  Source-Role-Soundness : Type
  Source-Role-Soundness =
    WellRoled → (τ σ : STy) → Co rep τ σ → er τ ≡ er σ

  -- English: erasure removes each cast.
  Cast-Vanishes : Type
  Cast-Vanishes =
    ∀ {n} {Γ : SCx n} {τ σ} (γ : Co rep τ σ) (e : STm Γ τ) →
    eraseTm (cast γ e) ≡ eraseTm e

  -- English: `coerce` erases to the identity function.
  Coerce-Erases-To-Identity : Type
  Coerce-Erases-To-Identity =
    ∀ {n} {Γ : SCx n} {τ σ} (γ : Co rep τ σ) →
    eraseTm (coerce {Γ = Γ} γ) ≡ ulam (uvar fzero)

  -- English: in a signature that passes the role check, the erasure of
  -- a term of the type τ has the erased type `er τ`.
  Erasure-Preserves-Typing : Type
  Erasure-Preserves-Typing =
    WellRoled → ∀ {n} {Γ : SCx n} {τ} (e : STm Γ τ) →
    (λ i → er (Γ i)) ⊢ᵉ eraseTm e ∶ er τ

-- The classic unsound program:
--   newtype Age = MkAge Int
--   type family F a where { F Int = Bool ; F Age = Char }
--   newtype T a = MkT (F a)
-- `classicS d` is this signature with the declared role d for the
-- parameter of T.
module Classic-Source-Statements where
  open Wager.FC.Classic

  -- English: the source role check rejects the declaration
  -- "representational" and the declaration "phantom" for the parameter
  -- of T.
  Classic-Rejected : Type
  Classic-Rejected =
    (d : Role) → leR d rep ≡ true → ¬ SSig.WellRoled (classicS d)

  -- The signature with the wrong declaration (representational).
  module Bad where
    open STypes rep
    open Wager.FC.Types (classicS rep)
    open Wager.FC.Coercion (classicS rep)
    open Wager.FC.Term (classicS rep)
    open Wager.Erased.Untyped.Typing litTy

    -- English: with the wrong declaration, `T Age` and `T Int` are
    -- representationally equal.
    Classic-Bad-Coercion : Type
    Classic-Bad-Coercion = Co rep (sT sAge) (sT sInt)

    -- English: with the wrong declaration, there is a closed term of
    -- the type Bool whose erasure is a Char literal. The erased term
    -- evaluates to the Char literal, and it does not have the erased
    -- type Bool.
    Classic-Unsound-If-Accepted : Type
    Classic-Unsound-If-Accepted =
      Σ[ e ∈ STm ∅ˢ sBool ]
        (eraseTm e ≡ ulit ℓchar)
        × (∅ᵉ ⊢ eraseTm e ⇓ vlit ℓchar)
        × (¬ (∅ᶜ ⊢ᵉ eraseTm e ∶ er sBool))

  -- The signature with the correct declaration (nominal).
  module Good where
    open STypes nom
    open Wager.FC.Types (classicS nom)
    open Wager.FC.Coercion (classicS nom)

    -- English: the source role check accepts the declaration "nominal".
    Classic-Nominal-Accepted : Type
    Classic-Nominal-Accepted = WellRoled

    -- English: with the correct declaration, Age and Int are
    -- representationally equal, and `T Age` and `T Int` are not.
    -- The source calculus thus rejects `coerce : T Age → T Int`.
    Classic-Nominal-No-Coercion : Type
    Classic-Nominal-No-Coercion =
      Co rep sAge sInt × (¬ Co rep (sT sAge) (sT sInt))

------------------------------------------------------------------------
-- STAGE 4: translation and simulation (theorems T3 and T5)
------------------------------------------------------------------------

-- The translation of Wager.Trans, for a source signature SS, a state
-- scheme Sc and a grade algebra A for the term grades.
--   T       the translation of a type
--   coerceT the translation of a representational coercion, as a
--           function of the target
--   tr      the translation of a term
--   eraseT  the erasure of a target term (a trope transition vanishes)
-- `𝒱 a` is observational equality of untyped values at the erased
-- type a (Wager.Erased.LogRel).
module Translation-Statements
  (SS : SSig) (Sc : Wager.Trans.Scheme.StateScheme SS)
  {R : Type} (A : GradeAlgebra R) where
  private
    ops = GradeAlgebra.ops A
  open GradeOps ops using (𝟘; 𝟙; _+_; _≤_)
  open Wager.FC.Types SS
  open Wager.FC.Coercion SS
  open Wager.FC.Term SS
  open Wager.Trans.Target SS Sc ops using (tSig; tTSig; tRoleSig; T; bodyFun; arr; [])
  open Wager.Trans.Coercion SS Sc ops using (coerceT; tr; eraseT; coI; fwd; tvar)
  open Wager.L2.Typing tSig tTSig ops using (Cx; _▸_⊢_∶_; 0ᵘ)
  open Wager.Erased.LogRel litTy
  open Wager.Erased.Untyped using (earr)

  -- English: a representational coercion becomes an ordinary term of
  -- the target: a function from the translation of τ to the
  -- translation of σ. The term uses no variable of the context, and
  -- its parameter has the grade 𝟙. This holds in EACH grade algebra.
  Coercion-Is-A-Term : Type
  Coercion-Is-A-Term =
    WellRoled → ∀ {τ σ} (γ : Co rep τ σ) {n} (Γ : Cx n) →
    0ᵘ ▸ Γ ⊢ coerceT γ ∶ arr 𝟙 (T τ) (T σ)

  -- English (T3): the erasure of each translated coercion evaluates to
  -- a function value, and this value is observationally equal to the
  -- identity function, at the erased type of τ.
  T3 : Type
  T3 =
    WellRoled → ∀ {τ σ} (γ : Co rep τ σ) →
    Σ[ f ∈ UVal ] (∅ᵉ ⊢ eraseT (coerceT γ) ⇓ f)
                × 𝒱 (earr (er τ) (er τ)) (vclo ∅ᵉ (uvar fzero)) f

  -- English (T3 at a first-order type): the body of the erased
  -- coercion, with its argument bound to the value v, evaluates to v.
  T3-First-Order : Type
  T3-First-Order =
    WellRoled → ∀ {τ σ} (γ : Co rep τ σ) → FO (er τ) →
    ∀ v → 𝒱 (er τ) v v →
    Σ[ w ∈ UVal ] ((v ∷ᵉ ∅ᵉ) ⊢ eraseT (fwd (coI rep γ) (tvar fzero)) ⇓ w) × (w ≡ v)

  -- English (T5, typing): the translation of a term of the type τ has
  -- the type `T τ`, with the usage 𝟙 for each variable. This holds in
  -- each grade algebra in which the grade 𝟙 is unrestricted: 𝟘 ≤ 𝟙 and
  -- 𝟙 + 𝟙 ≤ 𝟙.
  T5-Typing : Type
  T5-Typing =
    WellRoled → 𝟘 ≤ 𝟙 → (𝟙 + 𝟙) ≤ 𝟙 →
    ∀ {n} {Γ : SCx n} {τ} (e : STm Γ τ) →
    (λ _ → 𝟙) ▸ (λ i → T (Γ i)) ⊢ tr e ∶ T τ

  -- English (T5, behaviour): for a closed source term, the erased
  -- source term and the erased translation evaluate, and the two
  -- values are observationally equal at the erased type.
  T5-Behaviour : Type
  T5-Behaviour =
    WellRoled → ∀ {τ} (e : STm ∅ˢ τ) →
    Σ[ v ∈ UVal ] Σ[ w ∈ UVal ]
      (∅ᵉ ⊢ eraseTm e ⇓ v) × (∅ᵉ ⊢ eraseT (tr e) ⇓ w) × 𝒱 (er τ) v w

  -- English (T5 at a first-order type): the two erased programs
  -- evaluate to one value.
  T5-Behaviour-First-Order : Type
  T5-Behaviour-First-Order =
    WellRoled → ∀ {τ} (e : STm ∅ˢ τ) → FO (er τ) →
    Σ[ v ∈ UVal ] (∅ᵉ ⊢ eraseTm e ⇓ v) × (∅ᵉ ⊢ eraseT (tr e) ⇓ v)

  -- English: the target signature of the translation respects its
  -- declared grades. The hypothesis of T2 thus holds for it.
  Target-Signature-Valid : Type
  Target-Signature-Valid = Wager.Role.Validity.Valid tRoleSig mulZ

  module _ where
    open Wager.L1.Kinding tSig (tableOps tableZ)

    -- English (role correspondence): the body of a newtype N is a
    -- type-level function of the target. Target kinding accepts the
    -- grade g for its parameter exactly when the inferred source role
    -- of the parameter is at most g. The inferred role is thus the
    -- least grade that kinding accepts.
    Role-Correspondence : Type
    Role-Correspondence =
      (N : N₁) (g : Role) →
        ((leR (roleOf (body N)) g ≡ true) → Σ[ γ ∈ KUsage [] ] (γ ⊢ᵏ bodyFun N g))
      × ((γ : KUsage []) → γ ⊢ᵏ bodyFun N g → leR (roleOf (body N)) g ≡ true)

    -- English: the source role check holds exactly when target kinding
    -- accepts the declared role of each newtype.
    Role-Check-Is-Kinding : Type
    Role-Check-Is-Kinding =
        (WellRoled → (N : N₁) → Σ[ γ ∈ KUsage [] ] (γ ⊢ᵏ bodyFun N (role N)))
      × (((N : N₁) → Σ[ γ ∈ KUsage [] ] (γ ⊢ᵏ bodyFun N (role N))) → WellRoled)

-- `Translation` and `TwoState` are in Wager.Trans.TwoState.
-- `Translation` says what a translation of types must keep.
-- `TwoState` says that each newtype with a parameter is ONE trope state
-- on its representation, as in Stage 2 (`Int@age`, `Int@raw`).
module Two-State-Statements where

  module _ (SS : SSig) {R : Type} (ops : GradeOps R) where
    open Wager.FC.Types SS
    open Wager.Trans.Scheme SS
    open Wager.Trans.TwoState SS
    private
      tgt : StateScheme → Sig
      tgt Sc = Wager.Trans.Target.tSig SS Sc ops

    -- English: for each source signature, the translation with the row
    -- scheme meets the conditions of `Translation`.
    Row-Translation-Exists : Type
    Row-Translation-Exists = Translation (tgt rowScheme)

    -- English: when no type-level function looks at the argument of a
    -- newtype, the translation with two-state tropes exists.
    Two-State-Translation-Exists : Type
    Two-State-Translation-Exists =
      (c : Fam → N₁ → Base) (h : ∀ F N → fNt₁ F N ≡ inl (c F N)) →
      Σ[ t ∈ Translation (tgt (twoState c h)) ] TwoState (tgt (twoState c h)) t

  -- The source signature `taggedS rep` has the phantom newtype
  -- `newtype Tag a = MkTag Int` and the type-level function F with
  -- `F (Tag a) = G a`, `G Int = Bool`, `G Bool = Char`.
  --
  -- English: this source program has NO translation with two-state
  -- tropes. This holds for each target signature.
  No-Two-State-Translation : Type₁
  No-Two-State-Translation =
    (S : Sig) (t : Translation S) → ¬ TwoState S t
    where open Wager.Trans.TwoState (Wager.FC.Tagged.taggedS rep)

------------------------------------------------------------------------
-- STAGE 5: nominal coercions from type-level functions (theorem T6)
------------------------------------------------------------------------

-- A nominal coercion of the source is built from reflexivity, symmetry,
-- transitivity, congruence and the equations of the type-level
-- functions. `T` is the translation of types of Stage 4.
module T6-Statements
  (SS : SSig) (Sc : Wager.Trans.Scheme.StateScheme SS)
  {R : Type} (ops : GradeOps R) where
  open Wager.FC.Types SS
  open Wager.FC.Coercion SS
  open Wager.FC.Term SS
  open Wager.Trans.Target SS Sc ops using (tSig; T)
  open Wager.Trans.Coercion SS Sc ops using (tr)
  open Wager.L1.Conversion tSig using (DefEq)
  open Wager.L1.Eval tSig using (nf)

  -- English (T6): for each nominal coercion of the source, the two
  -- translated types have one normal form.
  T6 : Type
  T6 = ∀ {τ σ} → Co nom τ σ → nf (T τ) ≡ nf (T σ)

  -- English: the coercion becomes conversion of the target.
  T6-Conversion : Type
  T6-Conversion = ∀ {τ σ} → Co nom τ σ → DefEq (T τ) (T σ)

  -- English: no term remains. The translation of a cast along a nominal
  -- coercion is the translation of the term under the cast.
  T6-No-Term : Type
  T6-No-Term =
    ∀ {n} {Γ : SCx n} {τ σ} (γ : Co nom τ σ) (e : STm Γ τ) →
    tr (cast (c-sub γ) e) ≡ tr e

------------------------------------------------------------------------
-- STAGE 6: local equality assumptions (theorem T7)
------------------------------------------------------------------------

-- The owner asked for the two options of the stage, the separation
-- first (DESIGN-CHOICES.adoc, DC-6.1). This part is the separation.
--
-- The source calculus of the stage is `Wager.Local.Source`. It has the
-- type `⟨ τ ~ σ ⟩ ρ` of a GADT constructor field: a value of the type
-- ρ with evidence that the types τ and σ are equal. The match `lopen`
-- brings the equality into scope as a local assumption.
--
-- The program is `Wager.Local.Gadt.gadt-eval`. In Haskell, for a base
-- type b:
--
--   data G a where
--     GI :: (a ~ b)          => a -> G a
--     GB :: (a ~ Either b b) => a -> G a
--
--   eval :: G a -> b
--   eval (GI x) = x
--   eval (GB x) = case x of { Left y -> y ; Right y -> y }
--
-- `gadt-eval b α` is `eval` at the closed instance a := α. It is a term
-- of the source calculus, so it is well typed there.
--
--   erT     the erased type of a closed target type
--   eraseᵗ  the erasure of a target term
--   erˡ     the erased type of a source type
--   eraseˡ  the erasure of a source term
module T7-Statements
  (S : Sig) (TS : Wager.L2.Signature.TSig S) (ops : GradeOps (Sig.TG S)) where
  open Sig S using (Base)
  open Wager.L1.Syntax S using (Ty; []; ★)
  open Wager.L2.Typing S TS ops using (_▸_⊢_∶_; Tm; Usage; Cx; Lit; litTy)
  open Wager.L2.Erasure S TS ops using (erT; eraseᵗ)
  open Wager.Local.Source Base Lit litTy using (LTy; lbase; _⇒ˡ_; erˡ; eraseˡ)
  open Wager.Local.Gadt Base Lit litTy using (G; gadt-eval)

  -- English (T7, the separation): the target cannot type this program.
  -- For each base type b and each closed type α, no typed target term
  -- has these two properties together:
  --   its type has the erased type of the source type `G b α → b`;
  --   its erasure is the erasure of the source program.
  -- This holds for each target signature and each set of grade
  -- operations.
  --
  -- The statement does not exclude a translation that changes the
  -- erased type or the erased term of the program.
  T7-Separation : Type
  T7-Separation =
    (b : Base) (α : LTy) {γ : Usage 0} {Γ : Cx 0} {t : Tm 0} {A : Ty [] ★} →
    γ ▸ Γ ⊢ t ∶ A →
    erT A ≡ erˡ (G b α ⇒ˡ lbase b) →
    eraseᵗ t ≡ eraseˡ (gadt-eval b α) →
    ⊥

------------------------------------------------------------------------
-- STAGE 6, PART 2: the identity type at the grade 𝟘 (theorem T7)
------------------------------------------------------------------------

-- This part is the other option of the stage (DESIGN-CHOICES.adoc,
-- DC-6.1 and DC-6.5): the target gets an identity type.
--
-- EQUALITY EVIDENCE IS NOW A TERM. A term of the type `base (Id A B)`
-- is evidence that the closed types A and B are equal.
--
--   Id A B        a base constant of the signature (`IdFamily`)
--   rfl A         a literal of the base type `Id A A`
--   cast e t      the one new term former: the evidence e, the payload t
--   _▸_⊢ⁱ_∶_      the target judgement with one new rule, `t-cast`, which
--                 uses the evidence at the grade 𝟘
--   keepⁱ         the reference erasure: each cast evaluates its
--                 evidence, then its payload
--   eraseⁱ        the erasure of proofs: the evidence of each cast is
--                 absent
--   𝒱 a           observational equality of untyped values at the
--                 erased type a (Wager.Erased.LogRel)
--
-- The statements hold for each signature that has an identity family,
-- and for each set of grade operations. Two statements need the laws
-- of a grade algebra, and they say so.
module T7-Identity-Statements
  (S : Sig) (TS : Wager.L2.Signature.TSig S) (ops : GradeOps (Sig.TG S))
  (F : Wager.Identity.Family.IdFamily S TS) where
  open Wager.L1.Syntax S using (Ty; []; ★; base; arr)
  open Wager.L1.Conversion S using (DefEq)
  open Wager.L2.Typing S TS ops using (_▸_⊢_∶_; Tm)
  open Wager.L2.Erasure S TS ops using (erT; eraseᵗ)
  open Wager.Identity.Typing S TS ops F
  open GradeOps ops using (𝟘; 𝟙)
  open Wager.Erased.Untyped.Terms Lit using (UVal; ∅ᵉ; _⊢_⇓_)
  open Wager.Erased.LogRel litTy using (𝒱; FO)

  -- English (the target is a part): each typed term of the target is a
  -- typed term of the extension, with the same usage and the same type.
  T7-Conservative : Type
  T7-Conservative =
    ∀ {n} {γ : Usage n} {Γ : Cx n} {t : Tm n} {A : Ty [] ★} →
    γ ▸ Γ ⊢ t ∶ A → γ ▸ Γ ⊢ⁱ emb t ∶ A

  -- English: on a term of the target, the two erasures of the
  -- extension are the erasure of the target.
  T7-Conservative-Erasure : Type
  T7-Conservative-Erasure =
    ∀ {n} (t : Tm n) → (keepⁱ (emb t) ≡ eraseᵗ t) × (eraseⁱ (emb t) ≡ eraseᵗ t)

  -- English (introduction): a conversion gives evidence. If A and B
  -- are convertible, the literal `rfl A` has the type `Id A B`, in each
  -- context, and it uses no variable.
  T7-Intro : Type
  T7-Intro =
    ∀ {n} {Γ : Cx n} {A B : Ty [] ★} → DefEq A B →
    0ᵘ ▸ Γ ⊢ⁱ ilit (rfl A) ∶ base (Id A B)

  -- English (canonicity): closed evidence gives a conversion. If a
  -- closed term has the type `Id A B`, then A and B are convertible.
  -- The identity family thus adds no equality between closed types.
  T7-Canonicity : Type
  T7-Canonicity =
    ∀ {γ : Usage 0} {Γ : Cx 0} {e : ITm 0} {A B : Ty [] ★} →
    γ ▸ Γ ⊢ⁱ e ∶ base (Id A B) → DefEq A B

  -- English (T7, the erasure of proofs is sound): for a closed typed
  -- term, the reference program and the program with no evidence in its
  -- casts evaluate, and the two values are observationally equal at the
  -- erased type.
  --
  -- Totality is a part of the statement: the reference program, which
  -- evaluates the evidence of each cast, has a value.
  T7-Erasure : Type
  T7-Erasure =
    ∀ {γ : Usage 0} {Γ : Cx 0} {t : ITm 0} {A : Ty [] ★} →
    γ ▸ Γ ⊢ⁱ t ∶ A →
    Σ[ v ∈ UVal ] Σ[ w ∈ UVal ]
      (∅ᵉ ⊢ keepⁱ t ⇓ v) × (∅ᵉ ⊢ eraseⁱ t ⇓ w) × 𝒱 (erT A) v w

  -- English (T7 at a first-order type): the two programs evaluate to
  -- one value.
  T7-Erasure-First-Order : Type
  T7-Erasure-First-Order =
    ∀ {γ : Usage 0} {Γ : Cx 0} {t : ITm 0} {A : Ty [] ★} →
    γ ▸ Γ ⊢ⁱ t ∶ A → FO (erT A) →
    Σ[ v ∈ UVal ] (∅ᵉ ⊢ keepⁱ t ⇓ v) × (∅ᵉ ⊢ eraseⁱ t ⇓ v)

  -- English (the grade): in a grade algebra, evidence costs nothing.
  -- The usage vector of `cast e t` is the usage vector of the payload t,
  -- which is the term that remains after the erasure of proofs.
  T7-Grade : Type
  T7-Grade =
    GradeLaws ops →
    ∀ {n} {γ δ : Usage n} {Γ : Cx n} {e t : ITm n} {A B : Ty [] ★} →
    γ ▸ Γ ⊢ⁱ e ∶ base (Id A B) → δ ▸ Γ ⊢ⁱ t ∶ A →
    δ ▸ Γ ⊢ⁱ cast e t ∶ B

  -- English (a local equality assumption): in a grade algebra, for each
  -- pair of closed types A and B, this closed function is typed:
  --
  --   λ (e : Id A B) at the grade 𝟘. λ (x : A) at the grade 𝟙. cast e x
  --
  -- It has the type `Id A B → A → B`. The types A and B are any types.
  -- The first parameter is the local assumption that A and B are equal.
  T7-Assumption : Type
  T7-Assumption =
    GradeLaws ops → ∀ (A B : Ty [] ★) {Γ : Cx 0} →
    0ᵘ ▸ Γ ⊢ⁱ use-assumption A B ∶ arr 𝟘 (base (Id A B)) (arr 𝟙 A B)

------------------------------------------------------------------------
-- STAGE 7: the optional univalent cross-check
------------------------------------------------------------------------

-- The task: "Interpret target types in the cubical universe and newtype
-- transitions as equivalences. Show that the denotation of a translated
-- coercion equals transport along the path from `ua`."
--
-- The model is `Wager.Univalent.Model` (DESIGN-CHOICES.adoc, DC-7.1 to
-- DC-7.3). It is for the target of Stage 4, for each source signature,
-- each state scheme and each grade algebra, and for each interpretation
-- `El` of the base constants with an element `elLit ℓ` for each literal.
--
--   ⟦ X ⟧          the interpretation of a closed target type: a type of
--                  the cubical universe. A newtype instance is a wrapper
--                  `Box`, and `unboxEquiv : Box Z ≃ Z` is its transition.
--   Real X ρ u x   the untyped term u, in the environment ρ, evaluates
--                  to a value that realises the element x of ⟦ X ⟧
--   Denotes X Y f g
--                  the term transformer f denotes the function g: on a
--                  term that evaluates to a realiser of x, the term
--                  `f t` evaluates to a realiser of `g x`
--   pathOf wr γ    the path ⟦ T τ ⟧ ≡ ⟦ T σ ⟧ of a representational
--                  coercion γ. It is made from `ua unboxEquiv` (a newtype
--                  axiom), `sym`, composition, and congruence of the
--                  type formers. It needs the source role check `wr`.
module Stage7-Statements
  (SS : SSig) (Sc : Wager.Trans.Scheme.StateScheme SS)
  {R : Type} (A : GradeAlgebra R)
  (El : SSig.Base SS → Type)
  (elLit : (ℓ : SSig.Lit SS) → El (SSig.litTy SS ℓ)) where
  private
    ops = GradeAlgebra.ops A
  open GradeOps ops using (𝟙)
  open Wager.FC.Types SS
  open Wager.FC.Coercion SS
  open Wager.Trans.Target SS Sc ops using (T; arr)
  open Wager.Trans.Coercion SS Sc ops using (coI; fwd; bwd; coerceT; eraseT)
  open Wager.Univalent.Model SS Sc A El elLit
  open Wager.Erased.Untyped.Terms Lit using (UEnv)

  -- English (the cross-check): the translation of a representational
  -- coercion denotes transport along its path. On a term that evaluates
  -- to a realiser of x, the transformed term evaluates to a realiser of
  -- `transport (pathOf wr γ) x`.
  Coercion-Denotes-Transport : Type
  Coercion-Denotes-Transport =
    (wr : WellRoled) → ∀ {τ σ} (γ : Co rep τ σ) →
    Denotes (T τ) (T σ) (fwd (coI rep γ)) (transport (pathOf wr γ))

  -- English: the transformer in the other direction denotes transport
  -- along the inverse path.
  Coercion-Denotes-Transport-Back : Type
  Coercion-Denotes-Transport-Back =
    (wr : WellRoled) → ∀ {τ σ} (γ : Co rep τ σ) →
    Denotes (T σ) (T τ) (bwd (coI rep γ)) (transport (sym (pathOf wr γ)))

  -- English: the erased coercion function evaluates, in each
  -- environment, to a closure that realises the function
  -- `transport (pathOf wr γ)`.
  Coerce-Function-Is-Transport : Type
  Coerce-Function-Is-Transport =
    (wr : WellRoled) → ∀ {τ σ} (γ : Co rep τ σ) {n} {ρ : UEnv n} →
    Real (arr 𝟙 (T τ) (T σ)) ρ (eraseT (coerceT γ)) (transport (pathOf wr γ))
