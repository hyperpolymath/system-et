{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- DESIGN-CHOICES.adoc, DC-0.3: matches on typing derivations.
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- Stage 1 anti-vacuity examples. For each Stage 1 theorem this file
-- has one closed example that satisfies the hypotheses, and one closed
-- example that the system rejects. Agda checks both.
module Wager.Examples.Stage1 where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.Nat.Properties using (znots; snotz)
open import Cubical.Data.FinData.Base using (Fin; zero; suc)
open import Cubical.Data.Bool.Base using (Bool; true; false)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Sum.Base using (_⊎_; inl; inr)
open import Cubical.Data.Sigma using (_×_; Σ-syntax)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Relation.Nullary using (¬_)

open import Wager.Grade.Algebra
open import Wager.Grade.Finite using (false≢true)
open import Wager.Grade.Affine
open import Wager.Grade.Level
open import Wager.L1.Signature
import Wager.L1.Syntax
import Wager.L1.Conversion
import Wager.L1.Normal
import Wager.L1.Eval
import Wager.L1.Heads
import Wager.L2.Signature
import Wager.L2.Typing
import Wager.L2.Inversion
import Wager.L2.Preservation
open import Wager.Proofs

------------------------------------------------------------------------
-- The example signature, for a carrier T of term grades.
--   base constants: the natural numbers (as in the Lean language)
--   one generative constant `tt` (a box, also used as a trope state)
--   two primitives:
--     false  looks at the head: base ↦ 0, box ↦ 1, other ↦ 2
--     true   on a box, inspects the argument with `false`

exSig : Type → Sig
exSig T = record
  { KG = Unit ; TG = T ; Base = ℕ
  ; Con₁ = Unit ; cgrade = λ _ → tt
  ; Prim = Bool ; pgrade = λ _ → tt
  ; onBase = λ _ _ → 0
  ; onCon = λ { false _ → inl 1 ; true _ → inr false }
  ; onOther = λ _ → 2 }

-- One literal for each natural number, of the base type 0.
-- Two trope operations on the carrier `base 0`:
--   true   wrap:   raw   → box
--   false  unwrap: box   → raw
exTSig : (T : Type) → Wager.L2.Signature.TSig (exSig T)
exTSig T = record
  { Lit = ℕ ; litTy = λ _ → 0
  ; Op = Bool ; carrier = λ _ → base 0
  ; from = λ { true → nothing ; false → just tt }
  ; to   = λ { true → just tt ; false → nothing } }
  where
  open Wager.L1.Syntax (exSig T)
  open Wager.L2.Signature (exSig T)

------------------------------------------------------------------------
-- L1-Equality.

module L1-Examples where
  private S = exSig Unit
  open Wager.L1.Syntax S
  open Wager.L1.Conversion S
  open Wager.L1.Normal S
  open Wager.L1.Eval S
  open Wager.L1.Heads S

  -- (λa. a) B₀
  idApp : Ty [] ★
  idApp = app {g = tt} (lam (var vz)) (base 0)

  -- ACCEPTED: the two types are convertible, and `nf` computes the
  -- same normal form for both.
  accepted-defEq : DefEq idApp (base 0)
  accepted-defEq = d-beta (var vz) (base 0)

  accepted-nf : nf idApp ≡ nf (base 0)
  accepted-nf = refl

  -- The theorem gives the same fact from the conversion.
  accepted-by-theorem : nf idApp ≡ nf (base 0)
  accepted-by-theorem = fst (l1-equality S idApp (base 0)) accepted-defEq

  -- REJECTED: two different base constants are not convertible.
  rejected : ¬ DefEq (base {Γ = []} 0) (base 1)
  rejected d = znots (base-inj d)

  -- A primitive tells a boxed type from the type in the box.
  prim-on-box : nf {Γ = []} (papp false (capp tt (base 7))) ≡ nbase 1
  prim-on-box = refl

  prim-on-base : nf {Γ = []} (papp false (base 7)) ≡ nbase 0
  prim-on-base = refl

  -- The primitive `true` inspects below the outer box.
  prim-deep : nf {Γ = []} (papp true (capp tt (capp tt (base 7)))) ≡ nbase 1
  prim-deep = refl

  prim-separates : ¬ DefEq {Γ = []} (papp false (capp tt (base 7))) (papp false (base 7))
  prim-separates d =
    snotz (base-inj (d-trans (d-sym (δ-capp false tt (base 7)))
                             (d-trans d (δ-base false 7))))

  -- On a variable the primitive waits: the normal form is neutral.
  prim-stuck : nf {Γ = ★ ∷ []} (papp false (var vz)) ≡ ne (nstuck false (nvar vz))
  prim-stuck = refl

------------------------------------------------------------------------
-- T0 with the Affine algebra.

module T0-Affine where
  private
    S  = exSig Affine
    TS = exTSig Affine
  open Wager.L1.Syntax S using (Ty; ★; []; base; arr; _⊗_; capp)
  open Wager.L1.Conversion S
  open Wager.L1.Heads S
  open Wager.L2.Typing S TS affineOps
  open Wager.L2.Inversion S TS affine
  open Wager.L2.Preservation S TS affine using (inv-lam; inv-pair)

  Nat' : Ty [] ★
  Nat' = base 0

  Γ₀ : Cx 0
  Γ₀ ()

  ε : Usage 0
  ε = 0ᵘ

  -- (λ¹ x. x) 5
  redex : Tm 0
  redex = tapp (tlam a1 Nat' (tvar zero)) (lit 5)

  redex-typed : (ε +ᵘ (a1 ·ᵘ ε)) ▸ Γ₀ ⊢ redex ∶ Nat'
  redex-typed = t-app (t-lam (t-var zero)) (t-lit 5)

  redex-steps : redex ⟶ lit 5
  redex-steps = β-lam v-lit

  -- ACCEPTED (T0-Substitution): x[5/x], with x used at the grade 1.
  accepted-substitution : (ε +ᵘ (a1 ·ᵘ ε)) ▸ Γ₀ ⊢ lit 5 ∶ Nat'
  accepted-substitution = t0-substitution S TS affine (t-var zero) (t-lit 5)

  -- ACCEPTED (T0-Preservation): the reduct of the redex has the type.
  accepted-preservation : (ε +ᵘ (a1 ·ᵘ ε)) ▸ Γ₀ ⊢ lit 5 ∶ Nat'
  accepted-preservation = t0-preservation S TS affine redex-typed redex-steps

  -- ACCEPTED (T0-Progress): the redex is a value or it steps.
  accepted-progress : Value redex ⊎ (Σ[ t' ∈ Tm 0 ] (redex ⟶ t'))
  accepted-progress = t0-progress S TS affine redex-typed

  -- ACCEPTED (tropes): unwrap (wrap 5) has the raw type, and it steps
  -- to the raw value 5.
  roundTrip : Tm 0
  roundTrip = step false (step true (lit 5))

  roundTrip-typed : ε ▸ Γ₀ ⊢ roundTrip ∶ Nat'
  roundTrip-typed = t-step false (t-step true (t-lit 5))

  roundTrip-steps : roundTrip ⟶ lit 5
  roundTrip-steps = β-strip (v-step v-lit refl) refl

  accepted-trope : ε ▸ Γ₀ ⊢ lit 5 ∶ Nat'
  accepted-trope = t0-preservation S TS affine roundTrip-typed roundTrip-steps

  -- The boxed value has the boxed type, which is not the raw type.
  boxed-typed : ε ▸ Γ₀ ⊢ step true (lit 5) ∶ capp tt Nat'
  boxed-typed = t-step true (t-lit 5)

  boxed-not-raw : ¬ DefEq (capp tt Nat') Nat'
  boxed-not-raw d = headClash d refl

  ----------------------------------------------------------------------
  -- REJECTED: a binder of grade 1 whose body uses it two times.

  private
    no-dup : ∀ x y → leA a1 x ≡ true → leA a1 y ≡ true → leA (addA x y) a1 ≡ true → ⊥
    no-dup a0 y  p q r = false≢true p
    no-dup a1 a0 p q r = false≢true q
    no-dup a1 a1 p q r = false≢true r
    no-dup a1 aω p q r = false≢true r
    no-dup aω y  p q r = false≢true r

  dupBody : Tm 1
  dupBody = pair (tvar zero) (tvar zero)

  -- REJECTED (T0-Substitution): the body has no typing at the grade 1.
  rejected-substitution : ∀ {γ : Usage 0} {Γ : Cx 1} {C : Ty [] ★} →
                          ¬ ((γ ▹ a1) ▸ Γ ⊢ dupBody ∶ C)
  rejected-substitution d =
    let (A , B , γ₁ , γ₂ , c , le , d₁ , d₂) = inv-pair d
    in no-dup (γ₁ zero) (γ₂ zero)
              (fst (inv-var d₁) zero) (fst (inv-var d₂) zero) (le zero)

  dupFun : Tm 0
  dupFun = tlam a1 Nat' dupBody

  dupFun-rejected : ∀ {γ : Usage 0} {Γ : Cx 0} {C : Ty [] ★} → ¬ (γ ▸ Γ ⊢ dupFun ∶ C)
  dupFun-rejected d =
    let (B , γ' , c , le , d') = inv-lam d in rejected-substitution d'

  -- REJECTED (T0-Preservation): this term makes a step, and it has no
  -- typing. Preservation says nothing about it.
  dupRedex : Tm 0
  dupRedex = tapp dupFun (lit 5)

  dupRedex-steps : dupRedex ⟶ pair (lit 5) (lit 5)
  dupRedex-steps = β-lam v-lit

  rejected-preservation : ∀ {γ : Usage 0} {Γ : Cx 0} {C : Ty [] ★} → ¬ (γ ▸ Γ ⊢ dupRedex ∶ C)
  rejected-preservation d =
    let (q , A , B , γ₁ , γ₂ , c , le , d₁ , d₂) = inv-app d in dupFun-rejected d₁

  -- The same function with the grade ω is accepted.
  dupFunω-typed : ε ▸ Γ₀ ⊢ tlam aω Nat' dupBody ∶ arr aω Nat' (Nat' ⊗ Nat')
  dupFunω-typed =
    t-lam (t-sub (t-pair (t-var zero) (t-var zero)) (λ { zero → refl }))

  ----------------------------------------------------------------------
  -- REJECTED (T0-Progress): a closed term that is not a value and that
  -- makes no step. It has no typing.

  stuck : Tm 0
  stuck = tapp (lit 5) (lit 5)

  stuck-not-value : ¬ Value stuck
  stuck-not-value ()

  stuck-no-step : ∀ {t'} → ¬ (stuck ⟶ t')
  stuck-no-step (ξ-app₁ ())
  stuck-no-step (ξ-app₂ _ ())

  rejected-progress : ∀ {γ : Usage 0} {Γ : Cx 0} {C : Ty [] ★} → ¬ (γ ▸ Γ ⊢ stuck ∶ C)
  rejected-progress d =
    let (q , A , B , γ₁ , γ₂ , c , le , d₁ , d₂) = inv-app d
    in headClash (snd (inv-lit d₁)) refl

  ----------------------------------------------------------------------
  -- A finding. With the systemet order, 0 and 1 are not comparable.
  -- A binder of grade 1 that is NOT used is thus rejected: the grade 1
  -- is linear, not affine. The anytype order (0 ≤ 1) accepts it.

  dropFun : Tm 0
  dropFun = tlam a1 Nat' (lit 5)

  drop-rejected : ∀ {γ : Usage 0} {Γ : Cx 0} {C : Ty [] ★} → ¬ (γ ▸ Γ ⊢ dropFun ∶ C)
  drop-rejected d =
    let (B , γ' , c , le , d') = inv-lam d
    in false≢true (fst (inv-lit d') zero)

------------------------------------------------------------------------
-- T0 with the two-point lattice. The same rules give another
-- discipline: a `low` binder must be used, a `high` binder need not be.

module T0-Level where
  private
    S  = exSig Sec
    TS = exTSig Sec
  open Wager.L1.Syntax S using (Ty; ★; []; base; arr)
  open Wager.L2.Typing S TS levelOps
  open Wager.L2.Inversion S TS level
  open Wager.L2.Preservation S TS level using (inv-lam)

  Nat' : Ty [] ★
  Nat' = base 0

  Γ₀ : Cx 0
  Γ₀ ()

  ε : Usage 0
  ε = 0ᵘ

  redex : Tm 0
  redex = tapp (tlam low Nat' (tvar zero)) (lit 5)

  redex-typed : (ε +ᵘ (low ·ᵘ ε)) ▸ Γ₀ ⊢ redex ∶ Nat'
  redex-typed = t-app (t-lam (t-var zero)) (t-lit 5)

  -- ACCEPTED: T0 at the lattice instance.
  accepted-preservation : (ε +ᵘ (low ·ᵘ ε)) ▸ Γ₀ ⊢ lit 5 ∶ Nat'
  accepted-preservation = t0-preservation S TS level redex-typed (β-lam v-lit)

  -- ACCEPTED: a `high` binder that is not used.
  unusedHigh-typed : ε ▸ Γ₀ ⊢ tlam high Nat' (lit 5) ∶ arr high Nat' Nat'
  unusedHigh-typed = t-lam (t-sub (t-lit 5) (λ { zero → refl }))

  -- REJECTED: a `low` binder that is not used.
  unusedLow-rejected : ∀ {γ : Usage 0} {Γ : Cx 0} {C : Ty [] ★} →
                       ¬ (γ ▸ Γ ⊢ tlam low Nat' (lit 5) ∶ C)
  unusedLow-rejected d =
    let (B , γ' , c , le , d') = inv-lam d
    in false≢true (fst (inv-lit d') zero)

------------------------------------------------------------------------
-- The instance statements. ACCEPTED: `affine` and `level` are grade
-- algebras (Wager.Proofs). REJECTED: the Affine tables with one entry
-- changed (ω · 0 = ω) are not a grade algebra.

module Not-An-Algebra where
  open import Wager.Grade.Finite

  private
    badMul : Affine → Affine → Affine
    badMul aω a0 = aω
    badMul a  b  = mulA a b

    IsOmega : Affine → Type
    IsOmega aω = Unit
    IsOmega _  = ⊥

  badB : BoolOps Affine
  badB = record { add = addA ; mul = badMul ; zero = a0 ; one = a1 ; leB = leA }

  -- The Boolean check of the law `a · 0 = 0` computes to `false`.
  check-fails : Check.mul-zero? finAffine badB ≡ false
  check-fails = refl

  -- No proof of the laws exists for this structure.
  rejected : ¬ GradeLaws (toOps badB)
  rejected L = subst IsOmega (GradeLaws.mul-zero L aω) tt
