{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- DESIGN-CHOICES.adoc, DC-0.3: matches on normal forms and on evaluations.
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- Stage 6, part 2: anti-vacuity examples for T7, the identity type.
--
-- The signature of the examples is `Wager.Identity.Instance`, with one
-- base constant (`int`) and one literal (`one`). The grade algebra is
-- the one-point algebra, and for one example the algebra {0, 1, ω}.
module Wager.Examples.Stage6Identity where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Sigma using (_×_; _,_; Σ-syntax)
open import Cubical.Data.Sum.Base using (inl; inr)
open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.FinData.Base using (Fin; zero; suc)
open import Cubical.Relation.Nullary using (¬_)

open import Wager.Grade.Algebra
open import Wager.Grade.Trivial
open import Wager.Grade.Affine using (Affine; a0; a1; affineOps; affineLaws)
import Wager.Identity.Instance
import Wager.Identity.Typing
import Wager.L1.Syntax
import Wager.L1.Normal
import Wager.L1.Conversion
import Wager.L1.Equality
import Wager.L2.Erasure
open import Wager.Erased.Untyped
import Wager.Erased.LogRel
open import Wager.Proofs

-- The start of the signature: one base constant and one literal.
data B₀ : Type where
  int : B₀

data L₀ : Type where
  one : L₀

open Wager.Identity.Instance B₀ L₀ (λ _ → int) trivialOps
open Wager.L1.Syntax sig using (Ty; []; ★; base; arr; _⊗_; _⊕_)
open Wager.L1.Normal sig using (Nf; nbase)
open Wager.L1.Conversion sig using (DefEq; d-refl)
open Wager.L1.Equality sig using (defEq→nf)
open Wager.L2.Erasure sig tsig trivialOps using (erT)
open Wager.Identity.Typing sig tsig trivialOps family
open Terms Lit
open Wager.Erased.LogRel litTy using (FO; fo-base)

private
  -- The empty context and its usage vector.
  ∅ᵗ : Cx 0
  ∅ᵗ ()

  ∅ᵘ : Usage 0
  ∅ᵘ ()

tInt : Ty [] ★
tInt = base (cb int)

ℓone : Lit
ℓone = inl one

------------------------------------------------------------------------
-- The family is not empty, and it is the family of the instance.

-- The constant `Id Int Int` is `cid` at the code of `Int`, two times.
id-int-int : Id tInt tInt ≡ cid (cq (cb int)) (cq (cb int))
id-int-int = refl

------------------------------------------------------------------------
-- T7-Intro and T7-Erasure. ACCEPTED: a cast along `rfl`.

-- A conversion gives evidence.
evidence-int : ∅ᵘ ▸ ∅ᵗ ⊢ⁱ ilit (rfl tInt) ∶ base (Id tInt tInt)
evidence-int = t7-intro sig tsig trivialOps family {A = tInt} {B = tInt} d-refl

-- The literal one, moved from Int to Int along the evidence.
cast-one : ITm 0
cast-one = cast (ilit (rfl tInt)) (ilit ℓone)

cast-one-typed : ∅ᵘ ▸ ∅ᵗ ⊢ⁱ cast-one ∶ tInt
cast-one-typed = t-cast {A = tInt} {B = tInt} evidence-int (t-lit ℓone)

-- The erasure of proofs has no evidence.
cast-one-erased : eraseⁱ cast-one ≡ ulit ℓone
cast-one-erased = refl

-- The reference program evaluates the evidence, then the literal.
cast-one-keep : ∅ᵉ ⊢ keepⁱ cast-one ⇓ vlit ℓone
cast-one-keep = ⇓-letp (⇓-pair ⇓-lit ⇓-lit) (⇓-var zero)

cast-one-erase : ∅ᵉ ⊢ eraseⁱ cast-one ⇓ vlit ℓone
cast-one-erase = ⇓-lit

-- T7 at a first-order type: one value for the two programs.
cast-one-sound :
  Σ[ v ∈ UVal ] (∅ᵉ ⊢ keepⁱ cast-one ⇓ v) × (∅ᵉ ⊢ eraseⁱ cast-one ⇓ v)
cast-one-sound =
  t7-erasure-first-order sig tsig trivialOps family cast-one-typed fo-base

------------------------------------------------------------------------
-- T7-Canonicity. REJECTED: closed evidence that Int is Int + Int.

private
  IsNBase : Nf [] ★ → Type
  IsNBase (nbase _) = Unit
  IsNBase _         = ⊥

no-evidence : ∀ {e : ITm 0} → ¬ (∅ᵘ ▸ ∅ᵗ ⊢ⁱ e ∶ base (Id tInt (tInt ⊕ tInt)))
no-evidence d =
  subst IsNBase
    (defEq→nf (t7-canonicity sig tsig trivialOps family {A = tInt} {B = tInt ⊕ tInt} d)) tt

------------------------------------------------------------------------
-- T7-Erasure. REJECTED: a cast whose evidence has no value. The term
-- has no type, and the conclusion of T7 is false for it.

-- The evidence is the application of a literal to a literal.
stuck : ITm 0
stuck = cast (iapp (ilit ℓone) (ilit ℓone)) (ilit ℓone)

-- The program with no evidence has a value.
stuck-erase : ∅ᵉ ⊢ eraseⁱ stuck ⇓ vlit ℓone
stuck-erase = ⇓-lit

-- The reference program has no value: a literal is not a function.
stuck-keep : ∀ {v} → ¬ (∅ᵉ ⊢ keepⁱ stuck ⇓ v)
stuck-keep (⇓-letp (⇓-pair (⇓-app () _ _) _) _)

-- So the term has no type (by T7).
stuck-untyped : ∀ {A} → ¬ (∅ᵘ ▸ ∅ᵗ ⊢ⁱ stuck ∶ A)
stuck-untyped d =
  let (v , w , dv , dw , h) = t7-erasure sig tsig trivialOps family d
  in stuck-keep dv

------------------------------------------------------------------------
-- T7-Assumption. ACCEPTED: a local equality assumption.

-- A typed closed function from Int to Int + Int, under the assumption
-- that the two types are equal.
assume : ITm 0
assume = use-assumption tInt (tInt ⊕ tInt)

assume-typed :
  ∅ᵘ ▸ ∅ᵗ ⊢ⁱ assume ∶ arr tt (base (Id tInt (tInt ⊕ tInt))) (arr tt tInt (tInt ⊕ tInt))
assume-typed =
  t7-assumption sig tsig trivialOps family trivialLaws tInt (tInt ⊕ tInt)

-- Its erasure is `λ e. λ x. x`. The inner function is the identity, from
-- Int to Int + Int. In the target with no family, a typed function that
-- erases to the identity has one erased type on its two sides
-- (`Wager.L2.Erasure.identity-one-type`).
assume-erased : eraseⁱ assume ≡ ulam (ulam (uvar zero))
assume-erased = refl

-- No closed term can be its argument (`no-evidence`): the assumption is
-- false, so the body does not run in a closed typed program.

-- The same function in the algebra {0, 1, ω}: the assumption has the
-- grade 0, the grade of an unused assumption.
module AtAffine where
  private module I = Wager.Identity.Instance B₀ L₀ (λ _ → int) affineOps
  open Wager.L1.Syntax I.sig using () renaming (Ty to Tyᵃ; [] to []ᵃ; ★ to ★ᵃ; base to baseᵃ; arr to arrᵃ; _⊕_ to _⊕ᵃ_)
  open Wager.Identity.Typing I.sig I.tsig affineOps I.family
    using () renaming (_▸_⊢ⁱ_∶_ to _▸_⊢ᵃ_∶_; use-assumption to use-assumptionᵃ; Id to Idᵃ; 0ᵘ to 0ᵃ; Cx to Cxᵃ)

  private
    tIntᵃ : Tyᵃ []ᵃ ★ᵃ
    tIntᵃ = baseᵃ (I.cb int)

    ∅ᵃ : Cxᵃ 0
    ∅ᵃ ()

  assume-affine :
    0ᵃ ▸ ∅ᵃ ⊢ᵃ use-assumptionᵃ tIntᵃ (tIntᵃ ⊕ᵃ tIntᵃ)
      ∶ arrᵃ a0 (baseᵃ (Idᵃ tIntᵃ (tIntᵃ ⊕ᵃ tIntᵃ))) (arrᵃ a1 tIntᵃ (tIntᵃ ⊕ᵃ tIntᵃ))
  assume-affine =
    t7-assumption I.sig I.tsig affineOps I.family affineLaws tIntᵃ (tIntᵃ ⊕ᵃ tIntᵃ)

------------------------------------------------------------------------
-- The GADT program of part 1, in the extension. ACCEPTED.
--
-- The data holds the evidence: a constructor is a pair of the evidence
-- and the payload. The Agda variable α is the type variable of the
-- Haskell text (DESIGN-CHOICES.adoc, DC-6.2).

Gⁱ : Ty [] ★ → Ty [] ★
Gⁱ α = (base (Id α tInt) ⊗ α) ⊕ (base (Id α (tInt ⊕ tInt)) ⊗ α)

evalⁱ : Ty [] ★ → ITm 0
evalⁱ α =
  ilam tt (Gⁱ α) (icase (ivar zero)
    (iletp (ivar zero) (cast (ivar (suc zero)) (ivar zero)))
    (iletp (ivar zero)
      (icase (cast (ivar (suc zero)) (ivar zero)) (ivar zero) (ivar zero))))

-- The program is typed for each α, in the one-point algebra.
evalⁱ-typed : ∀ α → ∅ᵘ ▸ ∅ᵗ ⊢ⁱ evalⁱ α ∶ arr tt (Gⁱ α) tInt
evalⁱ-typed α =
  t-lam (t-case (t-var zero)
    (t-letp (t-var zero) (t-cast (t-var (suc zero)) (t-var zero)))
    (t-letp (t-var zero)
      (t-case (t-cast (t-var (suc zero)) (t-var zero)) (t-var zero) (t-var zero))))

-- One erased text for each α. No cast and no evidence is in it, except
-- the evidence that the data holds.
evalⁱ-erased : ∀ α → eraseⁱ (evalⁱ α) ≡
  ulam (ucase (uvar zero)
    (uletp (uvar zero) (uvar zero))
    (uletp (uvar zero) (ucase (uvar zero) (uvar zero) (uvar zero))))
evalⁱ-erased α = refl

-- The program at α := Int, on the first constructor with the literal one.
gi-one : ITm 0
gi-one = iapp (evalⁱ tInt) (iinj₁ (ipair (ilit (rfl tInt)) (ilit ℓone)))

gi-one-typed : ∅ᵘ ▸ ∅ᵗ ⊢ⁱ gi-one ∶ tInt
gi-one-typed =
  t-app (evalⁱ-typed tInt) (t-inj₁ (t-pair evidence-int (t-lit ℓone)))

-- The erased program gives the literal one.
gi-one-runs : ∅ᵉ ⊢ eraseⁱ gi-one ⇓ vlit ℓone
gi-one-runs =
  ⇓-app ⇓-lam (⇓-inl (⇓-pair ⇓-lit ⇓-lit))
    (⇓-casel (⇓-var zero) (⇓-letp (⇓-var zero) (⇓-var zero)))

-- T7: the reference program and the erased program give one value.
gi-one-sound :
  Σ[ v ∈ UVal ] (∅ᵉ ⊢ keepⁱ gi-one ⇓ v) × (∅ᵉ ⊢ eraseⁱ gi-one ⇓ v)
gi-one-sound =
  t7-erasure-first-order sig tsig trivialOps family gi-one-typed fo-base

-- THE LIMIT (DESIGN-CHOICES.adoc, DC-6.7). The erased type of the data
-- has a component for the evidence. In part 1 the erased type of the
-- source data has no such component.
data-holds-evidence : erT (Gⁱ tInt) ≡
  esum (eprod (ebase (Id tInt tInt)) (ebase (cb int)))
       (eprod (ebase (Id tInt (tInt ⊕ tInt))) (ebase (cb int)))
data-holds-evidence = refl
