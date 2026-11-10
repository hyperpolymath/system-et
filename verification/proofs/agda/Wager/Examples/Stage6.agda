{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- Stage 6 anti-vacuity examples for T7, the separation.
--
-- The target signature of the examples is the signature of Stage 5:
-- `tSig` for `taggedS rep`, the row scheme, and the one-point grade
-- algebra. The base type of the GADT is `Int`.
module Wager.Examples.Stage6 where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Sigma using (_×_; _,_; Σ-syntax)
open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.FinData.Base using (Fin; zero; suc)
open import Cubical.Relation.Nullary using (¬_)

open import Wager.Grade.Trivial
open import Wager.Role.Role
open import Wager.FC.Tagged
import Wager.Trans.Scheme
import Wager.Trans.Target
import Wager.L1.Syntax
import Wager.L2.Typing
import Wager.L2.Erasure
open import Wager.Erased.Untyped
import Wager.Local.Source
import Wager.Local.Gadt
import Wager.Local.Separation
open import Wager.Proofs

private
  SS = taggedS rep
  Sc = Wager.Trans.Scheme.rowScheme SS

open Wager.Trans.Target SS Sc trivialOps using (tSig; tTSig)
open Wager.L1.Syntax tSig using (Ty; []; ★; base; arr; _⊕_; Base)
open Wager.L2.Typing tSig tTSig trivialOps
open Wager.L2.Erasure tSig tTSig trivialOps using (erT; eraseᵗ; identity-one-type)
open Typing litTy using (_⊢ᵉ_∶_; ∅ᶜ; u-var; u-lam; u-app; u-case)
open Wager.Local.Source Base Lit litTy
open Wager.Local.Gadt Base Lit litTy
open Wager.Local.Separation tSig tTSig trivialOps using (gadt-evalᵘ; erased-program)

private
  variable
    τ σ : LTy

  tInt : Ty [] ★
  tInt = base bInt

  lInt : LTy
  lInt = lbase bInt

  -- The empty target context and its usage vector.
  ∅ᵗ : Cx 0
  ∅ᵗ ()

  ∅ᵘ : Usage 0
  ∅ᵘ _ = tt

------------------------------------------------------------------------
-- Accepted: the source program.

-- The program is a term of the source calculus at each instance.
-- Here: the instances `a := Int` and `a := Int + Int`.
eval-at-int : LTm ∅ᵃ ∅ˡ (G bInt lInt ⇒ˡ lInt)
eval-at-int = gadt-eval bInt lInt

eval-at-sum : LTm ∅ᵃ ∅ˡ (G bInt (lInt +ˡ lInt) ⇒ˡ lInt)
eval-at-sum = gadt-eval bInt (lInt +ˡ lInt)

-- The text of the program does not depend on the instance.
one-erased-text : ∀ α α' → eraseˡ (gadt-eval bInt α) ≡ eraseˡ (gadt-eval bInt α')
one-erased-text α α' = refl

-- The constructor GI at the instance `a := Int`, with the literal `ℓint`.
-- The evidence is reflexivity.
gi-one : LTm ∅ᵃ ∅ˡ (G bInt lInt)
gi-one = linl (lpack l-refl (llit ℓint))

-- The first branch runs: the erased program gives the literal.
live-branch-runs : ∅ᵉ ⊢ eraseˡ (lapp eval-at-int gi-one) ⇓ vlit ℓint
live-branch-runs =
  ⇓-app ⇓-lam (⇓-inl ⇓-lit)
    (⇓-casel (⇓-var zero) (⇓-app ⇓-lam (⇓-var zero) (⇓-var zero)))

------------------------------------------------------------------------
-- Rejected in the source: the constructor GB at the instance
-- `a := Int` needs evidence for `Int ~ Int + Int`. With no assumption,
-- an equality of the source calculus is the identity of types.

closed-equality-is-identity : Coˡ ∅ᵃ τ σ → τ ≡ σ
closed-equality-is-identity l-refl        = refl
closed-equality-is-identity (l-sym γ)     = sym (closed-equality-is-identity γ)
closed-equality-is-identity (l-trans γ δ) =
  closed-equality-is-identity γ ∙ closed-equality-is-identity δ
closed-equality-is-identity (l-arr γ δ)   =
  cong₂ _⇒ˡ_ (closed-equality-is-identity γ) (closed-equality-is-identity δ)
closed-equality-is-identity (l-sum γ δ)   =
  cong₂ _+ˡ_ (closed-equality-is-identity γ) (closed-equality-is-identity δ)

private
  IsLBase : LTy → Type
  IsLBase (lbase b)     = Unit
  IsLBase (τ ⇒ˡ σ)      = ⊥
  IsLBase (τ +ˡ σ)      = ⊥
  IsLBase (⟨ τ ~ σ ⟩ ρ) = ⊥

no-evidence-for-gb : ¬ Coˡ ∅ᵃ lInt (lInt +ˡ lInt)
no-evidence-for-gb γ = subst IsLBase (closed-equality-is-identity γ) tt

------------------------------------------------------------------------
-- Rejected in the target: the instance of T7 for this signature, at
-- the instance `a := Int` of the program.

no-target-term :
  ¬ (Σ[ t ∈ Tm 0 ] Σ[ A ∈ Ty [] ★ ]
       (∅ᵘ ▸ ∅ᵗ ⊢ t ∶ A)
     × (erT A ≡ erˡ (G bInt lInt ⇒ˡ lInt))
     × (eraseᵗ t ≡ eraseˡ eval-at-int))
no-target-term (t , A , d , eA , eT) =
  t7-separation tSig tTSig trivialOps bInt lInt d eA eT

-- The simplest case of "no hypothetical equality": the identity
-- function has no type `Int → Int + Int` in the target.
identity-rejected :
  ¬ (∅ᵘ ▸ ∅ᵗ ⊢ tlam tt tInt (tvar zero) ∶ arr tt tInt (tInt ⊕ tInt))
identity-rejected d = subst IsBaseE (identity-one-type d refl) tt
  where
  IsBaseE : ETy Base → Type
  IsBaseE (ebase x)   = Unit
  IsBaseE (earr a c)  = ⊥
  IsBaseE (eprod a c) = ⊥
  IsBaseE (esum a c)  = ⊥

------------------------------------------------------------------------
-- Accepted in the target, with another type of the data. This shows
-- what T7 does not exclude (DC-6.4): the erased program has a simple
-- type when the argument of GB has the erased type `Int + Int`.

other-erased-type :
  ∅ᶜ ⊢ᵉ gadt-evalᵘ ∶ earr (esum (ebase bInt) (esum (ebase bInt) (ebase bInt))) (ebase bInt)
other-erased-type =
  u-lam (u-case (u-var zero refl)
    (u-app (u-lam (u-var zero refl)) (u-var zero refl))
    (u-app (u-lam (u-case (u-var zero refl) (u-var zero refl) (u-var zero refl)))
           (u-var zero refl)))

-- A typed target term with the erasure of the source program. Its type
-- does not have the erased type of the source type.
private
  other : Tm 0
  other =
    tlam tt (tInt ⊕ (tInt ⊕ tInt))
      (case (tvar zero)
        (tapp (tlam tt tInt (tvar zero)) (tvar zero))
        (tapp (tlam tt (tInt ⊕ tInt) (case (tvar zero) (tvar zero) (tvar zero)))
              (tvar zero)))

other-typed : ∅ᵘ ▸ ∅ᵗ ⊢ other ∶ arr tt (tInt ⊕ (tInt ⊕ tInt)) tInt
other-typed =
  t-lam (t-case (t-var zero)
    (t-app (t-lam (t-var zero)) (t-var zero))
    (t-app (t-lam (t-case (t-var zero) (t-var zero) (t-var zero))) (t-var zero)))

other-same-erasure : eraseᵗ other ≡ eraseˡ eval-at-int
other-same-erasure = refl
