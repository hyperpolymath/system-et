{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- DESIGN-CHOICES.adoc, DC-0.3: matches on kinded syntax.
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- Role correspondence (Stage 4).
--
-- The body of a source newtype is a type-level function of the target.
-- Graded kinding of the target, with the lawful role table, accepts the
-- grade g for the parameter exactly when the inferred source role of
-- the parameter is at most g.
--
-- The target signature of the translation also respects its declared
-- grades (`Valid`), so the hypothesis of T2 holds for it.
open import Cubical.Foundations.Prelude
open import Wager.FC.Signature
open import Wager.Grade.Algebra
import Wager.Trans.Scheme

module Wager.Trans.RoleCorrespondence
  (SS : SSig) (Sc : Wager.Trans.Scheme.StateScheme SS)
  {R : Type} (ops : GradeOps R) where

open import Cubical.Data.Bool.Base using (true; false)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd; Σ-syntax)
open import Cubical.Relation.Nullary using (¬_)

open import Wager.Role.Role
open import Wager.Role.Table
open import Wager.FC.Types SS
open import Wager.Trans.Target SS Sc ops
open import Wager.L1.Kinding tSig (tableOps tableZ)
open import Wager.L1.KindingInversion tSig (tableOps tableZ) leR-refl leR-trans
import Wager.Role.Validity
import Wager.Role.Lawful

private
  -- The usage vector of the one type variable of a body.
  only : Role → KUsage (★ ∷ [])
  only g k vz = g

  ε : KUsage []
  ε k ()

  only-≼ : ∀ {γ : KUsage (★ ∷ [])} g → leR (γ ★ vz) g ≡ true → γ ≼ᵏ only g
  only-≼ g le k vz = le

  -- The laws of the lawful role structure that the proofs use.
  module L = GradeLaws roleZLaws

  open-ty : Body Base Fam → Ty (★ ∷ []) ★
  open-ty β = TB β (var vz)

-- Kinding accepts the inferred role.
kind-body : ∀ β → only (roleOf β) ⊢ᵏ open-ty β
kind-body bvar        = k-sub (k-var vz) (only-≼ rep refl)
kind-body (bbase b)   = k-sub (k-base b) (only-≼ {γ = 0ᵏ} ph refl)
kind-body (barr β γ)  =
  k-sub (k-arr (kind-body β) (kind-body γ)) (only-≼ _ (leR-refl _))
kind-body (bprod β γ) =
  k-sub (k-prod (kind-body β) (kind-body γ)) (only-≼ _ (leR-refl _))
kind-body (bsum β γ)  =
  k-sub (k-sum (kind-body β) (kind-body γ)) (only-≼ _ (leR-refl _))
kind-body (bfam F β)  = k-sub (k-papp F (kind-body β)) (only-≼ _ (leR-refl _))

-- Each kinding derivation uses the parameter at the inferred role or above.
kind-body-inv : ∀ β {δ : KUsage (★ ∷ [])} → δ ⊢ᵏ open-ty β → leR (roleOf β) (δ ★ vz) ≡ true
kind-body-inv bvar        d = inv-k-var d ★ vz
kind-body-inv (bbase b)   d = refl
kind-body-inv (barr β γ)  d =
  let (δ₁ , δ₂ , d₁ , d₂ , le) = inv-k-arr d
  in leR-trans _ _ _
       (L.add-mono _ _ _ _ (kind-body-inv β d₁) (kind-body-inv γ d₂)) (le ★ vz)
kind-body-inv (bprod β γ) d =
  let (δ₁ , δ₂ , d₁ , d₂ , le) = inv-k-prod d
  in leR-trans _ _ _
       (L.add-mono _ _ _ _ (kind-body-inv β d₁) (kind-body-inv γ d₂)) (le ★ vz)
kind-body-inv (bsum β γ)  d =
  let (δ₁ , δ₂ , d₁ , d₂ , le) = inv-k-sum d
  in leR-trans _ _ _
       (L.add-mono _ _ _ _ (kind-body-inv β d₁) (kind-body-inv γ d₂)) (le ★ vz)
kind-body-inv (bfam F β)  d =
  let (δ' , d' , le) = inv-k-papp d
  in leR-trans _ _ _
       (L.mul-mono nom nom _ _ refl (kind-body-inv β d')) (le ★ vz)

-- THE CORRESPONDENCE.
role-correspondence : (N : N₁) (g : Role) →
    ((leR (roleOf (body N)) g ≡ true) → Σ[ γ ∈ KUsage [] ] (γ ⊢ᵏ bodyFun N g))
  × ((γ : KUsage []) → γ ⊢ᵏ bodyFun N g → leR (roleOf (body N)) g ≡ true)
role-correspondence N g =
    (λ le → ε , k-lam (k-sub (kind-body (body N)) (λ { k vz → le })))
  , (λ γ d → let (γ' , d' , _) = inv-k-lam d in kind-body-inv (body N) d')

role-check-is-kinding :
    (WellRoled → (N : N₁) → Σ[ γ ∈ KUsage [] ] (γ ⊢ᵏ bodyFun N (role N)))
  × (((N : N₁) → Σ[ γ ∈ KUsage [] ] (γ ⊢ᵏ bodyFun N (role N))) → WellRoled)
role-check-is-kinding =
    (λ wr N → fst (role-correspondence N (role N)) (wr N))
  , (λ h N → snd (role-correspondence N (role N)) (fst (h N)) (snd (h N)))

------------------------------------------------------------------------
-- The target signature respects its declared grades.

private
  IsRep : Role → Type
  IsRep rep = Unit
  IsRep _   = ⊥

target-valid : Wager.Role.Validity.Valid tRoleSig mulZ
target-valid =
  Wager.Role.Lawful.valid-lawful tRoleSig (λ c p → subst IsRep p tt) (λ p → refl)
