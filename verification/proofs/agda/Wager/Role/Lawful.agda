{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- T2 with the lawful table, and a sufficient condition for a
-- signature to respect its declared grades.
open import Wager.Role.Signature

module Wager.Role.Lawful (RS : RoleSig) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool.Base using (Bool; true; false)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Relation.Nullary using (¬_)

open import Wager.Role.Role
open import Wager.Role.Table
open import Wager.L1.Syntax (toSig RS)
open import Wager.L1.Normal (toSig RS)
open import Wager.L1.Eval (toSig RS)
open import Wager.L1.Kinding (toSig RS) (tableOps tableZ)
open import Wager.Role.RepEq RS
open import Wager.Role.Validity RS mulZ
open import Wager.Role.Noninterference RS tableZ

-- T2, first part: a grade below representational respects `≈`.
t2-representational :
  Valid →
  ∀ {r : Role} (F : Ty [] (★ ⇒[ r ] ★)) {γ : KUsage []} → γ ⊢ᵏ F →
  leR r rep ≡ true →
  (A B : Ty [] ★) → nf A ≈ nf B → nf (app F A) ≈ nf (app F B)
t2-representational V {r} F d le A B h =
  noninterference V F d rep A B (R★-anti r rep le h)

-- T2, second part: the grade phantom gives equal normal forms. The
-- proof uses the entry nominal · phantom = phantom of the lawful table.
t2-phantom :
  Valid →
  (F : Ty [] (★ ⇒[ ph ] ★)) {γ : KUsage []} → γ ⊢ᵏ F →
  (A B : Ty [] ★) → nf (app F A) ≡ nf (app F B)
t2-phantom V F d A B = noninterference V F d nom A B tt

------------------------------------------------------------------------
-- A sufficient condition for `Valid`, with the lawful table:
-- no constant has the parameter grade phantom, and each primitive has
-- the parameter grade nominal.

private
  capp-R★ : ∀ ρ c {v w : CNf} → R★ ρ v w → R★ ρ (ncapp c v) (ncapp c w)
  capp-R★ ph  c h = tt
  capp-R★ rep c h = ≈-capp c h
  capp-R★ nom c h = cong (ncapp c) h

  cvalid-at : ∀ g c ρ {v w : CNf} → ¬ (g ≡ ph) →
              R★ (mulZ ρ g) v w → R★ ρ (ncapp c v) (ncapp c w)
  cvalid-at ph  c ρ   n h = ⊥.rec (n refl)
  cvalid-at rep c ph  n h = tt
  cvalid-at rep c rep n h = ≈-capp c h
  cvalid-at rep c nom n h = cong (ncapp c) h
  cvalid-at nom c ph  n h = tt
  cvalid-at nom c rep n h = ≡→≈ (cong (ncapp c) h)
  cvalid-at nom c nom n h = cong (ncapp c) h

  pvalid-nom : ∀ p ρ {v w : CNf} → R★ (mulZ ρ nom) v w → R★ ρ (inspect p v) (inspect p w)
  pvalid-nom p ph  h = tt
  pvalid-nom p rep h = ≡→≈ (cong (inspect p) h)
  pvalid-nom p nom h = cong (inspect p) h

valid-lawful : (∀ c → ¬ (cgrade c ≡ ph)) → (∀ p → pgrade p ≡ nom) → Valid
valid-lawful noPh allNom = record
  { cvalid = λ c ρ h → cvalid-at (cgrade c) c ρ (noPh c) h
  ; pvalid = λ p ρ {v} {w} h →
      pvalid-nom p ρ (subst (λ g → R★ (mulZ ρ g) v w) (allNom p) h) }
