{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- DESIGN-CHOICES.adoc, DC-0.3: matches on kinding derivations.
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- Inversion of graded kinding through the subusage rule `k-sub`.
-- A proof that a type has NO kinding derivation at a grade uses these
-- lemmas. They need the order `≤` to be reflexive and transitive.
open import Cubical.Foundations.Prelude
open import Wager.L1.Signature
open import Wager.Grade.Algebra

module Wager.L1.KindingInversion
  (S : Sig) (K : GradeOps (Sig.KG S))
  (le-refl  : ∀ a → GradeOps._≤_ K a a)
  (le-trans : ∀ a b c → GradeOps._≤_ K a b → GradeOps._≤_ K b c → GradeOps._≤_ K a c)
  where

open import Cubical.Data.Sigma using (_×_; Σ-syntax)

open import Wager.L1.Syntax S
open import Wager.L1.Kinding S K
open GradeOps K

private
  variable
    Γ   : Ctx
    k j : Kind
    g   : KG

≼ᵏ-refl : (γ : KUsage Γ) → γ ≼ᵏ γ
≼ᵏ-refl γ k x = le-refl (γ k x)

≼ᵏ-trans : {γ δ ε : KUsage Γ} → γ ≼ᵏ δ → δ ≼ᵏ ε → γ ≼ᵏ ε
≼ᵏ-trans p q k x = le-trans _ _ _ (p k x) (q k x)

inv-k-var : {γ : KUsage Γ} {x : Var Γ k} → γ ⊢ᵏ var x → unitᵏ x ≼ᵏ γ
inv-k-var (k-var x)    = ≼ᵏ-refl _
inv-k-var (k-sub d le) = ≼ᵏ-trans (inv-k-var d) le

inv-k-base : ∀ {γ : KUsage Γ} {b} → γ ⊢ᵏ base b → 0ᵏ ≼ᵏ γ
inv-k-base (k-base b)   = ≼ᵏ-refl _
inv-k-base (k-sub d le) = ≼ᵏ-trans (inv-k-base d) le

inv-k-capp : ∀ {γ : KUsage Γ} {c} {A : Ty Γ ★} → γ ⊢ᵏ capp c A →
             Σ[ δ ∈ KUsage Γ ] (δ ⊢ᵏ A) × ((cgrade c ⊙ᵏ δ) ≼ᵏ γ)
inv-k-capp (k-capp c d) = _ , d , ≼ᵏ-refl _
inv-k-capp (k-sub d le) =
  let (δ , d' , le') = inv-k-capp d in δ , d' , ≼ᵏ-trans le' le

inv-k-papp : ∀ {γ : KUsage Γ} {p} {A : Ty Γ ★} → γ ⊢ᵏ papp p A →
             Σ[ δ ∈ KUsage Γ ] (δ ⊢ᵏ A) × ((pgrade p ⊙ᵏ δ) ≼ᵏ γ)
inv-k-papp (k-papp p d) = _ , d , ≼ᵏ-refl _
inv-k-papp (k-sub d le) =
  let (δ , d' , le') = inv-k-papp d in δ , d' , ≼ᵏ-trans le' le

inv-k-lam : {γ : KUsage Γ} {b : Ty (k ∷ Γ) j} → γ ⊢ᵏ lam {g = g} b →
            Σ[ γ' ∈ KUsage Γ ] ((γ' ▹ᵏ g) ⊢ᵏ b) × (γ' ≼ᵏ γ)
inv-k-lam (k-lam d)    = _ , d , ≼ᵏ-refl _
inv-k-lam (k-sub d le) =
  let (γ' , d' , le') = inv-k-lam d in γ' , d' , ≼ᵏ-trans le' le
