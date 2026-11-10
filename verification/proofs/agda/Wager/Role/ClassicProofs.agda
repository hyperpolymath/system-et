{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- DESIGN-CHOICES.adoc, DC-0.3: matches on kinded syntax.
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- T4 (the classic unsound program at the type level) and the Proxy
-- test of Stage 2, for the concrete signature of Wager.Role.Classic.
module Wager.Role.ClassicProofs where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool.Base using (Bool; true; false)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Sigma using (_×_; Σ-syntax)
open import Cubical.Relation.Nullary using (¬_)

open import Wager.Grade.Finite using (false≢true)
open import Wager.Role.Role
open import Wager.Role.Table
open import Wager.Role.Signature
open import Wager.Role.Classic
import Wager.L1.Syntax
import Wager.L1.Normal
import Wager.L1.Eval
import Wager.L1.Kinding
import Wager.L1.KindingInversion
import Wager.Role.RepEq
import Wager.Role.Validity
import Wager.Role.Lawful

private
  -- Facts about the role order, by computation.
  ph-not-above-rep : ∀ x → leR rep x ≡ true → leR (mulZ nom x) ph ≡ true → ⊥
  ph-not-above-rep ph  p q = false≢true p
  ph-not-above-rep rep p q = false≢true q
  ph-not-above-rep nom p q = false≢true q

  rep-not-above-nom : ∀ x → leR rep x ≡ true → leR (mulZ nom x) rep ≡ true → ⊥
  rep-not-above-nom ph  p q = false≢true p
  rep-not-above-nom rep p q = false≢true q
  rep-not-above-nom nom p q = false≢true q

  nom-below : ∀ g → leR g rep ≡ true → leR nom g ≡ true → ⊥
  nom-below ph  p q = false≢true q
  nom-below rep p q = false≢true q
  nom-below nom p q = false≢true p

  IsRep : Role → Type
  IsRep rep = Unit
  IsRep _   = ⊥

  rep≢ph : ¬ (rep ≡ ph)
  rep≢ph p = subst IsRep p tt

-- Lemmas that hold for each declared grade `pg` of `proxy`.
module Generic (pg : Role) where
  private S = toSig (classicSig pg)
  open Wager.L1.Syntax S
  open Wager.L1.Normal S
  open Wager.L1.Eval S
  open Wager.Role.RepEq (classicSig pg)
  open Types pg

  -- Discrimination of closed normal types.
  IsCharNf : Nf [] ★ → Type
  IsCharNf (nbase bChar) = Unit
  IsCharNf _             = ⊥

  IsIntArg : Nf [] ★ → Type
  IsIntArg (ncapp _ (nbase bInt)) = Unit
  IsIntArg _                      = ⊥

  char≉bool : ¬ (nbase bChar ≈ nbase bBool)
  char≉bool e = subst IsCharNf (≈→strip e) tt

  -- The newtype and its representation are equivalent.
  age≈int : nf {Γ = []} Age ≈ nf Int
  age≈int = ≈-unfold age refl

  -- `classicF` maps Age to Char and Int to Bool.
  classicF-age : ∀ g → nf (app (classicF g) Age) ≡ nbase bChar
  classicF-age g = refl

  classicF-int : ∀ g → nf (app (classicF g) Int) ≡ nbase bBool
  classicF-int g = refl

  classicF-separates : ∀ g → ¬ (nf (app (classicF g) Age) ≈ nf (app (classicF g) Int))
  classicF-separates g = char≉bool

  -- `deepF` looks below Proxy: it also maps Age to Char and Int to Bool.
  deepF-separates : ∀ g → ¬ (nf (app (deepF g) Age) ≈ nf (app (deepF g) Int))
  deepF-separates g = char≉bool

  proxyF-separates : ∀ g → ¬ (nf (app (proxyF g) Int) ≡ nf (app (proxyF g) Bool'))
  proxyF-separates g p = subst IsIntArg p tt

-- Kinding with the lawful table.
module LawfulKinding (pg : Role) where
  private S = toSig (classicSig pg)
  open Wager.L1.Syntax S
  open Wager.L1.Kinding S (tableOps tableZ) public
  open Wager.L1.KindingInversion S (tableOps tableZ) leR-refl leR-trans public
  open Types pg

  ε : KUsage []
  ε k ()

  -- T4: no derivation for `classicF` at a grade below representational.
  classicF-rejected : (g : Role) → leR g rep ≡ true → (γ : KUsage []) → ¬ (γ ⊢ᵏ classicF g)
  classicF-rejected g le γ d =
    let (γ' , d₁ , _)  = inv-k-lam d
        (δ , d₂ , le₂) = inv-k-papp d₁
        le₃            = inv-k-var d₂
    in reject g le (δ ★ vz) (le₃ ★ vz) (le₂ ★ vz)
    where
    reject : ∀ g → leR g rep ≡ true → ∀ x → leR rep x ≡ true → leR (mulZ nom x) g ≡ true → ⊥
    reject ph  _ x p q = ph-not-above-rep x p q
    reject rep _ x p q = rep-not-above-nom x p q
    reject nom l x p q = false≢true l

  -- `classicF` at the grade nominal has a derivation.
  classicF-nominal : ε ⊢ᵏ classicF nom
  classicF-nominal = k-lam (k-sub (k-papp isAge (k-var vz)) le)
    where
    le : (nom ⊙ᵏ unitᵏ vz) ≼ᵏ (ε ▹ᵏ nom)
    le k vz = refl

  -- `constF = λa. isAge Int` at the grade phantom has a derivation.
  constF-phantom : ε ⊢ᵏ constF ph
  constF-phantom = k-lam (k-sub (k-papp isAge (k-base bInt)) le)
    where
    le : (nom ⊙ᵏ 0ᵏ) ≼ᵏ (ε ▹ᵏ ph)
    le k vz = refl

------------------------------------------------------------------------
-- T4. The signature is `classicSig rep`.

module T4 where
  open Wager.L1.Syntax (toSig (classicSig rep)) using ([])
  open Generic rep
  open LawfulKinding rep

  t4-kinding-rejects : (g : Role) → leR g rep ≡ true → (γ : KUsage []) →
                       ¬ (γ ⊢ᵏ Types.classicF rep g)
  t4-kinding-rejects = classicF-rejected

  t4-not-equivalent-1 = age≈int
  t4-not-equivalent-2 = classicF-separates

------------------------------------------------------------------------
-- The Proxy test, part A: lawful table, `proxy` declared phantom.

module ProxyA where
  private S = toSig (classicSig ph)
  open Wager.L1.Syntax S
  open Wager.L1.Normal S
  open Wager.L1.Eval S
  open Generic ph
  open LawfulKinding ph
  open Types ph
  open Wager.Role.Validity (classicSig ph) mulZ

  -- Kinding accepts the grade phantom for `deepF`:
  -- nominal · (phantom · representational) = phantom.
  deepF-phantom : ε ⊢ᵏ deepF ph
  deepF-phantom = k-lam (k-sub (k-papp deep (k-capp proxy (k-var vz))) le)
    where
    le : (nom ⊙ᵏ (ph ⊙ᵏ unitᵏ vz)) ≼ᵏ (ε ▹ᵏ ph)
    le k vz = refl

  proxyF-phantom : ε ⊢ᵏ proxyF ph
  proxyF-phantom = k-lam (k-sub (k-capp proxy (k-var vz)) le)
    where
    le : (ph ⊙ᵏ unitᵏ vz) ≼ᵏ (ε ▹ᵏ ph)
    le k vz = refl

  -- The signature does not respect its declared grades: a nominal
  -- observer tells `Proxy Int` from `Proxy Bool`.
  not-valid : ¬ Valid
  not-valid V =
    proxyF-separates ph (Valid.cvalid V proxy nom {v = nbase bInt} {w = nbase bBool} tt)

------------------------------------------------------------------------
-- The Proxy test, part B: lawful table, `proxy` declared representational.

module ProxyB where
  private S = toSig (classicSig rep)
  open Wager.L1.Syntax S
  open Wager.L1.Normal S
  open Wager.L1.Eval S
  open Types rep
  open Wager.Role.RepEq (classicSig rep)
  open Wager.Role.Validity (classicSig rep) mulZ
  open Wager.Role.Lawful (classicSig rep) using (valid-lawful)

  valid : Valid
  valid = valid-lawful (λ { age → rep≢ph ; proxy → rep≢ph }) (λ p → refl)

  private
    IsProxyInt : Nf [] ★ → Type
    IsProxyInt (ncapp proxy (nbase bInt)) = Unit
    IsProxyInt _                          = ⊥

  -- `Proxy Int` and `Proxy Bool` are not equivalent.
  no-phantom-coercion : ¬ (nf {Γ = []} (Proxy Int) ≈ nf (Proxy Bool'))
  no-phantom-coercion e = subst IsProxyInt (≈→strip e) tt

------------------------------------------------------------------------
-- The Proxy test, part C: GHC table, `proxy` declared phantom.

module ProxyC where
  private S = toSig (classicSig ph)
  open Wager.L1.Syntax S
  open Types ph
  private
    module KG where
      open Wager.L1.Kinding S (tableOps tableG) public
      open Wager.L1.KindingInversion S (tableOps tableG) leR-refl leR-trans public

  -- The GHC table rejects each grade below nominal for `deepF`.
  ghc-rejects-deep : (g : Role) → leR g rep ≡ true → (γ : KG.KUsage []) →
                     ¬ (γ KG.⊢ᵏ deepF g)
  ghc-rejects-deep g le γ d =
    let (γ' , d₁ , _)  = KG.inv-k-lam d
        (δ , d₂ , le₂) = KG.inv-k-papp d₁
    in nom-below g le (le₂ ★ vz)

  -- The GHC table rejects the grade phantom for `constF`, which does
  -- not use its parameter: nominal · phantom = nominal.
  ghc-rejects-unused : (γ : KG.KUsage []) → ¬ (γ KG.⊢ᵏ constF ph)
  ghc-rejects-unused γ d =
    let (γ' , d₁ , _)  = KG.inv-k-lam d
        (δ , d₂ , le₂) = KG.inv-k-papp d₁
    in false≢true (le₂ ★ vz)
