{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- DESIGN-CHOICES.adoc, DC-0.3: matches on kinded syntax.
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- Stage 2 anti-vacuity examples. Each theorem of Stage 2 has one closed
-- example that satisfies the hypotheses, and one closed example that
-- the system rejects. The rejected examples that are also statements
-- (T4, the Proxy test) are in Wager.Proofs. This file has the others.
module Wager.Examples.Stage2 where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool.Base using (Bool; true; false)
open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.FinData.Base using (Fin; zero; suc)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Sigma using (_×_; Σ-syntax)
open import Cubical.Relation.Nullary using (¬_)

open import Wager.Grade.Affine
open import Wager.Role.Role
open import Wager.Role.Table
open import Wager.Role.Signature
open import Wager.Role.Classic
import Wager.Role.ClassicProofs as CP
import Wager.L1.Syntax
import Wager.L1.Conversion
import Wager.L1.Normal
import Wager.L1.Eval
import Wager.L1.Heads
import Wager.L1.Kinding
import Wager.Role.RepEq
import Wager.Role.Validity
import Wager.L2.Typing
import Wager.L2.Inversion
open import Wager.Proofs

------------------------------------------------------------------------
-- T2 with the lawful table. The signature is `classicSig rep`: `proxy`
-- has the declared grade representational, and the signature is valid.

module T2-Examples where
  private
    RS = classicSig rep
    S  = toSig RS
  open Wager.L1.Syntax S
  open Wager.L1.Normal S
  open Wager.L1.Eval S
  open Wager.Role.RepEq RS
  open Types rep
  open CP.LawfulKinding rep

  -- λa. a →[1] Proxy a
  arrF : Ty [] (★ ⇒[ rep ] ★)
  arrF = lam (arr a1 (var vz) (Proxy (var vz)))

  arrF-kinded : ε ⊢ᵏ arrF
  arrF-kinded = k-lam (k-sub (k-arr (k-var vz) (k-capp proxy (k-var vz))) le)
    where
    le : (unitᵏ vz ⊕ᵏ (rep ⊙ᵏ unitᵏ vz)) ≼ᵏ (ε ▹ᵏ rep)
    le k vz = refl

  -- ACCEPTED (T2-Representational): the newtype coercion lifts through
  -- the arrow and through `proxy`:  (Age → Proxy Age) ≈ (Int → Proxy Int).
  accepted-representational : nf (app arrF Age) ≈ nf (app arrF Int)
  accepted-representational =
    t2-representational RS CP.ProxyB.valid arrF arrF-kinded refl Age Int (CP.Generic.age≈int rep)

  -- ACCEPTED (T2-Phantom): `constF` does not use its parameter, so its
  -- results on Age and on Bool have the same normal form.
  accepted-phantom : nf (app (constF ph) Age) ≡ nf (app (constF ph) Bool')
  accepted-phantom =
    t2-phantom RS CP.ProxyB.valid (constF ph) constF-phantom Age Bool'

  -- REJECTED: `classicF` has no kinding at the grade representational
  -- (this is T4), so T2 says nothing about it. Its results differ.
  rejected : (¬ (ε ⊢ᵏ classicF rep))
             × (¬ (nf (app (classicF rep) Age) ≈ nf (app (classicF rep) Int)))
  rejected = t4-kinding-rejects rep refl ε , snd t4-not-equivalent rep

  -- ACCEPTED (T4, anti-vacuity): the same function has a kinding at the
  -- grade nominal. The kinding judgement does not reject everything.
  classic-at-nominal : ε ⊢ᵏ classicF nom
  classic-at-nominal = classicF-nominal

------------------------------------------------------------------------
-- Noninterference with the GHC table. The proof does not use the law
-- `a · 𝟘 = 𝟘`, so the GHC table is an instance.

module GHC-Examples where
  private
    RS = classicSig rep
    S  = toSig RS
  open Wager.L1.Syntax S
  open Wager.L1.Normal S
  open Wager.L1.Eval S
  open Wager.L1.Kinding S (tableOps tableG)
  open Wager.Role.RepEq RS
  open Wager.Role.Validity RS mulG
  open Types rep

  private
    ε : KUsage []
    ε k ()

  -- `classicSig rep` respects its declared grades with the GHC table.
  valid-ghc : Valid
  valid-ghc = record { cvalid = cv ; pvalid = pv }
    where
    cv : ∀ c ρ {v w} → R★ (mulG ρ (cgrade c)) v w → R★ ρ (ncapp c v) (ncapp c w)
    cv age   ph  h = tt
    cv age   rep h = ≈-capp age h
    cv age   nom h = cong (ncapp age) h
    cv proxy ph  h = tt
    cv proxy rep h = ≈-capp proxy h
    cv proxy nom h = cong (ncapp proxy) h

    pv : ∀ p ρ {v w} → R★ (mulG ρ (pgrade p)) v w → R★ ρ (inspect p v) (inspect p w)
    pv p ph  h = tt
    pv p rep h = ≡→≈ (cong (inspect p) h)
    pv p nom h = cong (inspect p) h

  arrF : Ty [] (★ ⇒[ rep ] ★)
  arrF = lam (arr a1 (var vz) (Proxy (var vz)))

  arrF-kinded : ε ⊢ᵏ arrF
  arrF-kinded = k-lam (k-sub (k-arr (k-var vz) (k-capp proxy (k-var vz))) le)
    where
    le : (unitᵏ vz ⊕ᵏ (rep ⊙ᵏ unitᵏ vz)) ≼ᵏ (ε ▹ᵏ rep)
    le k vz = refl

  -- ACCEPTED: a representational observer and a representational grade.
  accepted : nf (app arrF Age) ≈ nf (app arrF Int)
  accepted =
    noninterference RS tableG valid-ghc arrF arrF-kinded rep Age Int (CP.Generic.age≈int rep)

  -- With the GHC table, the grade phantom gives `≈` for all arguments.
  -- It does not give `≡`: a nominal observer needs equal arguments,
  -- because nominal · phantom = nominal.
  ghc-phantom : (F : Ty [] (★ ⇒[ ph ] ★)) {γ : KUsage []} → γ ⊢ᵏ F →
                (A B : Ty [] ★) → nf (app F A) ≈ nf (app F B)
  ghc-phantom F d A B = noninterference RS tableG valid-ghc F d rep A B tt

------------------------------------------------------------------------
-- The newtype `Age` as a two-state trope on Int, with the Affine
-- algebra on the term grades.

module Trope-Examples where
  private
    RS = classicSig rep
    S  = toSig RS
  open Wager.L1.Syntax S using (Ty; ★; []; base; capp)
  open Wager.L1.Conversion S
  open Wager.L1.Heads S
  open Types rep
  private TS = classicTSig
  open Wager.L2.Typing S TS affineOps
  open Wager.L2.Inversion S TS affine

  Γ₀ : Cx 0
  Γ₀ ()

  ε : Usage 0
  ε = 0ᵘ

  -- ACCEPTED: wrap 5 has the type Int@age.
  wrapped-typed : ε ▸ Γ₀ ⊢ step wrapAge (lit 5) ∶ Age
  wrapped-typed = t-step wrapAge (t-lit 5)

  -- ACCEPTED: unwrap (wrap 5) has the type Int, and it reduces to 5.
  roundTrip-typed : ε ▸ Γ₀ ⊢ step unwrapAge (step wrapAge (lit 5)) ∶ Int
  roundTrip-typed = t-step unwrapAge wrapped-typed

  roundTrip-steps : step unwrapAge (step wrapAge (lit 5)) ⟶ lit {n = 0} 5
  roundTrip-steps = β-strip (v-step v-lit refl) refl

  -- REJECTED: unwrap 5 has no typing. The transition `unwrapAge` starts
  -- at the state `age`, and the literal has the raw type.
  unwrap-raw-rejected : ∀ {γ : Usage 0} {C : Ty [] ★} →
                        ¬ (γ ▸ Γ₀ ⊢ step unwrapAge (lit 5) ∶ C)
  unwrap-raw-rejected d =
    let (γ' , c , le , d') = inv-step d
    in headClash (snd (inv-lit d')) refl

  -- REJECTED: wrap 5 does not have the raw type. No conversion relates
  -- Int@age and Int: the only way between them is a transition.
  wrapped-not-raw : ¬ DefEq {Γ = []} Age Int
  wrapped-not-raw d = headClash d refl
