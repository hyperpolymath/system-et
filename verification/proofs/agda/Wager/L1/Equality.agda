{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- DESIGN-CHOICES.adoc, DC-0.3: matches on kinded syntax.
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- "Equality is conversion" for this language: conversion is
-- normalize-then-compare (the ET-2 headline `defEq_iff_nf` of the
-- Lean development, for the language with the signature).
open import Wager.L1.Signature

module Wager.L1.Equality (S : Sig) where

open import Cubical.Foundations.Prelude

open import Wager.L1.Syntax S
open import Wager.L1.Conversion S
open import Wager.L1.Normal S
open import Wager.L1.Eval S
open import Wager.L1.Completeness S using (completeness)
open import Wager.L1.Soundness S using (soundness)

private
  variable
    Γ : Ctx
    k : Kind

defEq→nf : {t u : Ty Γ k} → DefEq t u → nf t ≡ nf u
defEq→nf = completeness

nf→defEq : {t u : Ty Γ k} → nf t ≡ nf u → DefEq t u
nf→defEq {t = t} {u = u} p =
  d-trans (soundness t) (d-trans (≡→DefEq (cong embNf p)) (d-sym (soundness u)))
