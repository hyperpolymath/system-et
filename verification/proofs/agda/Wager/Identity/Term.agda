{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- The terms of the target with the identity family (Stage 6, part 2).
--
-- `ITm` is the term syntax of the target (`Wager.L2.Term.Tm`) with one
-- more former: `cast e t`. The term e is equality evidence, and t is
-- the payload. `emb` shows that each target term is a term here.
--
-- A term has two erasures into the untyped calculus:
--
--   keepⁱ   the reference. It evaluates the evidence of each cast, then
--           the payload, and gives the value of the payload. It does
--           not inspect the value of the evidence: the untyped calculus
--           has no test on a literal.
--   eraseⁱ  the erasure of proofs. The evidence of each cast is absent.
--           `eraseⁱ (cast e t)` is `eraseⁱ t`.
--
-- The two erasures are equal on a term with no cast.
open import Wager.L1.Signature
import Wager.L2.Signature
module Wager.Identity.Term (S : Sig) (TS : Wager.L2.Signature.TSig S) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.FinData.Base using (Fin; zero; suc)

open import Wager.L1.Syntax S
open import Wager.L2.Term S TS
open import Wager.Erased.Untyped
open Terms Lit

private
  variable
    n : ℕ

data ITm : ℕ → Type where
  ivar  : Fin n → ITm n
  ilam  : TG → Ty [] ★ → ITm (suc n) → ITm n
  iapp  : ITm n → ITm n → ITm n
  ipair : ITm n → ITm n → ITm n
  -- The body sees the first component at index 1 and the second at index 0.
  iletp : ITm n → ITm (suc (suc n)) → ITm n
  iinj₁ : ITm n → ITm n
  iinj₂ : ITm n → ITm n
  icase : ITm n → ITm (suc n) → ITm (suc n) → ITm n
  ilit  : Lit → ITm n
  istep : Op → ITm n → ITm n
  -- THE NEW FORMER: the evidence, then the payload.
  cast  : ITm n → ITm n → ITm n

-- Each target term is a term of the extension.
emb : Tm n → ITm n
emb (tvar i)     = ivar i
emb (tlam q A b) = ilam q A (emb b)
emb (tapp f a)   = iapp (emb f) (emb a)
emb (pair s t)   = ipair (emb s) (emb t)
emb (letp s b)   = iletp (emb s) (emb b)
emb (inj₁ t)     = iinj₁ (emb t)
emb (inj₂ t)     = iinj₂ (emb t)
emb (case s l r) = icase (emb s) (emb l) (emb r)
emb (lit ℓ)      = ilit ℓ
emb (step o t)   = istep o (emb t)

-- The reference erasure: each cast evaluates its evidence.
keepⁱ : ITm n → UTm n
keepⁱ (ivar i)      = uvar i
keepⁱ (ilam q A b)  = ulam (keepⁱ b)
keepⁱ (iapp f a)    = uapp (keepⁱ f) (keepⁱ a)
keepⁱ (ipair s t)   = upair (keepⁱ s) (keepⁱ t)
keepⁱ (iletp s b)   = uletp (keepⁱ s) (keepⁱ b)
keepⁱ (iinj₁ t)     = uinl (keepⁱ t)
keepⁱ (iinj₂ t)     = uinr (keepⁱ t)
keepⁱ (icase s l r) = ucase (keepⁱ s) (keepⁱ l) (keepⁱ r)
keepⁱ (ilit ℓ)      = ulit ℓ
keepⁱ (istep o t)   = keepⁱ t
-- Evaluate the evidence, then the payload. Give the payload (index 0).
keepⁱ (cast e t)    = uletp (upair (keepⁱ e) (keepⁱ t)) (uvar zero)

-- The erasure of proofs: the evidence of a cast is absent.
eraseⁱ : ITm n → UTm n
eraseⁱ (ivar i)      = uvar i
eraseⁱ (ilam q A b)  = ulam (eraseⁱ b)
eraseⁱ (iapp f a)    = uapp (eraseⁱ f) (eraseⁱ a)
eraseⁱ (ipair s t)   = upair (eraseⁱ s) (eraseⁱ t)
eraseⁱ (iletp s b)   = uletp (eraseⁱ s) (eraseⁱ b)
eraseⁱ (iinj₁ t)     = uinl (eraseⁱ t)
eraseⁱ (iinj₂ t)     = uinr (eraseⁱ t)
eraseⁱ (icase s l r) = ucase (eraseⁱ s) (eraseⁱ l) (eraseⁱ r)
eraseⁱ (ilit ℓ)      = ulit ℓ
eraseⁱ (istep o t)   = eraseⁱ t
eraseⁱ (cast e t)    = eraseⁱ t
