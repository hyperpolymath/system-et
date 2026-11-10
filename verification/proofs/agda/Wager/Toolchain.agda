{-# OPTIONS --cubical --safe #-}
-- cubical-0.9 sets --guardedness for all of its modules, and Agda 2.8.0
-- rejects an import of such a module from a module without the flag
-- (InfectiveImport). This file uses no coinduction. See TOOLCHAIN.adoc.
{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- Stage 0 anchor. It shows that the pinned toolchain (Agda 2.8.0 and
-- cubical v0.9) resolves and checks under `--cubical --safe`.
-- It is the module that the gate-failure tests of Stage 0 edit.
-- Stage 1 replaces it with the first real module.
module Wager.Toolchain where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)

-- A path that needs induction: the library and the Path type work.
+-zero-right : (n : ℕ) → n + zero ≡ n
+-zero-right zero    = refl
+-zero-right (suc n) = cong suc (+-zero-right n)

-- Function extensionality is a theorem in Cubical Agda. Later stages
-- use it in logical relations.
+-zero-right-ext : (λ n → n + zero) ≡ (λ n → n)
+-zero-right-ext = funExt +-zero-right
