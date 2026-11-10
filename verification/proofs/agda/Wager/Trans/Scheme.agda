{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- State schemes for the translation of newtypes (Stage 4).
--
-- The translation makes a newtype `N τ` a trope state on the
-- representation of `N τ`. A state scheme says how many states the
-- newtype N needs. The state of `N τ` is the pair of N and an index.
-- The index keeps what a type-level function can see of the argument τ.
--
--   obs F N i   the result of the function F on `N τ`, read from the
--               index i of `N τ`.
--
-- Two schemes are given:
--   rowScheme   the index is the row of the results of all the
--               functions. It exists for each signature.
--   twoState    one index. The newtype is a two-state trope (raw and
--               wrapped), as in Stage 2. It exists when no function
--               looks at the argument of a newtype.
open import Wager.FC.Signature

module Wager.Trans.Scheme (SS : SSig) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Sum.Base using (_⊎_; inl; inr)

open import Wager.FC.Types SS

record StateScheme : Type₁ where
  field
    Idx    : Type
    idx    : N₁ → VTy → Idx
    obs    : Fam → N₁ → Idx → Base
    obs-ok : ∀ F N v → obs F N (idx N v) ≡ applyF F (vnt₁ N v)

rowScheme : StateScheme
rowScheme = record
  { Idx    = Fam → Base
  ; idx    = λ N v F → applyF F (vnt₁ N v)
  ; obs    = λ F N i → i F
  ; obs-ok = λ F N v → refl }

twoState : (c : Fam → N₁ → Base) → (∀ F N → fNt₁ F N ≡ inl (c F N)) → StateScheme
twoState c h = record
  { Idx    = Unit
  ; idx    = λ N v → tt
  ; obs    = λ F N i → c F N
  ; obs-ok = λ F N v → sym (cong (λ x → resB x (λ G → applyF G v)) (h F N)) }
