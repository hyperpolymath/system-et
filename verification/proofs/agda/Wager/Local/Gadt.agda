{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- The program of Stage 6: a GADT match (DESIGN-CHOICES.adoc, DC-6.2).
--
-- In Haskell, for a base type b:
--
--   data G a where
--     GI :: (a ~ b)          => a -> G a
--     GB :: (a ~ Either b b) => a -> G a
--
--   eval :: G a -> b
--   eval (GI x) = x
--   eval (GB x) = case x of { Left y -> y ; Right y -> y }
--
-- The source calculus has no type variable. The type variable `a` of
-- the Haskell text is the Agda variable α: `G b α` is the type `G a` at
-- the closed instance a := α, and `gadt-eval b α` is `eval` at that
-- instance. The text of the program is the same at each instance.
open import Cubical.Foundations.Prelude

module Wager.Local.Gadt (B Lit : Type) (litTy : Lit → B) where

open import Cubical.Data.FinData.Base using (zero)

open import Wager.Local.Source B Lit litTy

G : B → LTy → LTy
G b α = ⟨ α ~ lbase b ⟩ α +ˡ ⟨ α ~ lbase b +ˡ lbase b ⟩ α

gadt-eval : ∀ b α → LTm ∅ᵃ ∅ˡ (G b α ⇒ˡ lbase b)
gadt-eval b α =
  llam (lcase (lvar zero)
    -- GI: the assumption is `α ~ b`.
    (lopen (lvar zero) (lcast (l-hyp here) (lvar zero)))
    -- GB: the assumption is `α ~ b + b`.
    (lopen (lvar zero)
      (lcase (lcast (l-hyp here) (lvar zero)) (lvar zero) (lvar zero))))
