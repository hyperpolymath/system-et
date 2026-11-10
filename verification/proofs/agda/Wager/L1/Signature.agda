{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- The signature of the L1 type language.
--
-- The systemet documents give base constants only. The signature is a
-- design choice of this experiment (DESIGN-CHOICES.adoc, DC-1.1).
-- A later stage adds entries to a signature. It does not add
-- constructors to the language.
module Wager.L1.Signature where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sum.Base using (_⊎_)

record Sig : Type₁ where
  field
    -- Carriers of the grades. KG grades kind arrows. TG grades the
    -- object arrow (and term binders). No law is needed at L1.
    KG TG : Type

    -- Base type constants, of kind ★.
    Base : Type

    -- Generative unary type constants. `capp c A` has kind ★ when A has
    -- kind ★. The parameter of `c` has the grade `cgrade c`.
    -- A trope state is such a constant: `A@s` is `capp s A`.
    Con₁   : Type
    cgrade : Con₁ → KG

    -- Total inspection primitives. `papp p A` has kind ★ when A has
    -- kind ★. The parameter of `p` has the grade `pgrade p`.
    -- A primitive looks at the head of its argument:
    --   a base constant b        gives the base constant `onBase p b`
    --   `capp c A`               gives `onCon p c`: a base constant, or
    --                            the primitive that then inspects A
    --   an arrow, product or sum gives the base constant `onOther p`
    Prim    : Type
    pgrade  : Prim → KG
    onBase  : Prim → Base → Base
    onCon   : Prim → Con₁ → Base ⊎ Prim
    onOther : Prim → Base
