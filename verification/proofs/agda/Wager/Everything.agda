{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- Imports every module of the Wager development.
module Wager.Everything where

import Wager.Grade.Algebra
import Wager.Grade.Finite
import Wager.Grade.Affine
import Wager.Grade.Level
import Wager.L1.Signature
import Wager.L1.Syntax
import Wager.L1.SyntaxLemmas
import Wager.L1.Conversion
import Wager.L1.Normal
import Wager.L1.Eval
import Wager.L1.Completeness
import Wager.L1.Soundness
import Wager.L1.Equality
import Wager.L1.Heads
import Wager.L1.Kinding
import Wager.L2.Signature
import Wager.L2.Usage
import Wager.L2.Term
import Wager.L2.Typing
import Wager.Statements
import Wager.L2.UsageLaws
import Wager.L2.Renaming
import Wager.L2.Substitution
import Wager.L2.Inversion
import Wager.L2.Preservation
import Wager.L2.Progress
import Wager.Proofs
import Wager.Examples.Stage1
import Wager.Role.Role
import Wager.Role.Role4
import Wager.Role.Table
import Wager.Role.Signature
import Wager.Role.RepEq
import Wager.Role.Validity
import Wager.Role.Classic
import Wager.L1.KindingInversion
import Wager.Role.Noninterference
import Wager.Role.Lawful
import Wager.Role.ClassicProofs
import Wager.Examples.Stage2
import Wager.Erased.Untyped
import Wager.FC.Signature
import Wager.FC.Types
import Wager.FC.Coercion
import Wager.FC.Term
import Wager.FC.Classic
import Wager.FC.RoleSoundness
import Wager.FC.Erasure
import Wager.FC.ClassicProofs
import Wager.Examples.Stage3
