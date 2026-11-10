{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- The target signature of the translation, and the translation of
-- types (Stage 4).
--
--   source                         target
--   base type b                    base b
--   τ → σ                          arr 𝟙 (T τ) (T σ)
--   pair, sum                      ⊗, ⊕
--   newtype N (no parameter)       capp (state of N) (representation)
--   newtype N τ                    capp (state of N at the index of τ)
--                                       (the translated body of N at τ)
--   type-level function F τ        papp F (T τ)
--
-- A newtype is thus a type in a trope state: `A@s` is `capp s A`, and
-- the carrier A is the representation. Each state has the grade
-- representational, and each primitive has the grade nominal.
--
-- The trope operations are `wrap` and `unwrap`, for each instance of a
-- newtype. No other operation exists, and no rule is added.
open import Cubical.Foundations.Prelude
open import Wager.FC.Signature
open import Wager.Grade.Algebra
import Wager.Trans.Scheme

module Wager.Trans.Target
  (SS : SSig) (Sc : Wager.Trans.Scheme.StateScheme SS)
  {R : Type} (ops : GradeOps R) where

open import Cubical.Data.Bool.Base using (true)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)
open import Cubical.Data.Sum.Base using (_⊎_; inl; inr)

open import Wager.Role.Role
open import Wager.Role.Signature
open import Wager.L1.Signature
open import Wager.Erased.Untyped using (ETy; ebase; earr; eprod; esum)
open import Wager.FC.Types SS
open Wager.Trans.Scheme SS
open StateScheme Sc public
open GradeOps ops using (𝟙)
import Wager.L1.Syntax
import Wager.L2.Signature

-- The states: one for each newtype with no parameter, and one for each
-- newtype with a parameter and each index.
State : Type
State = N₀ ⊎ (N₁ × Idx)

private
  onConT : Fam → State → Base ⊎ Fam
  onConT F (inl N)       = inl (fNt₀ F N)
  onConT F (inr (N , i)) = inl (obs F N i)

tRoleSig : RoleSig
tRoleSig = record
  { TG = R ; Base = Base
  ; Con₁ = State ; cgrade = λ _ → rep ; isNewtype = λ _ → true
  ; Prim = Fam ; pgrade = λ _ → nom
  ; onBase = fBase ; onCon = onConT ; onOther = fOther }

tSig : Sig
tSig = toSig tRoleSig

open Wager.L1.Syntax tSig hiding (Base) public
open Wager.L2.Signature tSig public

------------------------------------------------------------------------
-- The translation of types.

TE : ETy Base → Ty [] ★
TE (ebase b)   = base b
TE (earr a b)  = arr 𝟙 (TE a) (TE b)
TE (eprod a b) = TE a ⊗ TE b
TE (esum a b)  = TE a ⊕ TE b

-- The body of a newtype, at a type for the parameter. The context is
-- general: with a type variable for the parameter, the body is a
-- type-level function of the target.
TB : ∀ {Γ} → Body Base Fam → Ty Γ ★ → Ty Γ ★
TB bvar        A = A
TB (bbase b)   A = base b
TB (barr β γ)  A = arr 𝟙 (TB β A) (TB γ A)
TB (bprod β γ) A = TB β A ⊗ TB γ A
TB (bsum β γ)  A = TB β A ⊕ TB γ A
TB (bfam F β)  A = papp F (TB β A)

T : STy → Ty [] ★
T (sbase b)  = base b
T (τ ⇒ˢ σ)   = arr 𝟙 (T τ) (T σ)
T (τ ×ˢ σ)   = T τ ⊗ T σ
T (τ +ˢ σ)   = T τ ⊕ T σ
T (nt₀ N)    = capp (inl N) (TE (rep₀ N))
T (nt₁ N τ)  = capp (inr (N , idx N (ev τ))) (TB (body N) (T τ))
T (fam F τ)  = papp F (T τ)

-- The body of the newtype N as a type-level function of the target,
-- with the grade g for its parameter.
bodyFun : N₁ → (g : Role) → Ty [] (★ ⇒[ g ] ★)
bodyFun N g = lam (TB (body N) (var vz))

------------------------------------------------------------------------
-- The trope operations.

data Dir : Type where
  wrap unwrap : Dir

-- An instance of a newtype.
Inst : Type
Inst = N₀ ⊎ (N₁ × STy)

stateOf : Inst → State
stateOf (inl N)       = inl N
stateOf (inr (N , τ)) = inr (N , idx N (ev τ))

carrierOf : Inst → Ty [] ★
carrierOf (inl N)       = TE (rep₀ N)
carrierOf (inr (N , τ)) = TB (body N) (T τ)

private
  fromOp toOp : Dir × Inst → Maybe State
  fromOp (wrap   , x) = nothing
  fromOp (unwrap , x) = just (stateOf x)
  toOp   (wrap   , x) = just (stateOf x)
  toOp   (unwrap , x) = nothing

-- wrap:   carrier         → carrier @ state
-- unwrap: carrier @ state → carrier
tTSig : TSig
tTSig = record
  { Lit = Lit ; litTy = litTy
  ; Op = Dir × Inst ; carrier = λ o → carrierOf (snd o)
  ; from = fromOp ; to = toOp }
