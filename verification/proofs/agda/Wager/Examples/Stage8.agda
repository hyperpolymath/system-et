{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- Stage 8 anti-vacuity examples: terms with open types.
--
--   Open-Terms       the signature of Stage 5 (`taggedS rep`, the row
--                    scheme), the one-point grade algebra.
--   Open-Coercions   the same signature. One example is in the algebra
--                    {0, 1, ω}.
--   Role-Of-A-Variable   the signature `classicSig rep` of Stage 2.
--   Identity-Family  the signature of `Wager.Identity.Instance`.
module Wager.Examples.Stage8 where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Sigma using (_×_; _,_; Σ-syntax; fst; snd)
open import Cubical.Data.Sum.Base using (_⊎_; inl; inr)
open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.FinData.Base using (Fin; zero; suc)
open import Cubical.Relation.Nullary using (¬_)

open import Wager.Grade.Algebra
open import Wager.Grade.Trivial
open import Wager.Grade.Affine using (affineOps; affineLaws; a1)
open import Wager.Role.Role
open import Wager.Role.Table
open import Wager.Role.Signature
open import Wager.FC.Tagged
import Wager.FC.Types
import Wager.FC.Coercion
import Wager.Trans.Scheme
import Wager.Trans.Target
import Wager.Trans.Coercion
import Wager.L1.Syntax
import Wager.L1.Normal
import Wager.L1.Eval
import Wager.L1.Conversion
import Wager.L1.Kinding
import Wager.L2.Typing
import Wager.L2.Erasure
import Wager.Role.RepEq
import Wager.Role.Classic
import Wager.Role.ClassicProofs as CP
import Wager.Identity.Instance
import Wager.Identity.Family
import Wager.Poly.Coercion
import Wager.Poly.Typing
open import Wager.Erased.Untyped using (ETy; ebase)
open import Wager.Examples.Stage3 using (module Role-Check)
import Wager.Examples.Stage6Identity as E6
open import Wager.Statements using (module T8-Identity-Statements)
open import Wager.Proofs

private
  SS = taggedS rep
  Sc = Wager.Trans.Scheme.rowScheme SS

------------------------------------------------------------------------
-- T8-Inst, T8-Closed, T8-Closed-Instance, T8-Instance-Progress.

module Open-Terms where
  open Wager.FC.Types SS using (STy; sbase)
  open Wager.Trans.Target SS Sc trivialOps
  import Wager.L2.Typing tSig tTSig trivialOps as C
  open Wager.L2.Erasure tSig tTSig trivialOps using (erT; eraseᵗ; identity-one-type)
  open Wager.Poly.Typing tSig tTSig trivialOps

  -- One type variable of the kind ★.
  O : Ctx
  O = ★ ∷ []

  a : Ty O ★
  a = var vz

  tInt tBool : Ty [] ★
  tInt  = base bInt
  tBool = base bBool

  ∅ᵖ : Cxᵖ O 0
  ∅ᵖ ()

  -- The polymorphic identity function: 1 open term.
  idᵖ : Tmᵖ O 0
  idᵖ = tlam tt a (tvar zero)

  -- ACCEPTED: it has the open type `a → a`.
  idᵖ-typed : 0ᵘ ▸ ∅ᵖ ⊢ᵖ idᵖ ∶ arr tt a a
  idᵖ-typed = t-lam {γ = 0ᵘ} (t-var zero)

  at-int at-bool : TySub [] O
  at-int  = tInt ∷ₛ ids
  at-bool = tBool ∷ₛ ids

  -- Its instance at Int is the identity function of the target at Int.
  id-at-int : ⌊ inst at-int idᵖ ⌋ ≡ C.tlam tt tInt (C.tvar zero)
  id-at-int = refl

  -- ACCEPTED (T8-Closed-Instance): the instance is a typed term of the
  -- target of stages 1 to 5.
  id-at-int-typed :
    0ᵘ C.▸ (λ i → sub at-int (∅ᵖ i)) ⊢ ⌊ inst at-int idᵖ ⌋ ∶ arr tt tInt tInt
  id-at-int-typed = t8-closed-instance tSig tTSig trivialOps at-int idᵖ-typed

  -- ACCEPTED (T8-Instance-Progress): T0 applies to the instance.
  id-at-int-progress :
    C.Value ⌊ inst at-int idᵖ ⌋ ⊎ (Σ[ t' ∈ C.Tm 0 ] (⌊ inst at-int idᵖ ⌋ C.⟶ t'))
  id-at-int-progress = t8-instance-progress tSig tTSig trivialOps at-int idᵖ-typed

  private
    IsBool : ETy BaseName → Type
    IsBool (ebase bBool) = Unit
    IsBool _             = ⊥

  -- REJECTED: the same open term does not have the open type `a → Int`.
  -- If it had, its instance at Bool would be a typed identity function
  -- from Bool to Int (T8-Closed-Instance), and a typed term of the
  -- target that erases to the identity has one erased type on its two
  -- sides (`identity-one-type`, Stage 6).
  id-not-to-int : ∀ {γ} → ¬ (γ ▸ ∅ᵖ ⊢ᵖ idᵖ ∶ arr tt a (⇑ tInt))
  id-not-to-int d =
    subst IsBool
      (identity-one-type
        (t8-closed-instance tSig tTSig trivialOps at-bool d) refl)
      tt

------------------------------------------------------------------------
-- T8-Coercion-Typed, T8-Coercion-Instance, T8-No-Uniform-Unwrap.

module Open-Coercions where
  open Wager.FC.Types SS hiding (inst)
  open Wager.FC.Coercion SS
  open TTypes rep
  open Role-Check using (wr-rep)
  open Wager.Trans.Target SS Sc trivialOps
  open Wager.Trans.Coercion SS Sc trivialOps using (coerceT)
  open Wager.Poly.Coercion SS Sc trivialOps
  open Wager.Poly.Typing tSig tTSig trivialOps using (Cxᵖ; 0ᵘ; _▸_⊢ᵖ_∶_)

  O : Ctx
  O = ★ ∷ []

  ∅ᵖ : Cxᵖ O 0
  ∅ᵖ ()

  -- Two open source types: `a → Age` and `a → Int`.
  θ φ : OTy O
  θ = ovar vz ⇒ᵒ clo sAge
  φ = ovar vz ⇒ᵒ clo sInt

  -- The open coercion between them: the identity at the variable, and
  -- the axiom of the newtype Age at the result.
  c : Coᵒ θ φ
  c = o-arr o-refl (o-clo (c-ax₀ ageE))

  -- ONE POLYMORPHIC COERCION: 1 open term.
  poly : Tmᵖ O 0
  poly = coerceᵒ c

  -- ACCEPTED (T8-Coercion-Typed): it is typed at the open types.
  poly-typed : 0ᵘ ▸ ∅ᵖ ⊢ᵖ poly ∶ arr tt (Tᵒ θ) (Tᵒ φ)
  poly-typed = t8-coercion-typed SS Sc trivialOps trivialLaws wr-rep c ∅ᵖ

  -- Two instantiations of the type variable: Bool, and the newtype Age.
  ρ-bool ρ-age : SInst O
  ρ-bool _ = sBool
  ρ-age  _ = sAge

  s-bool s-age : TySub [] O
  s-bool = T sBool ∷ₛ ids
  s-age  = T sAge ∷ₛ ids

  ag-bool : Agrees s-bool ρ-bool
  ag-bool vz = refl

  ag-age : Agrees s-age ρ-age
  ag-age vz = refl

  -- ACCEPTED (T8-Coercion-Instance): the two instances of the 1 open
  -- term are the two closed coercion functions of Stage 4.
  poly-at-bool :
    ⌊ inst s-bool poly ⌋
      ≡ coerceT {τ = sBool ⇒ˢ sAge} {σ = sBool ⇒ˢ sInt}
                (c-arr (c-sub c-refl) (c-ax₀ ageE))
  poly-at-bool = t8-coercion-instance SS Sc trivialOps c ρ-bool s-bool ag-bool

  poly-at-age :
    ⌊ inst s-age poly ⌋
      ≡ coerceT {τ = sAge ⇒ˢ sAge} {σ = sAge ⇒ˢ sInt}
                (c-arr (c-sub c-refl) (c-ax₀ ageE))
  poly-at-age = t8-coercion-instance SS Sc trivialOps c ρ-age s-age ag-age

  -- ACCEPTED: an open coercion that unwraps a newtype with a parameter
  -- at a CLOSED argument: `a → Tag Int` to `a → Int`.
  tag-closed : Coᵒ {Δ = O} (ovar vz ⇒ᵒ clo (Tag sInt)) (ovar vz ⇒ᵒ clo sInt)
  tag-closed = o-arr o-refl (o-clo (c-ax₁ tagE sInt))

  tag-closed-typed :
    0ᵘ ▸ ∅ᵖ ⊢ᵖ coerceᵒ tag-closed
      ∶ arr tt (Tᵒ (ovar vz ⇒ᵒ clo (Tag sInt))) (Tᵒ (ovar vz ⇒ᵒ clo sInt))
  tag-closed-typed =
    t8-coercion-typed SS Sc trivialOps trivialLaws wr-rep tag-closed ∅ᵖ

  private
    IsInt : STy → Type
    IsInt (sbase bInt) = Unit
    IsInt _            = ⊥

  -- REJECTED (T8-No-Uniform-Unwrap): no open term is the coercion
  -- `Tag a → Int` at the two instances a := Int and a := Bool.
  no-poly-tag :
    ¬ (Σ[ t ∈ Tmᵖ O 0 ]
        (⌊ inst s-age t ⌋ ≡ coerceT (c-ax₁ tagE sInt))
        × (⌊ inst s-bool t ⌋ ≡ coerceT (c-ax₁ tagE sBool)))
  no-poly-tag (t , p , q) =
    subst IsInt
      (t8-no-uniform-unwrap SS Sc trivialOps tagE sInt sBool t s-age s-bool p q) tt

-- ACCEPTED: the polymorphic coercion is typed in the algebra {0, 1, ω}.
-- A coercion uses each variable one time.
module Open-Coercions-In-Affine where
  open Wager.FC.Types SS hiding (inst)
  open Wager.FC.Coercion SS
  open TTypes rep
  open Role-Check using (wr-rep)
  open Wager.Trans.Target SS Sc affineOps
  open Wager.Poly.Coercion SS Sc affineOps
  open Wager.Poly.Typing tSig tTSig affineOps using (Cxᵖ; 0ᵘ; _▸_⊢ᵖ_∶_)

  O : Ctx
  O = ★ ∷ []

  ∅ᵖ : Cxᵖ O 0
  ∅ᵖ ()

  c : Coᵒ {Δ = O} (ovar vz ⇒ᵒ clo sAge) (ovar vz ⇒ᵒ clo sInt)
  c = o-arr o-refl (o-clo (c-ax₀ ageE))

  poly-typed :
    0ᵘ ▸ ∅ᵖ ⊢ᵖ coerceᵒ c
      ∶ arr a1 (Tᵒ (ovar vz ⇒ᵒ clo sAge)) (Tᵒ (ovar vz ⇒ᵒ clo sInt))
  poly-typed = t8-coercion-typed SS Sc affineOps affineLaws wr-rep c ∅ᵖ

------------------------------------------------------------------------
-- T8-Role-Representational, T8-Role-Phantom, T8-Role-Nominal.

module Role-Of-A-Variable where
  open Wager.Role.Classic
  private
    RS = classicSig rep
    S  = toSig RS
  open Wager.L1.Syntax S
  open Wager.L1.Normal S
  open Wager.L1.Eval S
  open Wager.Role.RepEq RS
  open Types rep
  open CP.LawfulKinding rep

  O : Ctx
  O = ★ ∷ []

  -- The open type `a →[1] Proxy a`. The variable has the grade
  -- representational.
  A₁ : Ty O ★
  A₁ = arr a1 (var vz) (Proxy (var vz))

  A₁-kinded : (0ᵏ ▹ᵏ rep) ⊢ᵏ A₁
  A₁-kinded = k-sub (k-arr (k-var vz) (k-capp proxy (k-var vz))) le
    where
    le : (unitᵏ vz ⊕ᵏ (rep ⊙ᵏ unitᵏ vz)) ≼ᵏ (0ᵏ ▹ᵏ rep)
    le k vz = refl

  -- ACCEPTED (T8-Role-Representational): the instances at Age and at
  -- Int are equivalent.
  accepted-representational : nf (A₁ [ Age ]) ≈ nf (A₁ [ Int ])
  accepted-representational =
    t8-role-representational RS CP.ProxyB.valid A₁-kinded refl Age Int
      (CP.Generic.age≈int rep)

  -- The open type `isAge Int`. The variable does not occur, and it has
  -- the grade phantom.
  A₂ : Ty O ★
  A₂ = papp isAge Int

  A₂-kinded : (0ᵏ ▹ᵏ ph) ⊢ᵏ A₂
  A₂-kinded = k-sub (k-papp isAge (k-base bInt)) le
    where
    le : (nom ⊙ᵏ 0ᵏ) ≼ᵏ (0ᵏ ▹ᵏ ph)
    le k vz = refl

  -- ACCEPTED (T8-Role-Phantom): the instances at Age and at Bool have
  -- one normal form.
  accepted-phantom : nf (A₂ [ Age ]) ≡ nf (A₂ [ Bool' ])
  accepted-phantom = t8-role-phantom RS CP.ProxyB.valid A₂-kinded Age Bool'

  -- The body of the classic function: `isAge a`.
  A₃ : Ty O ★
  A₃ = papp isAge (var vz)

  -- REJECTED: kinding does not accept the grade representational for
  -- the variable of `isAge a` (this is T4), and the instances at Age
  -- and at Int are not equivalent.
  rejected : (¬ ((0ᵏ ▹ᵏ rep) ⊢ᵏ A₃))
             × (¬ (nf (A₃ [ Age ]) ≈ nf (A₃ [ Int ])))
  rejected =
      (λ d → t4-kinding-rejects rep refl 0ᵏ (k-lam d))
    , snd t4-not-equivalent rep

  -- ACCEPTED (T8-Role-Nominal): at the grade nominal the two arguments
  -- must have one normal form. `(λb. b) Int` and `Int` have one.
  accepted-nominal : nf (A₃ [ app (lam {g = rep} (var vz)) Int ]) ≡ nf (A₃ [ Int ])
  accepted-nominal =
    t8-role-nominal RS A₃ (app (lam {g = rep} (var vz)) Int) Int refl

------------------------------------------------------------------------
-- T8-Evidence-Rigid, T8-Gadt-Not-Open.

module Identity-Family where
  open E6 using (B₀; int; L₀; tInt; Gⁱ)
  open Wager.Identity.Instance B₀ L₀ (λ _ → int) trivialOps
  open Wager.L1.Syntax sig
  open Wager.L1.Conversion sig using (DefEq)
  open Wager.Identity.Family.IdFamily family using (Id)
  open T8-Identity-Statements B₀ L₀ (λ _ → int) trivialOps int using (Gᵍ)

  -- The data type of the statement is the data type of the example of
  -- Stage 6, part 2.
  same-data : ∀ α → Gᵍ α ≡ Gⁱ α
  same-data α = refl

  -- REJECTED (T8-Evidence-Rigid): no open type with one type variable
  -- has the evidence type `Id α Int` at each instance α.
  no-open-evidence :
    ¬ (Σ[ E ∈ Ty (★ ∷ []) ★ ] (∀ α → DefEq (E [ α ]) (base (Id α tInt))))
  no-open-evidence = t8-evidence-rigid B₀ L₀ (λ _ → int) trivialOps int tInt

  -- REJECTED (T8-Gadt-Not-Open): no open type with one type variable
  -- has the data type of the GADT program at each instance α.
  no-open-data :
    ¬ (Σ[ G ∈ Ty (★ ∷ []) ★ ] (∀ α → DefEq (G [ α ]) (Gⁱ α)))
  no-open-data = t8-gadt-not-open B₀ L₀ (λ _ → int) trivialOps int

  -- ACCEPTED: an open type with THREE type variables has the data type
  -- at each α. The two other variables stand for the two evidence
  -- types, and the instantiation gives them the two base constants.
  -- This open type does not say that its first two variables are
  -- evidence types. The rule `t-cast` needs evidence of a type
  -- `base (Id A B)`, so it does not apply to a term of the type of such
  -- a variable (DESIGN-CHOICES.adoc, DC-8.6).
  G₃ : Ty (★ ∷ ★ ∷ ★ ∷ []) ★
  G₃ = (var vz ⊗ var (vs (vs vz))) ⊕ (var (vs vz) ⊗ var (vs (vs vz)))

  at₃ : Ty [] ★ → TySub [] (★ ∷ ★ ∷ ★ ∷ [])
  at₃ α = base (Id α tInt) ∷ₛ base (Id α (tInt ⊕ tInt)) ∷ₛ α ∷ₛ ids

  three-variables : ∀ α → sub (at₃ α) G₃ ≡ Gⁱ α
  three-variables α = refl
