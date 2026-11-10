{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- DESIGN-CHOICES.adoc, DC-0.3: matches on typing derivations and values.
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- Stage 4 anti-vacuity examples. Each theorem of Stage 4 has one closed
-- example that satisfies the hypotheses, and one closed example that is
-- rejected.
--
-- The source signature is `taggedS rep` of Wager.FC.Tagged (Age, Box,
-- the phantom newtype Tag, the nominal newtype T, the functions F and
-- G). The state scheme is the row scheme.
module Wager.Examples.Stage4 where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool.Base using (true; false)
open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.FinData.Base using (Fin; zero; suc)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd; Σ-syntax)
open import Cubical.Data.Sum.Base using (_⊎_; inl; inr)
open import Cubical.Relation.Nullary using (¬_)

open import Wager.Grade.Algebra
open import Wager.Grade.Finite using (false≢true)
open import Wager.Grade.Affine
open import Wager.Grade.Trivial
open import Wager.Role.Role
open import Wager.Role.Table
open import Wager.FC.Signature
open import Wager.FC.Tagged
open import Wager.FC.Classic using (classicS)
open import Wager.Erased.Untyped
import Wager.FC.Types
import Wager.FC.Coercion
import Wager.FC.Term
import Wager.Trans.Scheme
import Wager.Trans.Target
import Wager.Trans.Coercion
import Wager.Trans.TwoState
import Wager.Erased.LogRel
import Wager.L1.Conversion
import Wager.L1.Normal
import Wager.L1.Eval
import Wager.L1.Equality
import Wager.L1.Kinding
import Wager.L2.Typing
import Wager.L2.Inversion
import Wager.L2.Preservation
open import Wager.Examples.Stage3 using (module Role-Check; module Role-Soundness-Examples; module Term-Examples)
open import Wager.Proofs

private
  SS = taggedS rep
  Sc = Wager.Trans.Scheme.rowScheme SS

open Wager.FC.Types SS
open Wager.FC.Coercion SS
open Wager.FC.Term SS
open TTypes rep
open Role-Check using (wr-rep)
open Role-Soundness-Examples using (box-co; tag-co)
open Term-Examples using (prog)
open Wager.Erased.LogRel litTy

------------------------------------------------------------------------
-- Coercions are terms of the target, in the affine algebra.

module Coercions-In-Affine where
  open Wager.Trans.Target SS Sc affineOps using (tSig; tTSig; T; arr; ★; [])
  open Wager.Trans.Coercion SS Sc affineOps using (coerceT; tr; tlam; lit; Tm)
  open Wager.L1.Conversion tSig
  open Wager.L1.Normal tSig using (Nf; nbase)
  open Wager.L1.Eval tSig using (nf)
  open Wager.L1.Equality tSig using (defEq→nf)
  open Wager.L2.Typing tSig tTSig affineOps using (Cx; Usage; _▸_⊢_∶_; 0ᵘ; _≤ᵘ_)
  open Wager.L2.Inversion tSig tTSig affine using (inv-lit)
  open Wager.L2.Preservation tSig tTSig affine using (inv-lam)
  open GradeOps affineOps using (_≤_; 𝟘; 𝟙)

  private
    ∅ : Cx 0
    ∅ ()

  -- Accepted (Coercion-Is-A-Term): Box Age → Box Int is a typed
  -- function of the target. Its parameter has the grade 1 (linear).
  box-typed : 0ᵘ ▸ ∅ ⊢ coerceT box-co ∶ arr a1 (T (Box sAge)) (T (Box sInt))
  box-typed = coercion-is-a-term SS Sc affine wr-rep box-co ∅

  -- Accepted: the phantom coercion Tag Int → Tag Bool is a typed
  -- function of the target (two trope transitions).
  tag-typed : 0ᵘ ▸ ∅ ⊢ coerceT tag-co ∶ arr a1 (T (Tag sInt)) (T (Tag sBool))
  tag-typed = coercion-is-a-term SS Sc affine wr-rep tag-co ∅

  -- The two target types are two different states of the carrier Int:
  -- they are NOT convertible. The function F tells them apart.
  private
    IsBoolNf : Nf [] ★ → Type
    IsBoolNf (nbase bBool) = Unit
    IsBoolNf _             = ⊥

  tag-states-differ : ¬ DefEq (T (Tag sInt)) (T (Tag sBool))
  tag-states-differ e = subst IsBoolNf (defEq→nf (d-papp {p = fE} e)) tt

  -- Rejected (T5-Typing needs an unrestricted grade 1): in the affine
  -- algebra the grade 1 is linear. The hypothesis 0 ≤ 1 is false, and
  -- the translation of a function that drops its argument has no type.
  affine-not-unrestricted : ¬ (𝟘 ≤ 𝟙)
  affine-not-unrestricted p = false≢true p

  constFun : STm ∅ˢ (sInt ⇒ˢ sInt)
  constFun = slam (slit ℓint)

  const-rejected : ∀ {γ : Usage 0} {Γ : Cx 0} {C} → ¬ (γ ▸ Γ ⊢ tr constFun ∶ C)
  const-rejected d =
    let (B , γ' , c , le , d') = inv-lam d
    in false≢true (fst (inv-lit d') zero)

------------------------------------------------------------------------
-- Whole programs, in the one-point algebra (no usage discipline).

module Programs where
  open Wager.Trans.Target SS Sc trivialOps using (tSig; tTSig; T)
  open Wager.Trans.Coercion SS Sc trivialOps using (coerceT; tr; eraseT)
  open Wager.L2.Typing tSig tTSig trivialOps using (_▸_⊢_∶_)

  -- prog = coerce (MkBox (MkAge 5, 7)) : Box Int   (Wager.Examples.Stage3)

  -- Accepted (T5-Typing): the translated program has the translated type.
  prog-typed : (λ _ → tt) ▸ (λ i → T (∅ˢ i)) ⊢ tr prog ∶ T (Box sInt)
  prog-typed = t5-typing SS Sc trivial wr-rep tt tt prog

  -- The erased translation. The trope transitions vanished. The map of
  -- the pair stays: the erased coercion is `λp. let (x, y) = p in (x, y)`.
  prog-erased :
    eraseT (tr prog)
      ≡ uapp (ulam (uletp (uvar zero) (upair (uvar (suc zero)) (uvar zero))))
             (upair (ulit ℓint) (ulit ℓint))
  prog-erased = refl

  -- Accepted (T5-Behaviour): the erased source program and the erased
  -- translation evaluate to one value, the pair of the two literals.
  source-value : ∅ᵉ ⊢ eraseTm prog ⇓ vpair (vlit ℓint) (vlit ℓint)
  source-value = ⇓-app ⇓-lam (⇓-pair ⇓-lit ⇓-lit) (⇓-var zero)

  target-value : ∅ᵉ ⊢ eraseT (tr prog) ⇓ vpair (vlit ℓint) (vlit ℓint)
  target-value =
    ⇓-app ⇓-lam (⇓-pair ⇓-lit ⇓-lit)
          (⇓-letp (⇓-var zero) (⇓-pair (⇓-var (suc zero)) (⇓-var zero)))

  -- The instance of the theorem for this program.
  prog-same-value :
    Σ[ v ∈ UVal ] (∅ᵉ ⊢ eraseTm prog ⇓ v) × (∅ᵉ ⊢ eraseT (tr prog) ⇓ v)
  prog-same-value =
    t5-behaviour-first-order SS Sc trivial wr-rep prog (fo-prod fo-base fo-base)

  -- Accepted (T3): the erased coercion Box Age → Box Int is
  -- observationally equal to the identity function.
  box-identity :
    Σ[ f ∈ UVal ] (∅ᵉ ⊢ eraseT (coerceT box-co) ⇓ f)
                × 𝒱 (earr (er (Box sAge)) (er (Box sAge))) (vclo ∅ᵉ (uvar zero)) f
  box-identity = t3 SS Sc trivial wr-rep box-co

------------------------------------------------------------------------
-- Rejected (T3): the relation `𝒱` is not trivial. The function that
-- swaps the two sides of a sum is NOT observationally equal to the
-- identity function.

module Not-The-Identity where
  private
    eInt : ETy BaseName
    eInt = ebase bInt

    swapBody : UTm 1
    swapBody = ucase (uvar zero) (uinr (uvar zero)) (uinl (uvar zero))

    five : UVal
    five = vinl (vlit ℓint)

  swap-not-identity :
    ¬ 𝒱 (earr (esum eInt eInt) (esum eInt eInt)) (vclo ∅ᵉ (uvar zero)) (vclo ∅ᵉ swapBody)
  swap-not-identity (r-clo h) with h five five (r-inl (r-lit ℓint refl))
  ... | _ , _ , ⇓-var zero , ⇓-casel (⇓-var zero) (⇓-inr (⇓-var zero)) , ()

------------------------------------------------------------------------
-- Role correspondence, in the lawful role table.

module Role-Examples where
  open Wager.Trans.Target SS Sc trivialOps using (tSig; bodyFun; [])
  open Wager.L1.Kinding tSig (tableOps tableZ)

  -- Accepted: kinding accepts the grade representational for the body
  -- of Box, and the grade phantom for the body of Tag.
  box-rep : Σ[ γ ∈ KUsage [] ] (γ ⊢ᵏ bodyFun boxE rep)
  box-rep = fst (role-correspondence SS Sc trivial boxE rep) refl

  tag-ph : Σ[ γ ∈ KUsage [] ] (γ ⊢ᵏ bodyFun tagE ph)
  tag-ph = fst (role-correspondence SS Sc trivial tagE ph) refl

  -- Rejected: kinding rejects the grade representational for the body
  -- of T (the parameter is below a type-level function), and the grade
  -- phantom for the body of Box.
  tee-rep-rejected : (γ : KUsage []) → ¬ (γ ⊢ᵏ bodyFun teeE rep)
  tee-rep-rejected γ d = false≢true (snd (role-correspondence SS Sc trivial teeE rep) γ d)

  box-ph-rejected : (γ : KUsage []) → ¬ (γ ⊢ᵏ bodyFun boxE ph)
  box-ph-rejected γ d = false≢true (snd (role-correspondence SS Sc trivial boxE ph) γ d)

------------------------------------------------------------------------
-- Two-state tropes.

module Two-State-Examples where

  -- Accepted: the classic signature of Stage 3 (Age, T, F) has a
  -- two-state translation. No function looks at the argument of T.
  classic-two-state :
    Σ[ t ∈ Wager.Trans.TwoState.Translation (classicS nom) _ ]
      Wager.Trans.TwoState.TwoState (classicS nom) _ t
  classic-two-state =
    two-state-translation-exists (classicS nom) trivialOps (λ _ _ → bUnit) (λ F N → refl)

  -- Rejected: the tagged signature has no two-state translation
  -- (`Wager.Proofs.no-two-state-translation`). It has the translation
  -- with the row scheme.
  tagged-row : Wager.Trans.TwoState.Translation SS _
  tagged-row = row-translation-exists SS trivialOps
