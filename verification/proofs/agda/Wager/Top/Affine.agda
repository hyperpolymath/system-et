{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- The variant of the translation with a grade q, in the algebra
-- {0, 1, ω} with q = ω: proofs and examples.
--
-- THE CANDIDATE IS FALSE for the whole fragment. The counterexample is
-- the source term `let (x, y) = (5, 5) in 5`. The rule `t-letp` binds
-- each component of a pair at the grade 𝟙, also in the variant. The
-- body drops the two components, and in this algebra 𝟘 ≤ 𝟙 is false.
module Wager.Top.Affine where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.FinData.Base using (Fin; zero; suc)
open import Cubical.Data.Sigma using (_×_; _,_; Σ-syntax; fst)
open import Cubical.Relation.Nullary using (¬_)

open import Wager.Grade.Algebra
open import Wager.Grade.Finite using (false≢true)
open import Wager.Grade.Affine using (Affine; a0; a1; aω; affineOps; affineLaws; affine)
open import Wager.Role.Role using (rep)
open import Wager.FC.Signature
open import Wager.FC.Tagged
import Wager.FC.Types
import Wager.FC.Coercion
import Wager.FC.Term
import Wager.Trans.Scheme
import Wager.Trans.Target
import Wager.Trans.Coercion
import Wager.L2.Typing
import Wager.L2.Inversion
import Wager.Top.Translation
import Wager.Top.Statements
import Wager.Top.Proofs
open import Wager.Top.AffineStatements

private
  SS = taggedS rep
  Sc = Wager.Trans.Scheme.rowScheme SS

open Wager.FC.Types SS
open Wager.FC.Coercion SS
open Wager.FC.Term SS
open TTypes rep
open Wager.Top.Translation SS Sc affineOps aω
open Wager.Top.Statements SS Sc affineOps aω
private module P = Wager.Top.Proofs SS Sc affineOps aω
open Wager.Trans.Target SS Sc opsq using (tSig; tTSig; T; Ty; ★; []; arr)
open Wager.Trans.Coercion SS Sc opsq using (Tm; letp; lit)
open Wager.L2.Typing tSig tTSig affineOps
  using (Usage; Cx; _▸_⊢_∶_; 0ᵘ; _▹_; _▹ᶜ_; t-letp; t-conv; t-sub)
open Wager.L2.Inversion tSig tTSig affine using (inv-lit)
open GradeOps affineOps using (𝟙)

-- The role check of the signature.
wr : SSig.WellRoled SS
wr boxE = refl
wr tagE = refl
wr teeE = refl

omega-is-top : Omega-Is-Top
omega-is-top a0 = refl
omega-is-top a1 = refl
omega-is-top aω = refl

------------------------------------------------------------------------
-- ACCEPTED. The function `λx. 5` drops its argument. The translation
-- of Stage 4 has no type for it in this algebra
-- (`Wager.Examples.Stage4.Coercions-In-Affine.const-rejected`). The
-- variant with q = ω has one.

constFun : STm ∅ˢ (sInt ⇒ˢ sInt)
constFun = slam (slit ℓint)

const-typed : (λ _ → aω) ▸ (λ i → T (∅ˢ i)) ⊢ trq constFun ∶ T (sInt ⇒ˢ sInt)
const-typed = P.top-typing affineLaws wr omega-is-top constFun tt

-- ACCEPTED. A coercion function of the variant: Box Age → Box Int. Its
-- binder has the grade ω.
box-co : Co rep (Box sAge) (Box sInt)
box-co = c-nt₁ boxE (c-ax₀ ageE)

box-typed : ∀ {n} (Γ : Cx n) →
            0ᵘ ▸ Γ ⊢ coerceTq box-co ∶ arr aω (T (Box sAge)) (T (Box sInt))
box-typed Γ = P.top-coerce-typed affineLaws wr refl box-co Γ

------------------------------------------------------------------------
-- REJECTED. A pair elimination that drops a component.

dropPair : STm ∅ˢ sInt
dropPair = sletp (spair (slit ℓint) (slit ℓint)) (slit ℓint)

private
  -- Inversion of the rule `t-letp`: the body has a derivation with the
  -- grade 𝟙 for each of the two components.
  inv-letp : ∀ {n} {γ : Usage n} {Γ : Cx n} {s : Tm n} {b : Tm (suc (suc n))} {C : Ty [] ★} →
             γ ▸ Γ ⊢ letp s b ∶ C →
             Σ[ δ ∈ Usage n ] Σ[ A ∈ Ty [] ★ ] Σ[ B ∈ Ty [] ★ ] Σ[ C' ∈ Ty [] ★ ]
               ((δ ▹ 𝟙 ▹ 𝟙) ▸ (Γ ▹ᶜ A ▹ᶜ B) ⊢ b ∶ C')
  inv-letp (t-letp d e) = _ , _ , _ , _ , e
  inv-letp (t-conv d e) = inv-letp d
  inv-letp (t-sub d le) = inv-letp d

-- The translation of `dropPair` has no type, for each usage vector,
-- each context and each type.
drop-rejected : ∀ {γ : Usage 0} {Γ : Cx 0} {C} → ¬ (γ ▸ Γ ⊢ trq dropPair ∶ C)
drop-rejected d =
  let (δ , A , B , C' , e) = inv-letp d
  in false≢true (fst (inv-lit e) zero)

top-typing-all-fails : Top-Typing-All-Fails
top-typing-all-fails h = drop-rejected (h affineLaws wr omega-is-top dropPair)
