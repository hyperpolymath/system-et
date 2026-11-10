{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- DESIGN-CHOICES.adoc, DC-0.3: matches on coercions and on realisers.
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- Stage 7 (the optional univalent cross-check): the proof.
--
-- The translation of a representational coercion denotes transport
-- along its path (`Wager.Univalent.Model.pathOf`).
--
-- The proof has the shape of the typing proof of Stage 4
-- (`Wager.Trans.Typing.coI-typed`): one lemma for each building block
-- of a transformer, then a recursion on the coercion.
--
--   a trope transition   the realiser does not change. The element
--                        changes by `unbox` or `box`, and this is
--                        transport along `ua unboxEquiv` (`uaβ`, `~uaβ`).
--   a function, a pair,  transport along the congruence of the type
--   a sum                former computes to the map of the parts.
--   composition          `transportComposite`.
--   a nominal coercion   the two types have one normal form.
open import Cubical.Foundations.Prelude
open import Wager.FC.Signature
open import Wager.Grade.Algebra
import Wager.Trans.Scheme
module Wager.Univalent.CrossCheck
  (SS : SSig) (Sc : Wager.Trans.Scheme.StateScheme SS)
  {R : Type} (A : GradeAlgebra R)
  (El : SSig.Base SS → Type)
  (elLit : (ℓ : SSig.Lit SS) → El (SSig.litTy SS ℓ)) where

open import Cubical.Foundations.Transport using (transportComposite)
open import Cubical.Foundations.GroupoidLaws using (symDistr)
open import Cubical.Foundations.Univalence using (ua; uaβ; ~uaβ)
open import Cubical.Data.Bool.Base using (true; false)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.FinData.Base using (Fin; zero; suc)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd; Σ-syntax)
open import Cubical.Data.Sum.Base using (_⊎_; inl; inr)

open import Wager.Grade.Finite using (false≢true)
open import Wager.Role.Role
open import Wager.FC.Types SS
open import Wager.FC.Coercion SS
open import Wager.Trans.Target SS Sc (GradeAlgebra.ops A)
open import Wager.Trans.Nominal SS Sc (GradeAlgebra.ops A) using (nominal-defeq; T-inst; T-embE)
open import Wager.Trans.Coercion SS Sc (GradeAlgebra.ops A)
open import Wager.Trans.Typing SS Sc A using (body-defeq)
open import Wager.L1.Normal tSig
open import Wager.L1.Eval tSig using (nf)
open import Wager.L1.Conversion tSig
open import Wager.L1.Equality tSig using (defEq→nf)
open import Wager.Erased.Untyped
open Terms Lit
open import Wager.Univalent.Model SS Sc A El elLit
open GradeOps (GradeAlgebra.ops A) using (𝟙)

private
  variable
    X Y Z X' Y' : Ty [] ★
    τ σ : STy

-- A pair of transformers denotes transport along a path and along its
-- inverse.
IsoDen : (X Y : Ty [] ★) → ⟦ X ⟧ ≡ ⟦ Y ⟧ → Iso → Type
IsoDen X Y p i =
  Denotes X Y (fwd i) (transport p) × Denotes Y X (bwd i) (transport (sym p))

------------------------------------------------------------------------
-- Each building block.

-- A realiser stays a realiser along a path of normal forms.
𝓡-nf : ∀ {u w : Nf [] ★} (e : u ≡ w) {v : UVal} {x : ⟦ u ⟧ⁿ} →
       𝓡 u v x → 𝓡 w v (transport (cong ⟦_⟧ⁿ e) x)
𝓡-nf e {v} {x} r =
  transport (λ i → 𝓡 (e i) v (transport-filler (cong ⟦_⟧ⁿ e) x i)) r

-- The identity transformer, between two convertible types.
id-den : (e : DefEq X Y) → IsoDen X Y (nomPath e) idIso
id-den e =
    (λ t x (v , d , r) → v , d , 𝓡-nf (defEq→nf e) r)
  , (λ t y (v , d , r) → v , d , 𝓡-nf (sym (defEq→nf e)) r)

-- The identity transformer, along the constant path.
refl-den : IsoDen X X refl idIso
refl-den {X = X} =
    (λ t x (v , d , r) → v , d , subst (𝓡 (nf X) v) (sym (transportRefl x)) r)
  , (λ t x (v , d , r) → v , d , subst (𝓡 (nf X) v) (sym (transportRefl x)) r)

swap-den : ∀ {p i} → IsoDen X Y p i → IsoDen Y X (sym p) (swapIso i)
swap-den (f , g) = g , f

comp-den : ∀ {p q i j} → IsoDen X Y p i → IsoDen Y Z q j →
           IsoDen X Z (p ∙ q) (compIso i j)
comp-den {X = X} {Z = Z} {p = p} {q = q} {i = i} {j = j} (f , g) (f' , g') =
    (λ t x h →
       let (w , d , r) = f' (fwd i t) (transport p x) (f t x h)
       in w , d , subst (𝓡 (nf Z) w) (sym (transportComposite p q x)) r)
  , (λ t z h →
       let (w , d , r) = g (bwd j t) (transport (sym q) z) (g' t z h)
       in w , d , subst (𝓡 (nf X) w)
                        (sym (cong (λ s → transport s z) (symDistr p q)
                              ∙ transportComposite (sym q) (sym p) z)) r)

-- THE TROPE TRANSITIONS of a newtype instance: the path from `ua`.
step-den : (x : Inst) →
           IsoDen (capp (stateOf x) (carrierOf x)) (carrierOf x) (ua unboxEquiv) (stepIso x)
step-den x =
    (λ t b (v , d , r) →
       v , d , subst (𝓡 (nf (carrierOf x)) v) (sym (uaβ unboxEquiv b)) r)
  , (λ t y (v , d , r) →
       v , d , subst (𝓡 (nf (carrierOf x)) v) (sym (cong unbox (~uaβ unboxEquiv y))) r)

-- The map of a function.
arrMap-den : ∀ {h g : Tr} (p : ⟦ X ⟧ ≡ ⟦ X' ⟧) (q : ⟦ Y ⟧ ≡ ⟦ Y' ⟧) →
             Denotes X' X h (transport (sym p)) → Denotes Y Y' g (transport q) →
             Denotes (arr 𝟙 X Y) (arr 𝟙 X' Y') (arrMap (arr 𝟙 X Y) X' h g)
                     (transport (cong₂ (λ P Q → P → Q) p q))
arrMap-den {h = h} p q ch cg t f (_ , dt , r-fun hf) =
    _ , ⇓-app ⇓-lam dt ⇓-lam
  , r-fun (λ w y ry →
      let (w' , dw' , rw') = ch (tvar zero) y (w , ⇓-var zero , ry)
          (r , dr , rr)    = hf w' (transport (sym p) y) rw'
      in cg (tapp (tvar (suc zero)) (h (tvar zero))) (f (transport (sym p) y))
            (r , ⇓-app (⇓-var (suc zero)) dw' dr , rr))

arrIso-den : ∀ {i j} (p : ⟦ X ⟧ ≡ ⟦ X' ⟧) (q : ⟦ Y ⟧ ≡ ⟦ Y' ⟧) →
             IsoDen X X' p i → IsoDen Y Y' q j →
             IsoDen (arr 𝟙 X Y) (arr 𝟙 X' Y') (cong₂ (λ P Q → P → Q) p q)
                    (arrIso X X' Y Y' i j)
arrIso-den {X = X} {X' = X'} {Y = Y} {Y' = Y'} {i = i} {j = j} p q (f , g) (f' , g') =
    arrMap-den {X = X} {X' = X'} {Y = Y} {Y' = Y'} {h = bwd i} {g = fwd j} p q g f'
  , arrMap-den {X = X'} {X' = X} {Y = Y'} {Y' = Y} {h = fwd i} {g = bwd j} (sym p) (sym q) f g'

-- The map of a pair.
prodMap-den : ∀ {f g : Tr} (p : ⟦ X ⟧ ≡ ⟦ X' ⟧) (q : ⟦ Y ⟧ ≡ ⟦ Y' ⟧) →
              Denotes X X' f (transport p) → Denotes Y Y' g (transport q) →
              Denotes (X ⊗ Y) (X' ⊗ Y') (prodMap f g) (transport (cong₂ _×_ p q))
prodMap-den p q cf cg t _ (_ , dt , r-pair {v = v₁} {w = v₂} {x = x} {y = y} r₁ r₂) =
  let (w₁ , d₁ , s₁) = cf (tvar (suc zero)) x (v₁ , ⇓-var (suc zero) , r₁)
      (w₂ , d₂ , s₂) = cg (tvar zero) y (v₂ , ⇓-var zero , r₂)
  in vpair w₁ w₂ , ⇓-letp dt (⇓-pair d₁ d₂) , r-pair s₁ s₂

prodIso-den : ∀ {i j} (p : ⟦ X ⟧ ≡ ⟦ X' ⟧) (q : ⟦ Y ⟧ ≡ ⟦ Y' ⟧) →
              IsoDen X X' p i → IsoDen Y Y' q j →
              IsoDen (X ⊗ Y) (X' ⊗ Y') (cong₂ _×_ p q) (prodIso i j)
prodIso-den {X = X} {X' = X'} {Y = Y} {Y' = Y'} {i = i} {j = j} p q (f , g) (f' , g') =
    prodMap-den {X = X} {X' = X'} {Y = Y} {Y' = Y'} {f = fwd i} {g = fwd j} p q f f'
  , prodMap-den {X = X'} {X' = X} {Y = Y'} {Y' = Y} {f = bwd i} {g = bwd j} (sym p) (sym q) g g'

-- The map of a sum.
sumMap-den : ∀ {f g : Tr} (p : ⟦ X ⟧ ≡ ⟦ X' ⟧) (q : ⟦ Y ⟧ ≡ ⟦ Y' ⟧) →
             Denotes X X' f (transport p) → Denotes Y Y' g (transport q) →
             Denotes (X ⊕ Y) (X' ⊕ Y') (sumMap f g) (transport (cong₂ _⊎_ p q))
sumMap-den p q cf cg t _ (_ , dt , r-inl {v = v} {x = x} r) =
  let (w , d , s) = cf (tvar zero) x (v , ⇓-var zero , r)
  in vinl w , ⇓-casel dt (⇓-inl d) , r-inl s
sumMap-den p q cf cg t _ (_ , dt , r-inr {v = v} {y = y} r) =
  let (w , d , s) = cg (tvar zero) y (v , ⇓-var zero , r)
  in vinr w , ⇓-caser dt (⇓-inr d) , r-inr s

sumIso-den : ∀ {i j} (p : ⟦ X ⟧ ≡ ⟦ X' ⟧) (q : ⟦ Y ⟧ ≡ ⟦ Y' ⟧) →
             IsoDen X X' p i → IsoDen Y Y' q j →
             IsoDen (X ⊕ Y) (X' ⊕ Y') (cong₂ _⊎_ p q) (sumIso i j)
sumIso-den {X = X} {X' = X'} {Y = Y} {Y' = Y'} {i = i} {j = j} p q (f , g) (f' , g') =
    sumMap-den {X = X} {X' = X'} {Y = Y} {Y' = Y'} {f = fwd i} {g = fwd j} p q f f'
  , sumMap-den {X = X'} {X' = X} {Y = Y'} {Y' = Y} {f = bwd i} {g = bwd j} (sym p) (sym q) g g'

------------------------------------------------------------------------
-- The map of a body, for a parameter that is used at the role d.

module _ {d : Role} (hn : leR nom d ≡ true → DefEq X Y)
         (hv : leR rep d ≡ true → ⟦ X ⟧ ≡ ⟦ Y ⟧) {i : Iso}
         (hd : (le : leR rep d ≡ true) → IsoDen X Y (hv le) i) where

  body-den : ∀ β (le : leR (roleOf β) d ≡ true) →
             IsoDen (TB β X) (TB β Y) (bodyPath hn hv β le) (bodyIso β X Y i)
  body-den bvar        le = hd le
  body-den (bbase b)   le = refl-den {X = base b}
  body-den (barr β γ)  le =
    arrIso-den {X = TB β X} {X' = TB β Y} {Y = TB γ X} {Y' = TB γ Y}
               {i = bodyIso β X Y i} {j = bodyIso γ X Y i}
               (bodyPath hn hv β le₁) (bodyPath hn hv γ le₂)
               (body-den β le₁) (body-den γ le₂)
    where
    le₁ = leR-trans _ _ _ (max-upper-l (roleOf β) (roleOf γ)) le
    le₂ = leR-trans _ _ _ (max-upper-r (roleOf β) (roleOf γ)) le
  body-den (bprod β γ) le =
    prodIso-den {X = TB β X} {X' = TB β Y} {Y = TB γ X} {Y' = TB γ Y}
                {i = bodyIso β X Y i} {j = bodyIso γ X Y i}
                (bodyPath hn hv β le₁) (bodyPath hn hv γ le₂)
                (body-den β le₁) (body-den γ le₂)
    where
    le₁ = leR-trans _ _ _ (max-upper-l (roleOf β) (roleOf γ)) le
    le₂ = leR-trans _ _ _ (max-upper-r (roleOf β) (roleOf γ)) le
  body-den (bsum β γ)  le =
    sumIso-den {X = TB β X} {X' = TB β Y} {Y = TB γ X} {Y' = TB γ Y}
               {i = bodyIso β X Y i} {j = bodyIso γ X Y i}
               (bodyPath hn hv β le₁) (bodyPath hn hv γ le₂)
               (body-den β le₁) (body-den γ le₂)
    where
    le₁ = leR-trans _ _ _ (max-upper-l (roleOf β) (roleOf γ)) le
    le₂ = leR-trans _ _ _ (max-upper-r (roleOf β) (roleOf γ)) le
  body-den (bfam F β)  le = id-den (d-papp (body-defeq hn β le))

------------------------------------------------------------------------
-- The translation of a coercion.

-- What the translation of a coercion at the role r denotes.
DenAt : ∀ r → Co r τ σ → PathAt r τ σ → Type
DenAt {τ = τ} {σ = σ} rep γ p = IsoDen (T τ) (T σ) p (coI rep γ)
DenAt nom γ p = Unit
DenAt ph  γ p = Unit

private
  -- A transformer below the wrapper of a newtype: unwrap, map, wrap.
  nt-wrap : ∀ N {τ σ i} (pb : ⟦ TB (body N) (T τ) ⟧ ≡ ⟦ TB (body N) (T σ) ⟧) →
            IsoDen (TB (body N) (T τ)) (TB (body N) (T σ)) pb
                   (bodyIso (body N) (T τ) (T σ) i) →
            IsoDen (T (nt₁ N τ)) (T (nt₁ N σ)) (cong Box pb) (ntIso N τ σ i)
  nt-wrap N {τ} {σ} pb (f , g) =
      (λ t x h → f (step (unwrap , inr (N , τ)) t) (unbox x) h)
    , (λ t y h → g (step (unwrap , inr (N , σ)) t) (unbox y) h)

  nt-den : ∀ N d (le : leR (roleOf (body N)) d ≡ true)
           (γ : Co d τ σ) (pa : PathAt d τ σ) → DenAt d γ pa →
           IsoDen (T (nt₁ N τ)) (T (nt₁ N σ)) (ntPath N d le γ pa) (ntIso N τ σ (coI d γ))
  nt-den N rep le γ p den =
    nt-wrap N (bodyPath (λ q → ⊥.rec (false≢true q)) (λ _ → p) (body N) le)
      (body-den (λ q → ⊥.rec (false≢true q)) (λ _ → p)
                {i = coI rep γ} (λ _ → den) (body N) le)
  nt-den N nom le γ _ den =
    nt-wrap N (bodyPath (λ _ → nominal-defeq γ) (λ _ → nomPath (nominal-defeq γ)) (body N) le)
      (body-den (λ _ → nominal-defeq γ) (λ _ → nomPath (nominal-defeq γ))
                {i = idIso} (λ _ → id-den (nominal-defeq γ)) (body N) le)
  nt-den N ph  le γ _ den =
    nt-wrap N (bodyPath (λ q → ⊥.rec (false≢true q)) (λ q → ⊥.rec (false≢true q)) (body N) le)
      (body-den (λ q → ⊥.rec (false≢true q)) (λ q → ⊥.rec (false≢true q))
                {i = idIso} (λ q → ⊥.rec (false≢true q)) (body N) le)

  -- A newtype axiom, along the equation of the type translation.
  ax-den : ∀ {C i} (e : C ≡ Z) (p : ⟦ X ⟧ ≡ ⟦ C ⟧) → IsoDen X C p i →
           IsoDen X Z (subst (λ W → ⟦ X ⟧ ≡ ⟦ W ⟧) e p) i
  ax-den {X = X} {i = i} e p h =
    transport (λ k → IsoDen X (e k) (subst-filler (λ W → ⟦ X ⟧ ≡ ⟦ W ⟧) e p k) i) h

coI-den : (wr : WellRoled) → ∀ r (γ : Co r τ σ) → DenAt r γ (pathAt wr r γ)
coI-den wr nom γ = tt
coI-den wr ph  γ = tt
coI-den wr rep (c-sym {τ = τ} {σ = σ} γ) =
  swap-den {X = T τ} {Y = T σ} {p = pathAt wr rep γ} {i = coI rep γ} (coI-den wr rep γ)
coI-den wr rep (c-trans {τ = τ} {σ = σ} {υ = υ} γ δ) =
  comp-den {X = T τ} {Y = T σ} {Z = T υ} {p = pathAt wr rep γ} {q = pathAt wr rep δ}
           {i = coI rep γ} {j = coI rep δ} (coI-den wr rep γ) (coI-den wr rep δ)
coI-den wr rep (c-sub γ)     = id-den (nominal-defeq γ)
coI-den wr rep (c-arr {τ = τ} {τ' = τ'} {σ = σ} {σ' = σ'} γ δ) =
  arrIso-den {X = T τ} {X' = T τ'} {Y = T σ} {Y' = T σ'} {i = coI rep γ} {j = coI rep δ}
             (pathAt wr rep γ) (pathAt wr rep δ) (coI-den wr rep γ) (coI-den wr rep δ)
coI-den wr rep (c-prod {τ = τ} {τ' = τ'} {σ = σ} {σ' = σ'} γ δ) =
  prodIso-den {X = T τ} {X' = T τ'} {Y = T σ} {Y' = T σ'} {i = coI rep γ} {j = coI rep δ}
              (pathAt wr rep γ) (pathAt wr rep δ) (coI-den wr rep γ) (coI-den wr rep δ)
coI-den wr rep (c-sum {τ = τ} {τ' = τ'} {σ = σ} {σ' = σ'} γ δ) =
  sumIso-den {X = T τ} {X' = T τ'} {Y = T σ} {Y' = T σ'} {i = coI rep γ} {j = coI rep δ}
             (pathAt wr rep γ) (pathAt wr rep δ) (coI-den wr rep γ) (coI-den wr rep δ)
coI-den wr rep (c-nt₁ N γ)   =
  nt-den N (mulG rep (role N)) (wr N) γ (pathAt wr (mulG rep (role N)) γ)
         (coI-den wr (mulG rep (role N)) γ)
coI-den wr rep (c-ax₀ N)     =
  ax-den {X = T (nt₀ N)} {C = TE (rep₀ N)} {i = stepIso (inl N)}
         (sym (T-embE (rep₀ N))) (ua unboxEquiv) (step-den (inl N))
coI-den wr rep (c-ax₁ N τ)   =
  ax-den {X = T (nt₁ N τ)} {C = TB (body N) (T τ)} {i = stepIso (inr (N , τ))}
         (sym (T-inst (body N) τ)) (ua unboxEquiv) (step-den (inr (N , τ)))

------------------------------------------------------------------------
-- THE CROSS-CHECK.

coercion-denotes-transport :
  (wr : WellRoled) → ∀ {τ σ} (γ : Co rep τ σ) →
  Denotes (T τ) (T σ) (fwd (coI rep γ)) (transport (pathOf wr γ))
coercion-denotes-transport wr γ = fst (coI-den wr rep γ)

coercion-denotes-transport-back :
  (wr : WellRoled) → ∀ {τ σ} (γ : Co rep τ σ) →
  Denotes (T σ) (T τ) (bwd (coI rep γ)) (transport (sym (pathOf wr γ)))
coercion-denotes-transport-back wr γ = snd (coI-den wr rep γ)

-- The coercion function: a closure that realises transport.
coerce-function-is-transport :
  (wr : WellRoled) → ∀ {τ σ} (γ : Co rep τ σ) {n} {ρ : UEnv n} →
  Real (arr 𝟙 (T τ) (T σ)) ρ (eraseT (coerceT γ)) (transport (pathOf wr γ))
coerce-function-is-transport wr γ =
    _ , ⇓-lam
  , r-fun (λ w x rx → fst (coI-den wr rep γ) (tvar zero) x (w , ⇓-var zero , rx))
