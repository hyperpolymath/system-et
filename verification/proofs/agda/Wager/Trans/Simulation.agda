{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- DESIGN-CHOICES.adoc, DC-0.3: matches on coercions, terms and values.
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- The erased translation behaves as the erased source (Stage 4: T3 and
-- the behaviour part of T5).
--
--   1. The transformer of a coercion does not change the erased
--      behaviour: if the erasure of t evaluates to a value related to
--      v, then the erasure of the transformed t also does (`CoRel`).
--      A trope transition vanishes in the erasure, so only the
--      functorial maps need an argument.
--   2. The erasure of a source term and the erasure of its translation
--      evaluate to related values (`fund`).
open import Cubical.Foundations.Prelude
open import Wager.FC.Signature
open import Wager.Grade.Algebra
import Wager.Trans.Scheme

module Wager.Trans.Simulation
  (SS : SSig) (Sc : Wager.Trans.Scheme.StateScheme SS)
  {R : Type} (ops : GradeOps R) where

open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.FinData.Base using (Fin; zero; suc)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd; Σ-syntax)
open import Cubical.Data.Sum.Base using (_⊎_; inl; inr)

open import Wager.Role.Role
open import Wager.Erased.Untyped using (ETy; ebase; earr; eprod; esum)
open import Wager.FC.Types SS
open import Wager.FC.Coercion SS
open import Wager.FC.Term SS
open import Wager.FC.RoleSoundness SS using (rep-sound)
open import Wager.Trans.Target SS Sc ops using (T; TB; Inst; wrap; unwrap; arr)
open GradeOps ops using (𝟙)
open import Wager.Trans.Coercion SS Sc ops
open import Wager.Erased.LogRel litTy

private
  variable
    n : ℕ

-- A transformer keeps the erased behaviour at the erased type a.
CoRel : ETy Base → Tr → Type
CoRel a f = ∀ {n} (v : UVal) {ρ : UEnv n} (t : Tm n) →
            𝒞 a v ρ (eraseT t) → 𝒞 a v ρ (eraseT (f t))

CoRelIso : ETy Base → Iso → Type
CoRelIso a i = CoRel a (fwd i) × CoRel a (bwd i)

------------------------------------------------------------------------
-- Each building block keeps the erased behaviour.

id-rel : ∀ {a} → CoRelIso a idIso
id-rel = (λ v t h → h) , (λ v t h → h)

swap-rel : ∀ {a i} → CoRelIso a i → CoRelIso a (swapIso i)
swap-rel (f , g) = g , f

comp-rel : ∀ {a i j} → CoRelIso a i → CoRelIso a j → CoRelIso a (compIso i j)
comp-rel {i = i} {j = j} (f , g) (f' , g') =
    (λ v t h → f' v (fwd i t) (f v t h))
  , (λ v t h → g v (bwd j t) (g' v t h))

-- A trope transition vanishes in the erasure.
step-rel : ∀ {a} (x : Inst) → CoRelIso a (stepIso x)
step-rel x = (λ v t h → h) , (λ v t h → h)

arrMap-rel : ∀ {a b} X A (h g : Tr) → CoRel a h → CoRel b g →
             CoRel (earr a b) (arrMap X A h g)
arrMap-rel X A h g ch cg _ {ρ = ρ} t (_ , dt , r-clo {ρ' = ρg} hfg) =
    _ , ⇓-app ⇓-lam dt ⇓-lam
  , r-clo (λ v w hvw →
      let (w' , dw' , hvw')       = ch v (tvar zero) (w , ⇓-var zero , hvw)
          (r , s , dr , ds , hrs) = hfg v w' hvw'
          (s' , ds' , hrs')       = cg r (tapp (tvar (suc zero)) (h (tvar zero)))
                                       (s , ⇓-app (⇓-var (suc zero)) dw' ds , hrs)
      in r , s' , dr , ds' , hrs')

arrIso-rel : ∀ {a b} A A' B B' i j → CoRelIso a i → CoRelIso b j →
             CoRelIso (earr a b) (arrIso A A' B B' i j)
arrIso-rel A A' B B' i j (f , g) (f' , g') =
    arrMap-rel (arr 𝟙 A B) A' (bwd i) (fwd j) g f'
  , arrMap-rel (arr 𝟙 A' B') A (fwd i) (bwd j) f g'

prodMap-rel : ∀ {a b} {f g : Tr} → CoRel a f → CoRel b g → CoRel (eprod a b) (prodMap f g)
prodMap-rel cf cg _ t (_ , dt , r-pair {v₁ = v₁} {v₂ = v₂} {w₁ = w₁} {w₂ = w₂} h₁ h₂) =
  let (w₁' , d₁ , h₁') = cf v₁ (tvar (suc zero)) (w₁ , ⇓-var (suc zero) , h₁)
      (w₂' , d₂ , h₂') = cg v₂ (tvar zero) (w₂ , ⇓-var zero , h₂)
  in vpair w₁' w₂' , ⇓-letp dt (⇓-pair d₁ d₂) , r-pair h₁' h₂'

prodIso-rel : ∀ {a b i j} → CoRelIso a i → CoRelIso b j → CoRelIso (eprod a b) (prodIso i j)
prodIso-rel {i = i} {j = j} (f , g) (f' , g') =
    prodMap-rel {f = fwd i} {g = fwd j} f f'
  , prodMap-rel {f = bwd i} {g = bwd j} g g'

sumMap-rel : ∀ {a b} {f g : Tr} → CoRel a f → CoRel b g → CoRel (esum a b) (sumMap f g)
sumMap-rel cf cg _ t (_ , dt , r-inl {v = v} {w = w} h) =
  let (w' , d , h') = cf v (tvar zero) (w , ⇓-var zero , h)
  in vinl w' , ⇓-casel dt (⇓-inl d) , r-inl h'
sumMap-rel cf cg _ t (_ , dt , r-inr {v = v} {w = w} h) =
  let (w' , d , h') = cg v (tvar zero) (w , ⇓-var zero , h)
  in vinr w' , ⇓-caser dt (⇓-inr d) , r-inr h'

sumIso-rel : ∀ {a b i j} → CoRelIso a i → CoRelIso b j → CoRelIso (esum a b) (sumIso i j)
sumIso-rel {i = i} {j = j} (f , g) (f' , g') =
    sumMap-rel {f = fwd i} {g = fwd j} f f'
  , sumMap-rel {f = bwd i} {g = bwd j} g g'

-- The map of a body, at the erased type of the body.
body-rel : ∀ β v {e} X Y i → CoRelIso e i → CoRelIso (erB β v e) (bodyIso β X Y i)
body-rel bvar        v X Y i c = c
body-rel (bbase b)   v X Y i c = id-rel
body-rel (barr β γ)  v X Y i c =
  arrIso-rel (TB β X) (TB β Y) (TB γ X) (TB γ Y) (bodyIso β X Y i) (bodyIso γ X Y i)
             (body-rel β v X Y i c) (body-rel γ v X Y i c)
body-rel (bprod β γ) v X Y i c =
  prodIso-rel {i = bodyIso β X Y i} {j = bodyIso γ X Y i} (body-rel β v X Y i c) (body-rel γ v X Y i c)
body-rel (bsum β γ)  v X Y i c =
  sumIso-rel {i = bodyIso β X Y i} {j = bodyIso γ X Y i} (body-rel β v X Y i c) (body-rel γ v X Y i c)
body-rel (bfam F β)  v X Y i c = id-rel

------------------------------------------------------------------------
-- The transformer of a coercion keeps the erased behaviour. The role
-- check is used to compare the erased types of the two sides.

module _ (wr : WellRoled) where

  co-rel : ∀ r {τ σ} (γ : Co r τ σ) → CoRelIso (er τ) (coI r γ)
  co-rel nom γ = id-rel
  co-rel ph  γ = id-rel
  co-rel rep (c-sym {τ = τ} {σ = σ} γ) =
    subst (λ a → CoRelIso a (swapIso (coI rep γ))) (rep-sound wr γ) (swap-rel {i = coI rep γ} (co-rel rep γ))
  co-rel rep (c-trans {τ = τ} γ δ) =
    comp-rel {i = coI rep γ} {j = coI rep δ} (co-rel rep γ)
             (subst (λ a → CoRelIso a (coI rep δ)) (sym (rep-sound wr γ)) (co-rel rep δ))
  co-rel rep (c-sub γ)     = id-rel
  co-rel rep (c-arr {τ = τ} {τ' = τ'} {σ = σ} {σ' = σ'} γ δ) =
    arrIso-rel (T τ) (T τ') (T σ) (T σ') (coI rep γ) (coI rep δ) (co-rel rep γ) (co-rel rep δ)
  co-rel rep (c-prod γ δ)  = prodIso-rel {i = coI rep γ} {j = coI rep δ} (co-rel rep γ) (co-rel rep δ)
  co-rel rep (c-sum γ δ)   = sumIso-rel {i = coI rep γ} {j = coI rep δ} (co-rel rep γ) (co-rel rep δ)
  co-rel rep (c-nt₁ {τ = τ} {σ = σ} N γ) =
    let (f , g) = body-rel (body N) (ev τ) (T τ) (T σ) (coI (mulG rep (role N)) γ)
                           (co-rel (mulG rep (role N)) γ)
    in (λ v t h → f v (step (unwrap , inr (N , τ)) t) h)
     , (λ v t h → g v (step (unwrap , inr (N , σ)) t) h)
  co-rel rep (c-ax₀ N)     = step-rel (inl N)
  co-rel rep (c-ax₁ N τ)   = step-rel (inr (N , τ))

  ----------------------------------------------------------------------
  -- T3.

  private
    idV : UVal
    idV = vclo ∅ᵉ (uvar zero)

  -- The erased coercion function is related to the identity function.
  coerce-identity : ∀ {τ σ} (γ : Co rep τ σ) →
    Σ[ f ∈ UVal ] (∅ᵉ ⊢ eraseT (coerceT γ) ⇓ f) × 𝒱 (earr (er τ) (er τ)) idV f
  coerce-identity γ =
      _ , ⇓-lam
    , r-clo (λ v w h →
        let (w' , d , h') = fst (co-rel rep γ) v (tvar zero) (w , ⇓-var zero , h)
        in v , w' , ⇓-var zero , d , h')

  -- At a first-order type the erased coercion gives its argument back.
  coerce-identity-fo : ∀ {τ σ} (γ : Co rep τ σ) → FO (er τ) → ∀ v → 𝒱 (er τ) v v →
    Σ[ w ∈ UVal ] ((v ∷ᵉ ∅ᵉ) ⊢ eraseT (fwd (coI rep γ) (tvar zero)) ⇓ w) × (w ≡ v)
  coerce-identity-fo γ fo v h =
    let (w , d , h') = fst (co-rel rep γ) v (tvar zero) (v , ⇓-var zero , h)
    in w , d , sym (𝒱-fo fo h')

  ----------------------------------------------------------------------
  -- T5, behaviour.

  private
    EnvRel : SCx n → UEnv n → UEnv n → Type
    EnvRel Γ ρ ρ' = ∀ i → 𝒱 (er (Γ i)) (ρ i) (ρ' i)

    env-ext : ∀ {Γ : SCx n} {ρ ρ' : UEnv n} {v w} τ →
              EnvRel Γ ρ ρ' → 𝒱 (er τ) v w → EnvRel (Γ ▹ˢ τ) (v ∷ᵉ ρ) (w ∷ᵉ ρ')
    env-ext τ h hvw zero    = hvw
    env-ext τ h hvw (suc i) = h i

  fund : ∀ {Γ : SCx n} {τ} (e : STm Γ τ) {ρ ρ' : UEnv n} → EnvRel Γ ρ ρ' →
         ℰ (er τ) ρ (eraseTm e) ρ' (eraseT (tr e))
  fund (svar i) h = _ , ⇓-var i , _ , ⇓-var i , h i
  fund (slam {τ = τ} b) h =
      _ , ⇓-lam , _ , ⇓-lam
    , r-clo (λ v w hvw →
        let (r , dr , s , ds , hrs) = fund b (env-ext τ h hvw)
        in r , s , dr , ds , hrs)
  fund (sapp f a) h with fund f h | fund a h
  ... | _ , df , _ , df' , r-clo hf | va , da , wa , da' , ha =
    let (r , s , dr , ds , hrs) = hf va wa ha
    in r , ⇓-app df da dr , s , ⇓-app df' da' ds , hrs
  fund (spair s t) h =
    let (v₁ , d₁ , w₁ , d₁' , h₁) = fund s h
        (v₂ , d₂ , w₂ , d₂' , h₂) = fund t h
    in vpair v₁ v₂ , ⇓-pair d₁ d₂ , vpair w₁ w₂ , ⇓-pair d₁' d₂' , r-pair h₁ h₂
  fund (sletp {τ = τ} {σ = σ} s b) h with fund s h
  ... | _ , ds , _ , ds' , r-pair h₁ h₂ =
    let (r , dr , r' , dr' , hr) = fund b (env-ext σ (env-ext τ h h₁) h₂)
    in r , ⇓-letp ds dr , r' , ⇓-letp ds' dr' , hr
  fund (sinl t) h =
    let (v , d , w , d' , hv) = fund t h
    in vinl v , ⇓-inl d , vinl w , ⇓-inl d' , r-inl hv
  fund (sinr t) h =
    let (v , d , w , d' , hv) = fund t h
    in vinr v , ⇓-inr d , vinr w , ⇓-inr d' , r-inr hv
  fund (scase {τ = τ} {σ = σ} s l r) h with fund s h
  ... | _ , ds , _ , ds' , r-inl hv =
    let (x , dx , x' , dx' , hx) = fund l (env-ext τ h hv)
    in x , ⇓-casel ds dx , x' , ⇓-casel ds' dx' , hx
  ... | _ , ds , _ , ds' , r-inr hv =
    let (x , dx , x' , dx' , hx) = fund r (env-ext σ h hv)
    in x , ⇓-caser ds dx , x' , ⇓-caser ds' dx' , hx
  fund (slit ℓ) h = vlit ℓ , ⇓-lit , vlit ℓ , ⇓-lit , r-lit ℓ refl
  fund (cast {τ = τ} {σ = σ} γ e) {ρ' = ρ'} h =
    let (v , d , c) = fund e h
    in v , d , subst (λ a → 𝒞 a v ρ' (eraseT (tr (cast γ e)))) (rep-sound wr γ)
                     (fst (co-rel rep γ) v (tr e) c)

  -- A closed program.
  behaviour : ∀ {τ} (e : STm ∅ˢ τ) →
    Σ[ v ∈ UVal ] Σ[ w ∈ UVal ]
      (∅ᵉ ⊢ eraseTm e ⇓ v) × (∅ᵉ ⊢ eraseT (tr e) ⇓ w) × 𝒱 (er τ) v w
  behaviour e =
    let (v , d , w , d' , h) = fund e {ρ = ∅ᵉ} {ρ' = ∅ᵉ} (λ ())
    in v , w , d , d' , h

  behaviour-fo : ∀ {τ} (e : STm ∅ˢ τ) → FO (er τ) →
    Σ[ v ∈ UVal ] (∅ᵉ ⊢ eraseTm e ⇓ v) × (∅ᵉ ⊢ eraseT (tr e) ⇓ v)
  behaviour-fo e fo =
    let (v , w , d , d' , h) = behaviour e
    in v , d , subst (λ x → ∅ᵉ ⊢ eraseT (tr e) ⇓ x) (sym (𝒱-fo fo h)) d'
