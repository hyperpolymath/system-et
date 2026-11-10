{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- DESIGN-CHOICES.adoc, DC-0.3: matches on kinded syntax.
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- Consequences of "conversion is normalize-then-compare" for types of
-- kind ★: convertible types have the same head, and the type formers
-- are injective up to conversion. The term metatheory (T0) uses these
-- facts where a System FC proof uses coercion inversion.
open import Wager.L1.Signature

module Wager.L1.Heads (S : Sig) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool.Base using (Bool; true; false)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Sigma using (_×_)

open import Wager.Grade.Finite using (true≢false)
open import Wager.L1.Syntax S
open import Wager.L1.Conversion S
open import Wager.L1.Normal S
open import Wager.L1.Eval S
open import Wager.L1.Equality S

private
  variable
    Γ : Ctx

data Head : Type where
  hne hbase hcapp harr hprod hsum : Head

head : Nf Γ ★ → Head
head (ne _)       = hne
head (nbase _)    = hbase
head (ncapp _ _)  = hcapp
head (narr _ _ _) = harr
head (_ n⊗ _)     = hprod
head (_ n⊕ _)     = hsum

sameHead : Head → Head → Bool
sameHead hne   hne   = true
sameHead hbase hbase = true
sameHead hcapp hcapp = true
sameHead harr  harr  = true
sameHead hprod hprod = true
sameHead hsum  hsum  = true
sameHead _     _     = false

private
  sameHead-refl : ∀ h → sameHead h h ≡ true
  sameHead-refl hne   = refl
  sameHead-refl hbase = refl
  sameHead-refl hcapp = refl
  sameHead-refl harr  = refl
  sameHead-refl hprod = refl
  sameHead-refl hsum  = refl

-- Convertible types of kind ★ have the same head. For two concrete
-- types with different heads, the second argument is `refl`.
headClash : {A B : Ty Γ ★} → DefEq A B →
            sameHead (head (nf A)) (head (nf B)) ≡ false → ⊥
headClash {A = A} {B = B} d q =
  true≢false
    (sym (subst (λ h → sameHead (head (nf A)) h ≡ true)
                (cong head (defEq→nf d)) (sameHead-refl (head (nf A))))
     ∙ q)

------------------------------------------------------------------------
-- Injectivity of the type formers, up to conversion.

private
  arrGrade : TG → Nf Γ ★ → TG
  arrGrade d (narr q _ _) = q
  arrGrade d _            = d

  fstArg : Nf Γ ★ → Nf Γ ★
  fstArg (narr _ a _) = a
  fstArg (a n⊗ _)     = a
  fstArg (a n⊕ _)     = a
  fstArg (ncapp _ a)  = a
  fstArg v            = v

  sndArg : Nf Γ ★ → Nf Γ ★
  sndArg (narr _ _ b) = b
  sndArg (_ n⊗ b)     = b
  sndArg (_ n⊕ b)     = b
  sndArg v            = v

  cappCon : Con₁ → Nf Γ ★ → Con₁
  cappCon d (ncapp c _) = c
  cappCon d _           = d

  baseOf : Base → Nf Γ ★ → Base
  baseOf d (nbase b) = b
  baseOf d _         = d

arr-inj : ∀ {q q'} {A B A' B' : Ty Γ ★} → DefEq (arr q A B) (arr q' A' B') →
          (q ≡ q') × DefEq A A' × DefEq B B'
arr-inj {q = q} d =
  let p = defEq→nf d
  in cong (arrGrade q) p , nf→defEq (cong fstArg p) , nf→defEq (cong sndArg p)

prod-inj : {A B A' B' : Ty Γ ★} → DefEq (A ⊗ B) (A' ⊗ B') → DefEq A A' × DefEq B B'
prod-inj d =
  let p = defEq→nf d in nf→defEq (cong fstArg p) , nf→defEq (cong sndArg p)

sum-inj : {A B A' B' : Ty Γ ★} → DefEq (A ⊕ B) (A' ⊕ B') → DefEq A A' × DefEq B B'
sum-inj d =
  let p = defEq→nf d in nf→defEq (cong fstArg p) , nf→defEq (cong sndArg p)

capp-inj : ∀ {c c'} {A A' : Ty Γ ★} → DefEq (capp c A) (capp c' A') →
           (c ≡ c') × DefEq A A'
capp-inj {c = c} d =
  let p = defEq→nf d in cong (cappCon c) p , nf→defEq (cong fstArg p)

base-inj : ∀ {b b'} → DefEq {Γ = Γ} (base b) (base b') → b ≡ b'
base-inj {b = b} d = cong (baseOf b) (defEq→nf d)
