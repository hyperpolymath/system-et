{-# OPTIONS --cubical --safe #-}
-- Forced by cubical-0.9 (InfectiveImport). No coinduction is used.
{-# OPTIONS --guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- Law checks for a finite carrier.
--
-- Each law becomes a Boolean that Agda computes over all elements.
-- A soundness lemma turns "the Boolean is true" into the law.
-- A law of a finite structure is then proved by `refl`, and a false
-- law gives the Boolean `false`.
module Wager.Grade.Finite where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool.Base using (Bool; true; false)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.List.Base using (List; []; _∷_)

open import Wager.Grade.Algebra

infixr 6 _&&_
infixr 5 _⇒_

_&&_ : Bool → Bool → Bool
true  && y = y
false && y = false

_⇒_ : Bool → Bool → Bool
true  ⇒ y = y
false ⇒ y = true

private
  IsFalse : Bool → Type
  IsFalse false = Unit
  IsFalse true  = ⊥

false≢true : false ≡ true → ⊥
false≢true p = subst IsFalse p tt

true≢false : true ≡ false → ⊥
true≢false p = false≢true (sym p)

&&-l : ∀ x {y} → x && y ≡ true → x ≡ true
&&-l true  _ = refl
&&-l false p = p

&&-r : ∀ x {y} → x && y ≡ true → y ≡ true
&&-r true  p = p
&&-r false p = ⊥.rec (false≢true p)

⇒-elim : ∀ {x y} → (x ⇒ y) ≡ true → x ≡ true → y ≡ true
⇒-elim {true}  p _ = p
⇒-elim {false} _ q = ⊥.rec (false≢true q)

all : {A : Type} → (A → Bool) → List A → Bool
all P []       = true
all P (x ∷ xs) = P x && all P xs

-- A carrier with a complete list of elements and a Boolean equality.
record Finite (A : Type) : Type where
  infix 4 _==_
  field
    elems    : List A
    complete : (P : A → Bool) → all P elems ≡ true → ∀ a → P a ≡ true
    _==_     : A → A → Bool
    ==-sound : ∀ a b → (a == b) ≡ true → a ≡ b

-- Grade operations with a Boolean order.
record BoolOps (A : Type) : Type where
  field
    add mul  : A → A → A
    zero one : A
    leB      : A → A → Bool

toOps : {A : Type} → BoolOps A → GradeOps A
toOps B = record
  { _+_ = add ; _·_ = mul ; 𝟘 = zero ; 𝟙 = one
  ; _≤_ = λ a b → leB a b ≡ true }
  where open BoolOps B

module Check {A : Type} (F : Finite A) (B : BoolOps A) where
  open Finite F
  open BoolOps B
  open GradeOps (toOps B)

  ∀₁ : (A → Bool) → Bool
  ∀₁ P = all P elems

  ∀₂ : (A → A → Bool) → Bool
  ∀₂ P = ∀₁ λ a → ∀₁ (P a)

  ∀₃ : (A → A → A → Bool) → Bool
  ∀₃ P = ∀₁ λ a → ∀₂ (P a)

  ∀₄ : (A → A → A → A → Bool) → Bool
  ∀₄ P = ∀₁ λ a → ∀₃ (P a)

  -- One Boolean for each law field of GradeLaws.
  add-assoc? add-comm? add-zero? mul-assoc? one-mul? mul-one? zero-mul?
    mul-zero? left-distrib? right-distrib? le-refl? le-trans? le-antisym?
    add-mono? mul-mono? : Bool
  add-assoc?     = ∀₃ λ a b c → ((a + b) + c) == (a + (b + c))
  add-comm?      = ∀₂ λ a b → (a + b) == (b + a)
  add-zero?      = ∀₁ λ a → (a + 𝟘) == a
  mul-assoc?     = ∀₃ λ a b c → ((a · b) · c) == (a · (b · c))
  one-mul?       = ∀₁ λ a → (𝟙 · a) == a
  mul-one?       = ∀₁ λ a → (a · 𝟙) == a
  zero-mul?      = ∀₁ λ a → (𝟘 · a) == 𝟘
  mul-zero?      = ∀₁ λ a → (a · 𝟘) == 𝟘
  left-distrib?  = ∀₃ λ a b c → (a · (b + c)) == ((a · b) + (a · c))
  right-distrib? = ∀₃ λ a b c → ((a + b) · c) == ((a · c) + (b · c))
  le-refl?       = ∀₁ λ a → leB a a
  le-trans?      = ∀₃ λ a b c → leB a b ⇒ leB b c ⇒ leB a c
  le-antisym?    = ∀₂ λ a b → leB a b ⇒ leB b a ⇒ (a == b)
  add-mono?      = ∀₄ λ a b c d → leB a b ⇒ leB c d ⇒ leB (a + c) (b + d)
  mul-mono?      = ∀₄ λ a b c d → leB a b ⇒ leB c d ⇒ leB (a · c) (b · d)

  private
    s₁ : ∀ {P} → ∀₁ P ≡ true → ∀ a → P a ≡ true
    s₁ {P} = complete P

    s₂ : ∀ {P} → ∀₂ P ≡ true → ∀ a b → P a b ≡ true
    s₂ h a = s₁ (s₁ h a)

    s₃ : ∀ {P} → ∀₃ P ≡ true → ∀ a b c → P a b c ≡ true
    s₃ h a = s₂ (s₁ h a)

    s₄ : ∀ {P} → ∀₄ P ≡ true → ∀ a b c d → P a b c d ≡ true
    s₄ h a = s₃ (s₁ h a)

  -- Soundness of each check.
  add-assoc! : add-assoc? ≡ true → ∀ a b c → (a + b) + c ≡ a + (b + c)
  add-assoc! h a b c = ==-sound _ _ (s₃ h a b c)

  add-comm! : add-comm? ≡ true → ∀ a b → a + b ≡ b + a
  add-comm! h a b = ==-sound _ _ (s₂ h a b)

  add-zero! : add-zero? ≡ true → ∀ a → a + 𝟘 ≡ a
  add-zero! h a = ==-sound _ _ (s₁ h a)

  mul-assoc! : mul-assoc? ≡ true → ∀ a b c → (a · b) · c ≡ a · (b · c)
  mul-assoc! h a b c = ==-sound _ _ (s₃ h a b c)

  one-mul! : one-mul? ≡ true → ∀ a → 𝟙 · a ≡ a
  one-mul! h a = ==-sound _ _ (s₁ h a)

  mul-one! : mul-one? ≡ true → ∀ a → a · 𝟙 ≡ a
  mul-one! h a = ==-sound _ _ (s₁ h a)

  zero-mul! : zero-mul? ≡ true → ∀ a → 𝟘 · a ≡ 𝟘
  zero-mul! h a = ==-sound _ _ (s₁ h a)

  mul-zero! : mul-zero? ≡ true → ∀ a → a · 𝟘 ≡ 𝟘
  mul-zero! h a = ==-sound _ _ (s₁ h a)

  left-distrib! : left-distrib? ≡ true → ∀ a b c → a · (b + c) ≡ (a · b) + (a · c)
  left-distrib! h a b c = ==-sound _ _ (s₃ h a b c)

  right-distrib! : right-distrib? ≡ true → ∀ a b c → (a + b) · c ≡ (a · c) + (b · c)
  right-distrib! h a b c = ==-sound _ _ (s₃ h a b c)

  le-refl! : le-refl? ≡ true → ∀ a → a ≤ a
  le-refl! h a = s₁ h a

  le-trans! : le-trans? ≡ true → ∀ a b c → a ≤ b → b ≤ c → a ≤ c
  le-trans! h a b c p q = ⇒-elim (⇒-elim (s₃ h a b c) p) q

  le-antisym! : le-antisym? ≡ true → ∀ a b → a ≤ b → b ≤ a → a ≡ b
  le-antisym! h a b p q = ==-sound _ _ (⇒-elim (⇒-elim (s₂ h a b) p) q)

  add-mono! : add-mono? ≡ true → ∀ a b c d → a ≤ b → c ≤ d → (a + c) ≤ (b + d)
  add-mono! h a b c d p q = ⇒-elim (⇒-elim (s₄ h a b c d) p) q

  mul-mono! : mul-mono? ≡ true → ∀ a b c d → a ≤ b → c ≤ d → (a · c) ≤ (b · d)
  mul-mono! h a b c d p q = ⇒-elim (⇒-elim (s₄ h a b c d) p) q

  -- All 15 checks together give the laws.
  mkLaws :
    add-assoc? ≡ true → add-comm? ≡ true → add-zero? ≡ true →
    mul-assoc? ≡ true → one-mul? ≡ true → mul-one? ≡ true →
    zero-mul? ≡ true → mul-zero? ≡ true →
    left-distrib? ≡ true → right-distrib? ≡ true →
    le-refl? ≡ true → le-trans? ≡ true → le-antisym? ≡ true →
    add-mono? ≡ true → mul-mono? ≡ true →
    GradeLaws (toOps B)
  mkLaws h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ h₁₃ h₁₄ h₁₅ = record
    { add-assoc = add-assoc! h₁ ; add-comm = add-comm! h₂ ; add-zero = add-zero! h₃
    ; mul-assoc = mul-assoc! h₄ ; one-mul = one-mul! h₅ ; mul-one = mul-one! h₆
    ; zero-mul = zero-mul! h₇ ; mul-zero = mul-zero! h₈
    ; left-distrib = left-distrib! h₉ ; right-distrib = right-distrib! h₁₀
    ; le-refl = le-refl! h₁₁ ; le-trans = le-trans! h₁₂ ; le-antisym = le-antisym! h₁₃
    ; add-mono = add-mono! h₁₄ ; mul-mono = mul-mono! h₁₅ }

  -- The 14 checks without `mul-zero?`.
  mkLaws14 :
    add-assoc? ≡ true → add-comm? ≡ true → add-zero? ≡ true →
    mul-assoc? ≡ true → one-mul? ≡ true → mul-one? ≡ true →
    zero-mul? ≡ true →
    left-distrib? ≡ true → right-distrib? ≡ true →
    le-refl? ≡ true → le-trans? ≡ true → le-antisym? ≡ true →
    add-mono? ≡ true → mul-mono? ≡ true →
    GradeLawsExceptMulZero (toOps B)
  mkLaws14 h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₉ h₁₀ h₁₁ h₁₂ h₁₃ h₁₄ h₁₅ = record
    { add-assoc = add-assoc! h₁ ; add-comm = add-comm! h₂ ; add-zero = add-zero! h₃
    ; mul-assoc = mul-assoc! h₄ ; one-mul = one-mul! h₅ ; mul-one = mul-one! h₆
    ; zero-mul = zero-mul! h₇
    ; left-distrib = left-distrib! h₉ ; right-distrib = right-distrib! h₁₀
    ; le-refl = le-refl! h₁₁ ; le-trans = le-trans! h₁₂ ; le-antisym = le-antisym! h₁₃
    ; add-mono = add-mono! h₁₄ ; mul-mono = mul-mono! h₁₅ }
