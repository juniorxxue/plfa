module _ where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; _≢_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.String using (String; _≟_)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse; fromWitnessFalse)

infix   4  _∋_⦂_
infix   4  _⊢_↑_
infix   4  _⊢_↓_
infixl  5  _,_⦂_

infixr  7  _⇒_

infix   5  ƛ_⇒_
infix   6  _↑
infix   6  _↓_
infixl  7  _·_
infix   9  `_

----------------------------------------------------------------------
--+                                                                +--
--+                             Syntax                             +--
--+                                                                +--
----------------------------------------------------------------------

Id : Set
Id = String

data Type : Set where
  Unit : Type
  Int : Type
  _⇒_ : Type → Type → Type

data Context : Set where
  ∅ : Context
  _,_⦂_ : Context → Id → Type → Context

data Term⁺ : Set
data Term⁻  : Set

-- terms can be inferred
-- we introduce a unit term
data Term⁺ where
  `_ : Id → Term⁺
  _·_ : Term⁺ → Term⁻ → Term⁺
  _↓_ : Term⁻ → Type → Term⁺

-- terms cannot ensure to infer a type
data Term⁻ where
  u  : Term⁻  -- should unit type be inferred? According to the recipe, constructor should be checked (?)
  ƛ_⇒_ : Id → Term⁻ → Term⁻
  _↑ : Term⁺ → Term⁻

----------------------------------------------------------------------
--+                                                                +--
--+                             Typing                             +--
--+                                                                +--
----------------------------------------------------------------------

data _∋_⦂_ : Context → Id → Type → Set where

  Z : ∀ {Γ x A}
      --------------------
    → Γ , x ⦂ A ∋ x ⦂ A

  S : ∀ {Γ x y A B}
    → {x≢y : False (x ≟ y)}
    → Γ ∋ x ⦂ A
      ------------------
    → Γ , y ⦂ B ∋ x ⦂ A


_ : ∅ , "x" ⦂ Int , "y" ⦂ Unit ∋ "x" ⦂ Int
_ = S Z


data _⊢_↑_ : Context → Term⁺ → Type → Set
data _⊢_↓_ : Context → Term⁻ → Type → Set

data _⊢_↑_ where

  ⊢var : ∀ {Γ A x}
    → Γ ∋ x ⦂ A
    → Γ ⊢ ` x ↑ A

  ⊢app : ∀ {Γ e₁ e₂ A B}
    → Γ ⊢ e₁ ↑ A ⇒ B
    → Γ ⊢ e₂ ↓ A
    → Γ ⊢ e₁ · e₂ ↑ B

  ⊢ann : ∀ {Γ e A}
    → Γ ⊢ e ↓ A
    → Γ ⊢ (e ↓ A) ↑ A

data _⊢_↓_ where

  ⊢u : ∀ {Γ}
    → Γ ⊢ u ↓ Unit

  ⊢lam : ∀ {Γ x e A B}
    → Γ , x ⦂ A ⊢ e ↓ B
    → Γ ⊢ ƛ x ⇒ e ↓ A ⇒ B

  -- I'm thinking of why create a extra term (e ↑)
  -- syntax directed: any term is check-able
  ⊢sub : ∀ {Γ e A B}
    → Γ ⊢ e ↑ A
    → A ≡ B
    → Γ ⊢ (e ↑) ↓ B


----------------------------------------------------------------------
--+                                                                +--
--+                  Synthesize and Inherit Types                  +--
--+                                                                +--
----------------------------------------------------------------------

ext∋ : ∀ {Γ B x y}
  → x ≢ y
  → ¬ (∃[ A ] Γ ∋ x ⦂ A)
  → ¬ (∃[ A ] Γ , y ⦂ B ∋ x ⦂ A)


lookup : ∀ (Γ : Context) (x : Id)
  → Dec (∃[ A ] Γ ∋ x ⦂ A)


synthesize : ∀ (Γ : Context) (e : Term⁺)
  → Dec (∃[ A ] Γ ⊢ e ↑ A)
synthesize Γ (` x) = {!!}
synthesize Γ (e · x) = {!!}
synthesize Γ (x ↓ x₁) = {!!}


inherit : ∀ (Γ : Context) (e : Term⁻) (A : Type)
  → Dec (Γ ⊢ e ↓ A)
