module _ where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; _≢_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.String using (String; _≟_)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (False; toWitnessFalse)

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
--                                                                  --
--                              Syntax                              --
--                                                                  --
----------------------------------------------------------------------


Id : Set
Id = String

data Type : Set where
  `ℕ : Type
  _⇒_ : Type → Type → Type

data Context : Set where
  ∅ : Context
  _,_⦂_ : Context → Id → Type → Context

data Term⁺ : Set
data Term⁻  : Set

-- terms can be inferred
-- we introduce a unit term
data Term⁺ where
  u  : Term⁺  -- should unit type be inferred. According to the recipe, constructor should be checked (?)
  `_ : Id → Term⁺
  _·_ : Term⁺ → Term⁻ → Term⁺
  _↓_ : Term⁻ → Type → Term⁺

-- terms cannot ensure to infer a type
data Term⁻ where
  ƛ_⇒_ : Id → Term⁻ → Term⁻
  _↑ : Term⁺ → Term⁻

----------------------------------------------------------------------
--                                                                  --
--                              Typing                              --
--                                                                  --
----------------------------------------------------------------------

data _∋_⦂_ : Context → Id → Type → Set where

  Z : ∀ {Γ x A}
    → Γ , x ⦂ A ∋ x ⦂ A
