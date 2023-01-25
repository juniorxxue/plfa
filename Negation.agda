module _ where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s; _≤_)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥; ⊥-elim)

¬¬-intro : ∀ {A : Set}
  → A
  → ¬ ¬ A
¬¬-intro x ¬x = ¬x x

contraposition : ∀ {A B : Set}
  → (A → B)
  → (¬ B → ¬ A)
contraposition f ¬y x = ¬y (f x)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y  =  ¬ (x ≡ y)

_ : 1 ≢ 2
_ = λ () -- there's no evidence for 1 ≡ 2

<-irreflexive : ∀ (n : ℕ) → ¬ (n < n)
<-irreflexive (suc n) (s≤s n<n) = <-irreflexive n n<n
