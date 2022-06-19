module overview.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)


+-assoc : ∀ (m n p : ℕ)
  → (m + n) + p ≡ m + (n + p)
+-assoc zero n p = refl
+-assoc (suc m) n p = cong suc (+-assoc m n p)


+-identity-r : ∀ (m : ℕ)
  → m + zero ≡ m
+-identity-r zero = refl
+-identity-r (suc m) = cong suc (+-identity-r m)

+-succ : ∀ (m n : ℕ)
  → m + suc n ≡ suc (m + n)
+-succ zero n = refl
+-succ (suc m) n = cong suc (+-succ m n)

+-comm : ∀ (m n : ℕ)
  → m + n ≡ n + m
+-comm m zero = +-identity-r m
+-comm m (suc n) rewrite +-succ m n = cong suc (+-comm m n)
