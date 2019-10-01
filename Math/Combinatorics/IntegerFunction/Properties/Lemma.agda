{-# OPTIONS --without-K --safe #-}

module Math.Combinatorics.IntegerFunction.Properties.Lemma where

open import Data.Integer
open import Data.Integer.Solver
open import Relation.Binary.PropositionalEquality

lemma₁ : ∀ a b c d → a * b * (c * d) ≡ (a * c) * (b * d)
lemma₁ = solve 4 (λ a b c d → a :* b :* (c :* d) := (a :* c) :* (b :* d) ) refl
  where open +-*-Solver

lemma₂ : ∀ n → n ≡ 1ℤ + (n - 1ℤ)
lemma₂ = solve 1 (λ n → n := con 1ℤ :+ (n :- con 1ℤ)) refl
  where open +-*-Solver

lemma₃ : ∀ m n → m ≡ n + (m - n)
lemma₃ = solve 2 (λ m n → m := n :+ (m :- n)) refl
  where open +-*-Solver
