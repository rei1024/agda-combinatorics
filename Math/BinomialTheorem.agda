------------------------------------------------------------------------
-- Binomial theorem
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --exact-split #-}

open import Algebra
import Algebra.Operations.Semiring as SemiringOperations

module Math.BinomialTheorem {e l} (SM : Semiring e l) where

open import Data.Nat using (suc; _∸_)
open import Data.Fin using (toℕ)

open import Math.Combinatorics.Function
open import Function

open Semiring SM
open SemiringOperations SM

{-
binomialTheorem : ∀ x y n →
  ((x + y) ^ n) ≈ sumₜ-syntax (suc n) (λ k → C n (toℕ k) × (x ^ toℕ k * y ^ (n ∸ toℕ k)))
binomialTheorem x y 0       = {!   !}
binomialTheorem x y (suc n) = {!   !}
-}
