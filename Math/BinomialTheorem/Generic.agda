------------------------------------------------------------------------
-- Binomial theorem
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --exact-split #-}

-- agda-stdlib
open import Algebra
import Algebra.Operations.Semiring as SemiringOperations
import Algebra.Properties.CommutativeMonoid as CommutativeMonoidProperties
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

module Math.BinomialTheorem.Generic {e l} (SR : Semiring e l) where

-- agda-stdlib
open import Data.Nat as ℕ using (zero; suc; _∸_)
open import Function

-- agda-combinatorics
open import Math.Combinatorics.Function
open import Math.Combinatorics.Function.Properties

-- agda-misc
open import Math.NumberTheory.Summation.Generic
open import Math.NumberTheory.Summation.Generic.Properties

open Semiring SR
open SemiringOperations SR
open CommutativeMonoidProperties +-commutativeMonoid
open SetoidReasoning setoid
open MonoidSummation +-monoid
open SemiringSummationProperties SR
{-
theorem : ∀ x y n →
  (x + y) ^ n ≈ Σ[ k ≤ n ] (C n k × (x ^ k * y ^ (n ∸ k)))
theorem x y 0       = begin
  1#
    ≈⟨ sym $ *-identityʳ 1# ⟩
  1# * 1#
    ≈⟨ sym $ +-identityʳ (1# * 1#) ⟩
  1# * 1# + 0#
    ≡⟨⟩
  C 0 0 × ((x ^ 0) * y ^ (0 ∸ 0))
    ≈⟨ sym $ Σ≤[0,f]≈f[0] (λ k → C 0 k × (x ^ k * y ^ (0 ∸ k))) ⟩
  Σ≤ 0 (λ k → C 0 k × (x ^ k * y ^ (0 ∸ k)))
    ∎
theorem x y (suc n) = begin
  (x + y) * (x + y) ^ n ≈⟨ *-congˡ $ theorem x y n ⟩
  (x + y) * Σ[ k ≤ n ] (C n k × (x ^ k * y ^ (n ∸ k))) ≈⟨ {!   !} ⟩
  Σ≤ (suc n) (λ k → C (suc n) k × (x ^ k * y ^ (suc n ∸ k))) ∎
-}
