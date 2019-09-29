------------------------------------------------------------------------
-- Binomial theorem
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --exact-split #-}

open import Algebra
import Algebra.Operations.Semiring as SemiringOperations
import Algebra.Properties.CommutativeMonoid as CommutativeMonoidProperties
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
module Math.BinomialTheorem {e l} (SM : Semiring e l) where

open import Data.Fin using (toℕ)
open import Data.Nat as ℕ using (zero; suc; _∸_)
open import Data.Table as Table
open import Math.Combinatorics.Function
open import Math.Combinatorics.Function.Properties
open import Function

open Semiring SM
open SemiringOperations SM
open CommutativeMonoidProperties +-commutativeMonoid
open SetoidReasoning setoid

{-
theorem : ∀ x y n →
  (x + y) ^ n ≈ ∑[ kF < suc n ] (let k = toℕ kF in C n k × (x ^ k * y ^ (n ∸ k)))
theorem x y 0       = begin
  1#                        ≈⟨ sym $ *-identityʳ 1# ⟩
  1# * 1#                   ≈⟨ sym $ +-identityʳ (1# * 1#) ⟩
  (1# * 1#) + 0#            ≈⟨ sym $ +-identityʳ (1# * 1# + 0#) ⟩
  ((1# * 1#) + 0#) + 0#     ≡⟨⟩
  C 0 0 × (x ^ 0 * 1#) + 0# ≡⟨⟩
  sumₜ-syntax 1 (λ kF → let k = toℕ kF in C 0 k × (x ^ k * y ^ (0 ∸ k))) ∎
theorem x y (suc n) = begin
  (x + y) ^ suc n       ≡⟨⟩
  (x + y) * (x + y) ^ n ≈⟨ *-congˡ $ theorem x y n ⟩
  (x + y) * sumₜ-syntax (suc n) (λ kF → let k = toℕ kF in C n k × (x ^ k * y ^ (n ∸ k)))
    ≈⟨ {!   !} ⟩
  sumₜ-syntax (2 ℕ.+ n) (λ kF → let k = toℕ kF in C (suc n) k × (x ^ k * y ^ (suc n ∸ k))) ∎
-}
