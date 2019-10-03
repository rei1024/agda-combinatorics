------------------------------------------------------------------------
-- Binomial theorem
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --exact-split #-}

module Math.BinomialTheorem.Nat where

-- agda-stdlib
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Function

-- agda-combinatorics
open import Math.Combinatorics.Function
open import Math.Combinatorics.Function.Properties

-- agda-misc
open import Math.NumberTheory.Summation.Nat
open import Math.NumberTheory.Summation.Nat.Properties

open ≤-Reasoning

theorem : ∀ x y n →
  (x + y) ^ n ≡ Σ[ k ≤ n ] (C n k * (x ^ k * y ^ (n ∸ k)))
theorem x y 0       = begin-equality
  C 0 0 * ((x ^ 0) * y ^ (0 ∸ 0))
    ≡⟨ sym $ Σ≤[f,0]≡f[0] (λ k → C 0 k * (x ^ k * y ^ (0 ∸ k))) ⟩
  Σ≤ (λ k → C 0 k * (x ^ k * y ^ (0 ∸ k))) 0
    ∎
theorem x y (suc n) = begin-equality
  (x + y) * (x + y) ^ n
    ≡⟨ cong ((x + y) *_) $ theorem x y n ⟩
  (x + y) * Σ[ k ≤ n ] (C n k * (x ^ k * y ^ (n ∸ k)))
    ≡⟨ *-distribʳ-+ (Σ[ k ≤ n ] (C n k * (x ^ k * y ^ (n ∸ k)))) x y ⟩
  x * Σ[ k ≤ n ] (C n k * (x ^ k * y ^ (n ∸ k))) + y * Σ[ k ≤ n ] (C n k * (x ^ k * y ^ (n ∸ k)))
    ≡⟨ {!sym $ cong₂ _+_ (Σ≤-*-commute ? n x) (Σ≤-*-commute ? n y)  !} ⟩
  Σ[ k ≤ n ] (x * (C n k * (x ^ k * y ^ (n ∸ k)))) + Σ[ k ≤ n ] (y * (C n k * (x ^ k * y ^ (n ∸ k))))
    ≡⟨ {!   !} ⟩
  Σ≤ (λ k → C (suc n) k * (x ^ k * y ^ (suc n ∸ k))) n + (C (suc n) (suc n) * (x ^ suc n * y ^ (suc n ∸ suc n)))
    ≡⟨⟩
  Σ≤ (λ k → C (suc n) k * (x ^ k * y ^ (suc n ∸ k))) (suc n)
    ∎
