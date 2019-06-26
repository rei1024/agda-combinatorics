------------------------------------------------------------------------
-- Definitions of combinatorial functions
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --exact-split #-}

module Math.Combinatorics.Function where

import Algebra.Operations.CommutativeMonoid as CommutativeMonoidOperations
open import Data.Fin using (toℕ)
open import Data.Nat
open import Data.Nat.DivMod
open import Data.Nat.Properties using (+-0-commutativeMonoid)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Nullary.Decidable using (False; fromWitnessFalse)

open CommutativeMonoidOperations +-0-commutativeMonoid

infix 10 _! _!!

------------------------------------------------------------------------
-- Factorial
-- n ! = n * (n - 1) * ... * 2 * 1

_! : ℕ → ℕ
0       ! = 1
(suc n) ! = suc n * n !

------------------------------------------------------------------------
-- Permutation
-- P n k = n * (n - 1) * ... * (n - k + 1)  (k terms)

P : ℕ → ℕ → ℕ
P n       0       = 1
P 0       (suc k) = 0
P (suc n) (suc k) = suc n * P n k

------------------------------------------------------------------------
-- Properties of _!

private
  zero-product : ∀ m n → m * n ≡ 0 → m ≡ 0 ⊎ n ≡ 0
  zero-product 0       n m*n≡0 = inj₁ refl
  zero-product (suc m) 0 m*n≡0 = inj₂ refl

-- factorial never be 0
n!≢0 : ∀ n → (n !) ≢ 0
n!≢0 0      ()
n!≢0 (suc n) [1+n]!≡0 with zero-product (suc n) (n !) [1+n]!≡0
... | inj₂ n!≡0 = n!≢0 n n!≡0

False[n!≟0] : ∀ n → False (n ! ≟ 0)
False[n!≟0] n = fromWitnessFalse (n!≢0 n)

------------------------------------------------------------------------
-- Combination, Binomial coefficient
-- C n k = P n k / k !

C : ℕ → ℕ → ℕ
C n k = (P n k div k !) {False[n!≟0] k}

-- recursive definition
CRec : ℕ → ℕ → ℕ
CRec n       0       = 1
CRec 0       (suc k) = 0
CRec (suc n) (suc k) = CRec n k + CRec n (suc k)

------------------------------------------------------------------------
-- Double factorial

_!! : ℕ → ℕ
0           !! = 1
1           !! = 1
suc (suc n) !! = suc (suc n) * n !!

------------------------------------------------------------------------
-- unsigned Stirling numbers of the first kind

S1 : ℕ → ℕ → ℕ
S1 0       0       = 1
S1 0       (suc k) = 0
S1 (suc n) 0       = 0
S1 (suc n) (suc k) = n * S1 n (suc k) + S1 n k

------------------------------------------------------------------------
-- Stirling numbers of the second kind

S2 : ℕ → ℕ → ℕ
S2 0       0       = 1
S2 0       (suc k) = 0
S2 (suc n) 0       = 0
S2 (suc n) (suc k) = suc k * S2 n (suc k) + S2 n k

------------------------------------------------------------------------
-- Lah number

L : ℕ → ℕ → ℕ
L n               0             = 0
L 0               (suc k)       = 0
L 1               1             = 1
L 1               (suc (suc k)) = 0
L (suc n@(suc _)) (suc k)       =
  (n + suc k) * L n (suc k) + L n k

------------------------------------------------------------------------
-- Bell number

B : ℕ → ℕ
B n = sumₜ-syntax (suc n) (λ i → S2 n (toℕ i))

------------------------------------------------------------------------
-- Rising factorial
-- Pochhammer symbol
-- Poch n k = n * (n + 1) * ... * (n + k - 1) (k terms)

Poch : ℕ → ℕ → ℕ
Poch n 0       = 1
Poch n (suc k) = n * Poch (suc n) k
