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
open import Data.List
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
-- A000142

_! : ℕ → ℕ
0       ! = 1
(suc n) ! = suc n * n !

------------------------------------------------------------------------
-- Permutation, Falling factorial
-- P n k = n * (n - 1) * ... * (n - k + 1)  (k terms)

P : ℕ → ℕ → ℕ
P n       0       = 1
P 0       (suc k) = 0
P (suc n) (suc k) = suc n * P n k

------------------------------------------------------------------------
-- Combination, Binomial coefficient
-- C n k = P n k / k !

C : ℕ → ℕ → ℕ
C n       0       = 1
C 0       (suc k) = 0
C (suc n) (suc k) = (C n k * suc n) / suc k

-- recursive definition
CRec : ℕ → ℕ → ℕ
CRec n       0       = 1
CRec 0       (suc k) = 0
CRec (suc n) (suc k) = CRec n k + CRec n (suc k)

------------------------------------------------------------------------
-- Double factorial
-- A006882

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
L (suc n@(suc _)) (suc k)       = (n + suc k) * L n (suc k) + L n k

------------------------------------------------------------------------
-- Bell number
-- A000110

B : ℕ → ℕ
B n = sumₜ-syntax (suc n) (λ i → S2 n (toℕ i))

------------------------------------------------------------------------
-- Rising factorial
-- Pochhammer symbol
-- Poch n k = n * (n + 1) * ... * (n + k - 1) (k terms)

Poch : ℕ → ℕ → ℕ
Poch n 0       = 1
Poch n (suc k) = n * Poch (suc n) k

------------------------------------------------------------------------
-- Central binomial coefficient
-- A000984

CB : ℕ → ℕ
CB n = C (2 * n) n

------------------------------------------------------------------------
-- Catalan number
-- A000108

Catalan : ℕ → ℕ
Catalan n = CB n / suc n

------------------------------------------------------------------------
-- Eulerian number

A : ℕ → ℕ → ℕ
A 0       0       = 1
A 0       (suc m) = 0
A (suc n) 0       = 1
A (suc n) (suc m) = (n ∸ m) * A n m + suc (suc m) * A n (suc m)

------------------------------------------------------------------------
-- Eulerian numbers of the second kind

E2 : ℕ → ℕ → ℕ
E2 0       0       = 1
E2 0       (suc m) = 0
E2 (suc n) 0       = 1
E2 (suc n) (suc m) =
  (2 * suc n ∸ suc m ∸ 1) * E2 n m + suc (suc m) * E2 n (suc m)

------------------------------------------------------------------------
-- Multinomial coefficient
-- MC xs = (sum xs) ! / product (map (_!) xs)

Multinomial : List ℕ → ℕ
Multinomial []                   = 1
Multinomial (x ∷ [])             = 1
Multinomial xxs@(x ∷ xs@(_ ∷ _)) = C (sum xxs) x * Multinomial xs

------------------------------------------------------------------------
-- Pascal's triangle

gpascal : ∀ {a} {A : Set a} → (A → A → A) → A → A → ℕ → List A
gpascal f v0 v1 0       = v1 ∷ []
gpascal f v0 v1 (suc n) =
  let ps = gpascal f v0 v1 n in zipWith f (v0 ∷ ps) (ps ∷ʳ v0)

pascal : ℕ → List ℕ
pascal = gpascal _+_ 0 1
