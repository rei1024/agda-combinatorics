------------------------------------------------------------------------
-- Properties of combinatorial functions on integers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --exact-split #-}

module Math.Combinatorics.IntegerFunction.Properties where

open import Data.Nat as ℕ hiding (_*_; _+_; _≤_; _<_)
import Data.Nat.Properties as ℕₚ
open import Data.Integer as ℤ
import Data.Integer.Properties as ℤₚ
open import Relation.Binary.PropositionalEquality
open import Function.Core

import Math.Combinatorics.Function as ℕF
import Math.Combinatorics.Function.Properties as ℕFₚ
open import Math.Combinatorics.IntegerFunction
import Math.Combinatorics.IntegerFunction.Properties.Lemma as Lemma

------------------------------------------------------------------------
-- Properties of [-1]^_

[-1]^[1+n]≡-1*[-1]^n : ∀ n → [-1]^ (ℕ.suc n) ≡ -1ℤ * [-1]^ n
[-1]^[1+n]≡-1*[-1]^n zero              = refl
[-1]^[1+n]≡-1*[-1]^n (ℕ.suc zero)      = refl
[-1]^[1+n]≡-1*[-1]^n (ℕ.suc (ℕ.suc n)) = [-1]^[1+n]≡-1*[-1]^n n

[-1]^[m+n]≡[-1]^m*[-1]^n : ∀ m n → [-1]^ (m ℕ.+ n) ≡ [-1]^ m * [-1]^ n
[-1]^[m+n]≡[-1]^m*[-1]^n zero              n = sym $ ℤₚ.*-identityˡ $ [-1]^ n
[-1]^[m+n]≡[-1]^m*[-1]^n (ℕ.suc zero)      n = [-1]^[1+n]≡-1*[-1]^n n
[-1]^[m+n]≡[-1]^m*[-1]^n (ℕ.suc (ℕ.suc m)) n = [-1]^[m+n]≡[-1]^m*[-1]^n m n

-- TODO: [-1]^n≡-1∨[-1]^n≡1

[-1]^[2*n]≡1 : ∀ n → [-1]^ (2 ℕ.* n) ≡ + 1
[-1]^[2*n]≡1 zero = refl
[-1]^[2*n]≡1 (ℕ.suc n) = begin-equality
  [-1]^ (2 ℕ.* ℕ.suc n) ≡⟨ cong ([-1]^_) $ ℕₚ.*-distribˡ-+ 2 1 n ⟩
  [-1]^ (2 ℕ.+ 2 ℕ.* n) ≡⟨⟩
  [-1]^ (2 ℕ.* n)       ≡⟨ [-1]^[2*n]≡1 n ⟩
  + 1                   ∎
  where open ℤₚ.≤-Reasoning

[-1]^[1+2*n]≡-1 : ∀ n → [-1]^ (1 ℕ.+ 2 ℕ.* n) ≡ -1ℤ
[-1]^[1+2*n]≡-1 n = begin-equality
  [-1]^ (1 ℕ.+ 2 ℕ.* n) ≡⟨ [-1]^[1+n]≡-1*[-1]^n (2 ℕ.* n) ⟩
  -1ℤ * [-1]^ (2 ℕ.* n) ≡⟨ cong (-1ℤ *_) $ [-1]^[2*n]≡1 n ⟩
  -1ℤ * + 1             ∎
  where open ℤₚ.≤-Reasoning

------------------------------------------------------------------------
-- Properties of permutation

P[n,0]≡1 : ∀ n → P n 0 ≡ (+ 1)
P[n,0]≡1 (+ n)      = refl
P[n,0]≡1 (-[1+ n ]) = refl

P[n,1]≡n : ∀ n → P n 1 ≡ n
P[n,1]≡n (+ n)      = cong (+_) $ ℕFₚ.P[n,1]≡n n
P[n,1]≡n (-[1+ n ]) = begin-equality
  -1ℤ * + ℕF.Poch (ℕ.suc n) 1
    ≡⟨ cong (λ v → -1ℤ * + v) $ ℕFₚ.Poch[n,1]≡n (ℕ.suc n) ⟩
  -1ℤ * (+ (ℕ.suc n))
    ≡⟨ ℤₚ.-1*n≡-n (+ (ℕ.suc n)) ⟩
  - (+ ℕ.suc n)
    ∎
  where open ℤₚ.≤-Reasoning

module _ where
  open ℤₚ.≤-Reasoning

  P[-n,k]≡[-1]^k*ℕPoch[n,k] : ∀ n k → P (- (+ n)) k ≡ [-1]^ k * + ℕF.Poch n k
  P[-n,k]≡[-1]^k*ℕPoch[n,k] zero      zero      = refl
  P[-n,k]≡[-1]^k*ℕPoch[n,k] zero      (ℕ.suc k) = sym $ ℤₚ.*-zeroʳ ([-1]^ ℕ.suc k)
  P[-n,k]≡[-1]^k*ℕPoch[n,k] (ℕ.suc n) k         = refl

  P[-n,2*k]≡ℕPoch[n,2*k] : ∀ n k → P (- (+ n)) (2 ℕ.* k) ≡ + ℕF.Poch n (2 ℕ.* k)
  P[-n,2*k]≡ℕPoch[n,2*k] n k = begin-equality
    P (- (+ n)) (2 ℕ.* k) ≡⟨ P[-n,k]≡[-1]^k*ℕPoch[n,k] n (2 ℕ.* k) ⟩
    [-1]^ (2 ℕ.* k) * p   ≡⟨ cong (_* p) $ [-1]^[2*n]≡1 k ⟩
    1ℤ * p                ≡⟨ ℤₚ.*-identityˡ p ⟩
    p                     ∎
    where p = + ℕF.Poch n (2 ℕ.* k)

  0≤n∧n<k⇒P[n,k]≡0 : ∀ {n k} → 0ℤ ≤ n → n < + k → P n k ≡ + 0
  0≤n∧n<k⇒P[n,k]≡0 {+_ n} {k} 0≤n (+<+ n<k) = cong (+_) $ ℕFₚ.n<k⇒P[n,k]≡0 n<k

  P[1+n,1+k]≡[1+n]*P[n,k] : ∀ n k → P (ℤ.suc n) (ℕ.suc k) ≡ ℤ.suc n * P n k
  P[1+n,1+k]≡[1+n]*P[n,k] (+ n)            k = begin-equality
    + (ℕ.suc n ℕ.* ℕF.P n k) ≡⟨ sym $ ℤₚ.pos-distrib-* (ℕ.suc n) (ℕF.P n k) ⟩
    + (ℕ.suc n) * + ℕF.P n k ≡⟨⟩
    ℤ.suc (+ n) * + ℕF.P n k ∎
  P[1+n,1+k]≡[1+n]*P[n,k] (-[1+ 0 ])       k = refl
  P[1+n,1+k]≡[1+n]*P[n,k] (-[1+ ℕ.suc n ]) k = begin-equality
    [-1]^ (ℕ.suc k) * + ℕF.Poch (ℕ.suc n) (ℕ.suc k)
      ≡⟨⟩
    [-1]^ (ℕ.suc k) * + (ℕ.suc n ℕ.* p)
      ≡⟨ cong (_* + (ℕ.suc n ℕ.* p)) $ [-1]^[1+n]≡-1*[-1]^n k ⟩
    -1ℤ * [-1]^ k * + (ℕ.suc n ℕ.* p)
      ≡⟨ sym $ cong (-1ℤ * [-1]^ k *_) $ ℤₚ.pos-distrib-* (ℕ.suc n) p ⟩
    -1ℤ * [-1]^ k * (+ ℕ.suc n * + p)
      ≡⟨ Lemma.lemma₁ -1ℤ ([-1]^ k) (+ ℕ.suc n) (+ p) ⟩
    -1ℤ * + ℕ.suc n * ([-1]^ k * + p)
      ≡⟨ cong (_* ([-1]^ k * + p)) $ ℤₚ.-1*n≡-n (+ ℕ.suc n) ⟩
    -[1+ n ] * ([-1]^ k * + p)
      ∎
    where p = ℕF.Poch (ℕ.suc (ℕ.suc n)) k

  P[n,1+k]≡n*P[n-1,k] : ∀ n k → P n (ℕ.suc k) ≡ n * P (n - 1ℤ) k
  P[n,1+k]≡n*P[n-1,k] n k = begin-equality
    P n (ℕ.suc k)                  ≡⟨ cong (λ v → P v (ℕ.suc k)) $ Lemma.lemma₂ n ⟩
    P (1ℤ + (n - 1ℤ)) (ℕ.suc k)    ≡⟨ P[1+n,1+k]≡[1+n]*P[n,k] (n - 1ℤ) k ⟩
    (1ℤ + (n - 1ℤ)) * P (n - 1ℤ) k ≡⟨ sym $ cong (_* P (n - 1ℤ) k) $ Lemma.lemma₂ n ⟩
    n * P (n - 1ℤ) k               ∎

  P-split : ∀ (m : ℕ) (n : ℤ) (o : ℕ) → P ((+ m) + n) (m ℕ.+ o) ≡ P ((+ m) + n) m * P n o
  P-split zero      n o = begin-equality
    P (0ℤ + n) o         ≡⟨ cong (λ v → P v o) $ ℤₚ.+-identityˡ n ⟩
    P n o                ≡⟨ sym $ ℤₚ.*-identityˡ (P n o) ⟩
    1ℤ * P n o           ≡⟨ sym $ cong (_* P n o) $ P[n,0]≡1 (0ℤ + n) ⟩
    P (0ℤ + n) 0 * P n o ∎
  P-split (ℕ.suc m) n o = begin-equality
    P (ℤ.suc (+ m) + n) (ℕ.suc (m ℕ.+ o))
      ≡⟨ cong (λ v → P v (ℕ.suc (m ℕ.+ o))) $ ℤₚ.+-assoc 1ℤ (+ m) n ⟩
    P (ℤ.suc (+ m + n)) (ℕ.suc (m ℕ.+ o))
      ≡⟨ P[1+n,1+k]≡[1+n]*P[n,k] (+ m + n) (m ℕ.+ o) ⟩
    ℤ.suc (+ m + n) * P (+ m + n) (m ℕ.+ o)
      ≡⟨ cong (ℤ.suc (+ m + n) *_) $ P-split m n o ⟩
    ℤ.suc (+ m + n) * (P (+ m + n) m * P n o)
      ≡⟨ sym $ ℤₚ.*-assoc (ℤ.suc (+ m + n)) (P (+ m + n) m) (P n o) ⟩
    ℤ.suc (+ m + n) * P (+ m + n) m * P n o
      ≡⟨ sym $ cong (_* P n o) $ P[1+n,1+k]≡[1+n]*P[n,k] (+ m + n) m ⟩
    P (ℤ.suc (+ m + n)) (ℕ.suc m) * P n o
      ≡⟨ sym $ cong (λ v → P v (ℕ.suc m) * P n o) $ ℤₚ.+-assoc 1ℤ (+ m) n ⟩
    P (+ (ℕ.suc m) + n) (ℕ.suc m) * P n o
      ∎

  P-split-minus : ∀ m n o → P m (n ℕ.+ o) ≡ P m n * P (m - + n) o
  P-split-minus m n o = begin-equality
    P m (n ℕ.+ o)         ≡⟨ cong (λ v → P v (n ℕ.+ o)) m≡n+p ⟩
    P (+ n + p) (n ℕ.+ o) ≡⟨ P-split n p o ⟩
    P (+ n + p) n * P p o ≡⟨ sym $ cong (λ v → P v n * P p o) $ m≡n+p ⟩
    P m n * P (m - + n) o ∎
    where
    p = m - + n
    m≡n+p : m ≡ + n + (m - + n)
    m≡n+p = Lemma.lemma₃ m (+ n)
