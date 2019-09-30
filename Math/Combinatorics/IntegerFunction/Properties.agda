------------------------------------------------------------------------
-- Properties of combinatorial functions on integers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --exact-split #-}

module Math.Combinatorics.IntegerFunction.Properties where

open import Data.Nat as ℕ hiding (_*_; _+_; _≤_; _<_)
import Data.Nat.Properties as ℕₚ
open import Data.Integer
import Data.Integer.Properties as ℤₚ
open import Relation.Binary.PropositionalEquality
open import Function.Core

import Math.Combinatorics.Function as ℕF
import Math.Combinatorics.Function.Properties as ℕFₚ
open import Math.Combinatorics.IntegerFunction

P[n,0]≡1 : ∀ n → P n 0 ≡ (+ 1)
P[n,0]≡1 (+ n)      = refl
P[n,0]≡1 (-[1+ n ]) = refl

P[n,1]≡n : ∀ n → P n 1 ≡ n
P[n,1]≡n (+ n)      = cong (+_) $ ℕFₚ.P[n,1]≡n n
P[n,1]≡n (-[1+ n ]) = begin-equality
  - (+ 1) * (+ (ℕ.suc n ℕ.* 1))
    ≡⟨ cong (λ v → - (+ 1) * (+ (ℕ.suc v))) $ ℕₚ.*-identityʳ n ⟩
  - (+ 1) * (+ (ℕ.suc n))
    ≡⟨ ℤₚ.-1*n≡-n (+ (ℕ.suc n)) ⟩
  - (+ ℕ.suc n)
    ∎
  where open ℤₚ.≤-Reasoning

module _ where
  open ℤₚ.≤-Reasoning
  0≤n∧n<k⇒P[n,k]≡0 : ∀ {n k} → 0ℤ ≤ n → n < + k → P n k ≡ + 0
  0≤n∧n<k⇒P[n,k]≡0 {+_ n} {k} 0≤n (+<+ n<k) = cong (+_) $ ℕFₚ.n<k⇒P[n,k]≡0 n<k

  {-
  P-split : ∀ (m : ℕ) (n : ℤ) (o : ℕ) → P ((+ m) + n) (m ℕ.+ o) ≡ P ((+ m) + n) m * P n o
  P-split m (+ n)      o = begin-equality
    + (ℕF.P (m ℕ.+ n) (m ℕ.+ o))
      ≡⟨ cong (+_) $ ℕFₚ.P-split m n o ⟩
    + (ℕF.P (m ℕ.+ n) m ℕ.* ℕF.P n o)
      ≡⟨ sym $ ℤₚ.pos-distrib-* (ℕF.P (m ℕ.+ n) m) (ℕF.P n o) ⟩
    + (ℕF.P (m ℕ.+ n)) m * + (ℕF.P n o)
      ∎
  P-split m (-[1+ n ]) o = {!   !}
 -}
