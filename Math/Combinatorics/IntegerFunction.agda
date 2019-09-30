------------------------------------------------------------------------
-- Definitions of combinatorial functions on integers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --exact-split #-}

module Math.Combinatorics.IntegerFunction where

open import Data.Nat hiding (_*_)
open import Data.Integer

import Math.Combinatorics.Function as ℕF

[-1]^_ : ℕ → ℤ
[-1]^ 0               = + 1
[-1]^ 1               = - (+ 1)
[-1]^ ℕ.suc (ℕ.suc n) = [-1]^ n

P : ℤ → ℕ → ℤ
P (+ n)      k = + (ℕF.P n k)
P (-[1+ n ]) k = [-1]^ k * + ℕF.Poch (ℕ.suc n) k
