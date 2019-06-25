------------------------------------------------------------------------
-- Properties of functions
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --exact-split #-}

module Math.Combinatorics.ListFunction.Properties where

-- stdlib
open import Data.List
import Data.List.Properties as Lₚ
open import Data.Nat
open import Function
open import Relation.Binary.PropositionalEquality

-- agda-combinatorics
open import Math.Combinatorics.ListFunction

module _ {a} {A : Set a} where
  length-applyEach : ∀ (f : A → A) (xs : List A) →
                     length (applyEach f xs) ≡ length xs
  length-applyEach f []       = refl
  length-applyEach f (x ∷ xs) = begin
    1 + length (map (x ∷_) (applyEach f xs)) ≡⟨ cong suc $ Lₚ.length-map (x ∷_) (applyEach f xs ) ⟩
    1 + length (applyEach f xs)              ≡⟨ cong suc $ length-applyEach f xs ⟩
    1 + length xs                            ∎
    where open ≡-Reasoning
