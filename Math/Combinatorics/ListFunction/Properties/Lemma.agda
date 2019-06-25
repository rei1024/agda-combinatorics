------------------------------------------------------------------------
-- Lemmas
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --exact-split #-}

module Math.Combinatorics.ListFunction.Properties.Lemma where

open import Data.List hiding (_∷ʳ_)
open import Data.List.Relation.Binary.Sublist.Propositional using (_⊆_; []; _∷_; _∷ʳ_)

module _ {a} {A : Set a} where
  []⊆xs : ∀ (xs : List A) → [] ⊆ xs
  []⊆xs []       = []
  []⊆xs (x ∷ xs) = x ∷ʳ []⊆xs xs
