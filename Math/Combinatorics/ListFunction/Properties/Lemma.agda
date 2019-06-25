------------------------------------------------------------------------
-- Lemmas
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --exact-split #-}

module Math.Combinatorics.ListFunction.Properties.Lemma where

open import Data.List hiding (_∷ʳ_)
import Data.List.Properties as Lₚ
open import Data.List.Relation.Binary.Sublist.Propositional using (_⊆_; []; _∷_; _∷ʳ_)
open import Function
open import Relation.Binary.PropositionalEquality

module _ {a} {A : Set a} where
  []⊆xs : ∀ (xs : List A) → [] ⊆ xs
  []⊆xs []       = []
  []⊆xs (x ∷ xs) = x ∷ʳ []⊆xs xs

module _ {a b} {A : Set a} {B : Set b} where
  lemma₁ : ∀ (f : A → B) (x : A) (xss : List (List A)) →
    map (λ ys → f x ∷ ys) (map (map f) xss) ≡ map (map f) (map (λ ys → x ∷ ys) xss)
  lemma₁ f x xss = begin
    map (λ ys → f x ∷ ys) (map (map f) xss) ≡⟨ sym $ Lₚ.map-compose xss ⟩
    map (λ ys → f x ∷ map f ys) xss         ≡⟨ Lₚ.map-compose xss ⟩
    map (map f) (map (λ ys → x ∷ ys) xss)   ∎
    where open ≡-Reasoning
