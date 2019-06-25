------------------------------------------------------------------------
-- Properties of functions
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --exact-split #-}

module Math.Combinatorics.ListFunction.Properties where

-- stdlib
open import Data.List
import Data.List.Properties as Lₚ
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as Allₚ
open import Data.Nat
open import Function
open import Relation.Binary.PropositionalEquality

-- agda-combinatorics
open import Math.Combinatorics.Function
open import Math.Combinatorics.Function.Properties
open import Math.Combinatorics.ListFunction

------------------------------------------------------------------------
-- Properties of `applyEach`

module _ {a} {A : Set a} where
  open ≡-Reasoning
  length-applyEach : ∀ (f : A → A) (xs : List A) →
                     length (applyEach f xs) ≡ length xs
  length-applyEach f []       = refl
  length-applyEach f (x ∷ xs) = begin
    1 + length (map (x ∷_) (applyEach f xs)) ≡⟨ cong suc $ Lₚ.length-map (x ∷_) (applyEach f xs ) ⟩
    1 + length (applyEach f xs)              ≡⟨ cong suc $ length-applyEach f xs ⟩
    1 + length xs                            ∎

  All-length-applyEach : ∀ (f : A → A) (xs : List A) →
                         All (λ ys → length ys ≡ length xs) (applyEach f xs)
  All-length-applyEach f []       = []
  All-length-applyEach f (x ∷ xs) =
    refl ∷ (Allₚ.map⁺ $ All.map (cong suc) $ All-length-applyEach f xs)

------------------------------------------------------------------------
-- Properties of `combinations`

module _ {a} {A : Set a} where
  open ≡-Reasoning
  length-combinations : ∀ (k : ℕ) (xs : List A) →
                        length (combinations k xs) ≡ C (length xs) k
  length-combinations 0       xs       = refl
  length-combinations (suc k) []       = sym $ C[0,1+k]≡0 k
  length-combinations (suc k) (x ∷ xs) = begin
    length (map (x ∷_) (combinations k xs) ++ combinations (suc k) xs)
      ≡⟨ Lₚ.length-++ (map (x ∷_) (combinations k xs)) ⟩
    length (map (x ∷_) (combinations k xs)) + length (combinations (suc k) xs)
      ≡⟨ cong₂ _+_ (Lₚ.length-map (x ∷_) (combinations k xs)) refl ⟩
    length (combinations k xs) + length (combinations (suc k) xs)
      ≡⟨ cong₂ _+_ (length-combinations k xs) (length-combinations (suc k) xs) ⟩
    C (length xs) k + C (length xs) (suc k)
      ≡⟨ sym $ C[1+n,1+k]≡C[n,k]+C[n,1+k] (length xs) k ⟩
    C (length (x ∷ xs)) (suc k)
      ∎

  -- combinations-⊆⇒∈ : xs ⊆ ys → xs ∈ combinations (length xs) ys
  -- combinations-∈⇒⊆ : xs ∈ combinations (length xs) ys → xs ⊆ ys
  -- combinations-⊆⇔∈ : xs ⊆ ys ⇔ xs ∈ combinations (length xs) ys
  -- unique-combinations : Unique xs → Unique (combinations k xs)
