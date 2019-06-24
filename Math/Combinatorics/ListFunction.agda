------------------------------------------------------------------------
-- Definitions of functions that generate list
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --exact-split #-}

module Math.Combinatorics.ListFunction where

open import Data.List
open import Data.List.NonEmpty as NE using (List⁺)
open import Data.Nat
open import Data.Product as Prod using (_×_; _,_)
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])

module _ {a} {A : Set a} where
  -- applyEach (_+ 10) (upTo 3)
  -- >>> (10 ∷ 1 ∷ 2 ∷ []) ∷ (0 ∷ 11 ∷ 2 ∷ []) ∷ (0 ∷ 1 ∷ 12 ∷ []) ∷ []
  applyEach : (A → A) → List A → List (List A)
  applyEach f [] = []
  applyEach f (x ∷ xs) = (f x ∷ xs) ∷ map (x ∷_) (applyEach f xs)

module _ {a} {A : Set a} where
  -- combinations
  -- combinations 2 (upTo 3)
  -- >>> (0 ∷ 1 ∷ []) ∷ (0 ∷ 2 ∷ []) ∷
  -- >>> (0 ∷ 3 ∷ []) ∷ (1 ∷ 2 ∷ []) ∷ (1 ∷ 3 ∷ []) ∷ (2 ∷ 3 ∷ []) ∷ []
  combinations : ℕ → List A → List (List A)
  combinations 0       xs       = [ [] ]
  combinations (suc k) []       = []
  combinations (suc k) (x ∷ xs) =
    map (x ∷_) (combinations k xs) ++ combinations (suc k) xs

  -- combinationsWithComplement 2 (upTo 2)
  -- >>> (0 ∷ 1 ∷ [] , 2 ∷ []) ∷
  -- >>> (0 ∷ 2 ∷ [] , 1 ∷ []) ∷ (1 ∷ 2 ∷ [] , 0 ∷ []) ∷ []
  combinationsWithComplement : ℕ → List A → List (List A × List A)
  combinationsWithComplement 0       xs       = [ [] , xs ]
  combinationsWithComplement (suc k) []       = []
  combinationsWithComplement (suc k) (x ∷ xs) =
    map (Prod.map₁ (x ∷_)) (combinationsWithComplement k xs) ++
    map (Prod.map₂ (x ∷_)) (combinationsWithComplement (suc k) xs)

  -- splits₂ (upTo 3)
  -- >>> ([] , 0 ∷ 1 ∷ 2 ∷ []) List⁺.∷
  -- >>> (0 ∷ [] , 1 ∷ 2 ∷ []) ∷
  -- >>> (0 ∷ 1 ∷ [] , 2 ∷ []) ∷ (0 ∷ 1 ∷ 2 ∷ [] , []) ∷ []
  splits₂ : List A → List⁺ (List A × List A)
  splits₂ []       = ([] , []) NE.∷ []
  splits₂ (x ∷ xs) = ([] , x ∷ xs) NE.∷⁺ NE.map (Prod.map₁ (x ∷_)) (splits₂ xs)

  splits : ℕ → List A → List (List (List A))
  splits 0             xs = []
  splits 1             xs = [ xs ∷ [] ]
  splits (suc (suc k)) xs = concatMap f (splits (suc k) xs)
    where
    f : List (List A) → List (List (List A))
    f []         = []
    f (ys ∷ yss) = NE.toList $
      NE.map (λ { (as , bs) → as ∷ bs ∷ yss }) (splits₂ ys)

  splits⁺₂Acc : A → List A → List (List⁺ A × List⁺ A)
  splits⁺₂Acc x []       = []
  splits⁺₂Acc x (y ∷ xs) = (x NE.∷ [] , y NE.∷ xs) ∷
                           map (Prod.map₁ (x NE.∷⁺_)) (splits⁺₂Acc y xs)

  -- splits⁺₂ (nats⁺ 3)
  -- >>> (0 List⁺.∷ [] , 1 List⁺.∷ 2 ∷ 3 ∷ []) ∷
  -- >>> (0 List⁺.∷ 1 ∷ [] , 2 List⁺.∷ 3 ∷ []) ∷
  -- >>> (0 List⁺.∷ 1 ∷ 2 ∷ [] , 3 List⁺.∷ []) ∷ []
  splits⁺₂ : List⁺ A → List (List⁺ A × List⁺ A)
  splits⁺₂ (x NE.∷ xs) = splits⁺₂Acc x xs

  splits⁺ : ℕ → List⁺ A → List (List (List⁺ A))
  splits⁺ 0             xs = []
  splits⁺ 1             xs = [ xs ∷ [] ]
  splits⁺ (suc (suc k)) xs = concatMap f (splits⁺ (suc k) xs)
    where
    f : List (List⁺ A) → List (List (List⁺ A))
    f []         = []
    f (ys ∷ yss) =
      map (λ { (as , bs) → as ∷ bs ∷ yss }) (splits⁺₂ ys)

  splits⁺AllAcc : A → List A → List⁺ (List⁺ (List⁺ A))
  splits⁺AllAcc x []       = ((x NE.∷ []) NE.∷ []) NE.∷ []
  splits⁺AllAcc x (y ∷ xs) =
    NE.map (λ zs → (x NE.∷ []) NE.∷⁺ zs) yss NE.⁺++⁺
    NE.map (λ { (z NE.∷ zs) → (x NE.∷⁺ z) NE.∷ zs} ) yss
    where yss = splits⁺AllAcc y xs

  splits⁺All : List⁺ A → List⁺ (List⁺ (List⁺ A))
  splits⁺All (x NE.∷ xs) = splits⁺AllAcc x xs

  -- Generalization of combinationsWithComplement
  -- partitions 2 (upTo 3)
  -- >>> ((0 ∷ []) ∷ (1 ∷ 2 ∷ []) ∷ []) ∷
  -- >>> ((0 ∷ 1 ∷ []) ∷ (2 ∷ []) ∷ []) ∷
  -- >>> ((1 ∷ []) ∷ (0 ∷ 2 ∷ []) ∷ []) ∷ []
  partitions : ℕ → List A → List (List (List A))
  partitions 0       []       = [ [] ]
  partitions 0       (x ∷ xs) = []
  partitions (suc k) []       = []
  partitions (suc k) (x ∷ xs) =
    map ([ x ] ∷_) (partitions k xs) ++
    concatMap (applyEach (x ∷_)) (partitions (suc k) xs)

  partitionsAll : List A → List (List (List A))
  partitionsAll []       = [ [] ]
  partitionsAll (x ∷ xs) =
    map ([ x ] ∷_) yss ++ concatMap (applyEach (x ∷_)) yss
    where yss = partitionsAll xs
