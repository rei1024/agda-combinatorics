------------------------------------------------------------------------
-- Definitions of functions that generate list or vector
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --exact-split #-}

module Math.Combinatorics.VecFunction where

open import Data.List
open import Data.List.NonEmpty as NE using (List⁺)
open import Data.Nat
import Data.Nat.Properties as ℕₚ
open import Data.Product as Prod using (_×_; _,_)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])

import Math.Combinatorics.ListFunction as ListFun

module _ {a} {A : Set a} where

  applyEach : ∀ {n} → (A → A) → Vec A n → Vec (Vec A n) n
  applyEach f []       = []
  applyEach f (x ∷ xs) = (f x ∷ xs) ∷ Vec.map (x ∷_) (applyEach f xs)

module _ {a} {A : Set a} where
  -- combinations
  combinations : ∀ k → List A → List (Vec A k)
  combinations 0       xs       = [ [] ]
  combinations (suc k) []       = []
  combinations (suc k) (x ∷ xs) =
    map (x ∷_) (combinations k xs) ++ combinations (suc k) xs

  combinationsWithComplement : ∀ m {n} → Vec A (m + n) →
                               List (Vec A m × Vec A n)
  combinationsWithComplement 0                 xs       = [ [] , xs ]
  combinationsWithComplement m@(suc _) {0}     xs       =
    [ subst (Vec A) (ℕₚ.+-identityʳ m) xs , [] ]
  combinationsWithComplement (suc m)   {suc n} (x ∷ xs) =
    map (Prod.map₁ (x ∷_)) (combinationsWithComplement m xs) ++
    map (Prod.map₂ (x ∷_)) (combinationsWithComplement (suc m) xs′)
      where xs′ = subst (Vec A) (ℕₚ.+-suc m n) xs

  splits₂ : ∀ {n} → Vec A n → Vec (List A × List A) (1 + n)
  splits₂ []           = ([] , []) ∷ []
  splits₂ xxs@(x ∷ xs) = ([] , Vec.toList xxs) ∷
                         Vec.map (Prod.map₁ (x ∷_)) (splits₂ xs)

  splits : ∀ k → List A → List (Vec (List A) k)
  splits 0             xs = []
  splits 1             xs = [ xs ∷ [] ]
  splits (suc (suc k)) xs = concatMap f (splits (suc k) xs)
    where
    f : Vec (List A) (suc k) → List (Vec (List A) (suc (suc k)))
    f (ys ∷ yss) =
      map (λ { (as , bs) → as ∷ bs ∷ yss }) (NE.toList (ListFun.splits₂ ys))

  splits⁺₂ : ∀ {n} → Vec A (1 + n) → Vec (List⁺ A × List⁺ A) n
  splits⁺₂ (x ∷ [])     = []
  splits⁺₂ (x ∷ y ∷ xs) =
    (x NE.∷ [] , y NE.∷ Vec.toList xs) ∷
    Vec.map (Prod.map₁ (x NE.∷⁺_)) (splits⁺₂ (y ∷ xs))

  splits⁺ : ∀ k → List⁺ A → List (Vec (List⁺ A) k)
  splits⁺ 0             xs = []
  splits⁺ 1             xs = [ xs ∷ [] ]
  splits⁺ (suc (suc k)) xs = concatMap f (splits⁺ (suc k) xs)
    where
    f : Vec (List⁺ A) (suc k) → List (Vec (List⁺ A) (suc (suc k)))
    f (ys ∷ yss) =
      map (λ { (as , bs) → as ∷ bs ∷ yss }) (ListFun.splits⁺₂ ys)

  partitions : ∀ k → List A → List (Vec (List A) k)
  partitions 0       []       = [ [] ]
  partitions 0       (x ∷ xs) = []
  partitions (suc k) []       = []
  partitions (suc k) (x ∷ xs) =
    map ([ x ] ∷_) (partitions k xs) ++
    concatMap (Vec.toList ∘ applyEach (x ∷_)) (partitions (suc k) xs)
