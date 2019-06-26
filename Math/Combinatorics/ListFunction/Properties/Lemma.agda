------------------------------------------------------------------------
-- Lemmas
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --exact-split #-}

module Math.Combinatorics.ListFunction.Properties.Lemma where

open import Data.List hiding (_∷ʳ_)
import Data.List.Properties as Lₚ
open import Data.List.Relation.Binary.Sublist.Propositional using (_⊆_; []; _∷_; _∷ʳ_)
open import Data.Product as Prod using (proj₁; proj₂; _×_; _,_)
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

module _ {a b c} {A : Set a} {B : Set b} {C : Set c} where
  proj₁-map₁ : ∀ (f : A → B) (t : A × C) → proj₁ (Prod.map₁ f t) ≡ f (Prod.proj₁ t)
  proj₁-map₁ _ _ = refl

module _ {a b} {A : Set a} {B : Set b} where
  proj₁-map₂ : ∀ (f : B → B) (t : A × B) → proj₁ (Prod.map₂ f t) ≡ proj₁ t
  proj₁-map₂ _ _ = refl

  proj₁′ : A × B → A
  proj₁′ = proj₁

  {-
  map₂ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : A → Set c} →
         (∀ {x} → B x → C x) → Σ A B → Σ A C
  map₂ f = map id f
  -}
