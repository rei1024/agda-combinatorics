------------------------------------------------------------------------
-- Properties of functions
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --exact-split #-}

module Math.Combinatorics.ListFunction.Properties where

-- stdlib
open import Data.List hiding (_∷ʳ_)
import Data.List.Properties as Lₚ
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Membership.Propositional.Properties as ∈ₚ
open import Data.List.Relation.Binary.Sublist.Propositional using (_⊆_; []; _∷_; _∷ʳ_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as Allₚ
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Data.Nat
open import Data.Product using (_×_; _,_; ∃)
open import Data.Sum using (inj₁; inj₂)
open import Function
open import Function.Equivalence using (_⇔_; equivalence)
open import Relation.Binary.PropositionalEquality

-- agda-combinatorics
open import Math.Combinatorics.Function
open import Math.Combinatorics.Function.Properties
open import Math.Combinatorics.ListFunction
import Math.Combinatorics.ListFunction.Properties.Lemma as Lemma

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

  All-length-combinations : ∀ (k : ℕ) (xs : List A) →
                            All (λ ys → length ys ≡ k) (combinations k xs)
  All-length-combinations 0       xs = refl ∷ []
  All-length-combinations (suc k) []       = []
  All-length-combinations (suc k) (x ∷ xs) = Allₚ.++⁺ (Allₚ.map⁺ $ All.map (cong suc) $ All-length-combinations k xs) (All-length-combinations (suc k) xs)

  ∈-length-combinations : ∀ (xs : List A) k ys → xs ∈ combinations k ys → length xs ≡ k
  ∈-length-combinations xs k ys xs∈combinations[k,ys] = All.lookup (All-length-combinations k ys) xs∈combinations[k,ys]

  combinations-⊆⇒∈ : ∀ {xs ys : List A} → xs ⊆ ys → xs ∈ combinations (length xs) ys
  combinations-⊆⇒∈ {[]}     {ys}     xs⊆ys = here refl
  combinations-⊆⇒∈ {x ∷ xs} {y ∷ ys} (.y  ∷ʳ x∷xs⊆ys) =
    ∈ₚ.∈-++⁺ʳ (map (y ∷_) (combinations (length xs) ys)) (combinations-⊆⇒∈ x∷xs⊆ys)
  combinations-⊆⇒∈ {x ∷ xs} {.x ∷ ys} (refl ∷  xs⊆ys)   =
    ∈ₚ.∈-++⁺ˡ $ ∈ₚ.∈-map⁺ (x ∷_) $ combinations-⊆⇒∈ xs⊆ys

  combinations-∈⇒⊆ : ∀ {xs ys : List A} → xs ∈ combinations (length xs) ys → xs ⊆ ys
  combinations-∈⇒⊆ {[]}     {ys} xs∈combinations[length[xs],ys] = Lemma.[]⊆xs ys
  combinations-∈⇒⊆ {x ∷ xs} {y ∷ ys} x∷xs∈combinations[length[x∷xs],y∷ys] with ∈ₚ.∈-++⁻ (map (y ∷_) (combinations (length xs) ys)) x∷xs∈combinations[length[x∷xs],y∷ys]
  ... | inj₁ x∷xs∈map[y∷-][combinations[length[xs],ys]] with ∈ₚ.∈-map⁻ (y ∷_) x∷xs∈map[y∷-][combinations[length[xs],ys]] -- ∷ ∃zs→zs∈combinations[length[xs],ys]×x∷xs≡y∷zs
  combinations-∈⇒⊆ {x ∷ xs} {y ∷ ys} _ | inj₁ _ | zs , (zs∈combinations[length[xs],ys] , x∷xs≡y∷zs) = x≡y ∷ xs⊆ys
    where
    xs≡zs : xs ≡ zs
    xs≡zs = Lₚ.∷-injectiveʳ x∷xs≡y∷zs
    x≡y : x ≡ y
    x≡y = Lₚ.∷-injectiveˡ x∷xs≡y∷zs
    xs⊆ys : xs ⊆ ys
    xs⊆ys = combinations-∈⇒⊆ $ subst (λ v → v ∈ combinations (length xs) ys) (sym xs≡zs) zs∈combinations[length[xs],ys]
  combinations-∈⇒⊆ {x ∷ xs} {y ∷ ys} _ | inj₂ x∷xs∈combinations[length[x∷xs],ys]         = y ∷ʳ x∷xs⊆ys
    where
    x∷xs⊆ys : x ∷ xs ⊆ ys
    x∷xs⊆ys = combinations-∈⇒⊆ x∷xs∈combinations[length[x∷xs],ys]

  combinations-⊆⇔∈ : ∀ {xs ys : List A} → xs ⊆ ys ⇔ xs ∈ combinations (length xs) ys
  combinations-⊆⇔∈ = equivalence combinations-⊆⇒∈ combinations-∈⇒⊆

module _ {a b} {A : Set a} {B : Set b} where
  combinations-map : ∀ k (f : A → B) (xs : List A) →
    combinations k (map f xs) ≡ map (map f) (combinations k xs)
  combinations-map 0       f xs       = refl
  combinations-map (suc k) f []       = refl
  combinations-map (suc k) f (x ∷ xs) = begin
    map (f x ∷_) (combinations k (map f xs)) ++ combinations (suc k) (map f xs)
      ≡⟨ cong₂ _++_ (cong (map (f x ∷_)) (combinations-map k f xs)) (combinations-map (suc k) f xs) ⟩
    map (f x ∷_) (map (map f) (combinations k xs)) ++ map (map f) (combinations (suc k) xs)
      ≡⟨ cong (_++ map (map f) (combinations (suc k) xs)) $ Lemma.lemma₁ f x (combinations k xs) ⟩
    map (map f) (map (x ∷_) (combinations k xs)) ++ map (map f) (combinations (suc k) xs)
      ≡⟨ sym $ Lₚ.map-++-commute (map f) (map (x ∷_) (combinations k xs)) (combinations (suc k) xs) ⟩
    map (map f) (map (x ∷_) (combinations k xs) ++ combinations (suc k) xs)
      ∎
    where open ≡-Reasoning

  -- unique-combinations : Unique xs → Unique (combinations k xs)
  -- All (⊆ xs) (combinations k xs)
