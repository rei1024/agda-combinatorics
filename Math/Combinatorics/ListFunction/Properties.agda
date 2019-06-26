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
open import Data.Product as Prod using (_×_; _,_; ∃; proj₁; proj₂)
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
    1 + length (map (x ∷_) (applyEach f xs))
      ≡⟨ cong suc $ Lₚ.length-map (x ∷_) (applyEach f xs ) ⟩
    1 + length (applyEach f xs)
      ≡⟨ cong suc $ length-applyEach f xs ⟩
    1 + length xs
      ∎

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
  All-length-combinations 0       xs       = refl ∷ []
  All-length-combinations (suc k) []       = []
  All-length-combinations (suc k) (x ∷ xs) =
    Allₚ.++⁺ (Allₚ.map⁺ $ All.map (cong suc) $ All-length-combinations k xs)
             (All-length-combinations (suc k) xs)

  ∈-length-combinations : ∀ (xs : List A) k ys → xs ∈ combinations k ys → length xs ≡ k
  ∈-length-combinations xs k ys xs∈combinations[k,ys] =
    All.lookup (All-length-combinations k ys) xs∈combinations[k,ys]

  combinations-⊆⇒∈ : ∀ {xs ys : List A} → xs ⊆ ys → xs ∈ combinations (length xs) ys
  combinations-⊆⇒∈ {[]}     {ys}     xs⊆ys              = here refl
  combinations-⊆⇒∈ {x ∷ xs} {y ∷ ys} (.y  ∷ʳ x∷xs⊆ys)   =
    ∈ₚ.∈-++⁺ʳ (map (y ∷_) (combinations (length xs) ys)) (combinations-⊆⇒∈ x∷xs⊆ys)
  combinations-⊆⇒∈ {x ∷ xs} {.x ∷ ys} (refl ∷  xs⊆ys)   =
    ∈ₚ.∈-++⁺ˡ $ ∈ₚ.∈-map⁺ (x ∷_) $ combinations-⊆⇒∈ xs⊆ys

  combinations-∈⇒⊆ : ∀ {xs ys : List A} → xs ∈ combinations (length xs) ys → xs ⊆ ys
  combinations-∈⇒⊆ {[]}     {ys}     _                       = Lemma.[]⊆xs ys
  combinations-∈⇒⊆ {x ∷ xs} {y ∷ ys} x∷xs∈c[len[x∷xs],y∷ys]
    with ∈ₚ.∈-++⁻ (map (y ∷_) (combinations (length xs) ys)) x∷xs∈c[len[x∷xs],y∷ys]
  ... | inj₁ x∷xs∈map[y∷-][c[len[xs],ys]]
      with ∈ₚ.∈-map⁻ (y ∷_) x∷xs∈map[y∷-][c[len[xs],ys]] -- ∷ ∃ λ zs → zs ∈ combinations (length xs) ys × x ∷ xs ≡ y ∷ zs
  combinations-∈⇒⊆ {x ∷ xs} {y ∷ ys} _ | inj₁ _
         | zs , (zs∈c[len[xs],ys] , x∷xs≡y∷zs) = x≡y ∷ xs⊆ys
    where
    xs≡zs : xs ≡ zs
    xs≡zs = Lₚ.∷-injectiveʳ x∷xs≡y∷zs
    x≡y : x ≡ y
    x≡y = Lₚ.∷-injectiveˡ x∷xs≡y∷zs
    xs⊆ys : xs ⊆ ys
    xs⊆ys = combinations-∈⇒⊆ $ subst (λ v → v ∈ combinations (length xs) ys)
                                      (sym xs≡zs) zs∈c[len[xs],ys]
  combinations-∈⇒⊆ {x ∷ xs} {y ∷ ys} _ | inj₂ x∷xs∈c[len[x∷xs],ys] = y ∷ʳ x∷xs⊆ys
    where
    x∷xs⊆ys : x ∷ xs ⊆ ys
    x∷xs⊆ys = combinations-∈⇒⊆ x∷xs∈c[len[x∷xs],ys]

  combinations-∈⇔⊆ : ∀ {xs ys : List A} → xs ∈ combinations (length xs) ys ⇔ xs ⊆ ys
  combinations-∈⇔⊆ = equivalence combinations-∈⇒⊆ combinations-⊆⇒∈

  All-⊆-combinations : ∀ k (xs : List A) → All (_⊆ xs) (combinations k xs)
  All-⊆-combinations k xs = All.tabulate λ {ys} ys∈combinations[k,xs] →
    combinations-∈⇒⊆ $ subst (λ v → ys ∈ combinations v xs)
      (sym $ ∈-length-combinations ys k xs ys∈combinations[k,xs])
      ys∈combinations[k,xs]

  combinations-∈⇒⊆∧length : ∀ {xs : List A} {k ys} →
                            xs ∈ combinations k ys → (xs ⊆ ys × length xs ≡ k)
  combinations-∈⇒⊆∧length {xs} {k} {ys} xs∈c[k,ys] =
    combinations-∈⇒⊆ xs∈c[len[xs],ys] , length[xs]≡k
    where
    length[xs]≡k : length xs ≡ k
    length[xs]≡k = ∈-length-combinations xs k ys xs∈c[k,ys]
    xs∈c[len[xs],ys] : xs ∈ combinations (length xs) ys
    xs∈c[len[xs],ys] =
      subst (λ v → xs ∈ combinations v ys) (sym length[xs]≡k) xs∈c[k,ys]

  combinations-⊆∧length⇒∈ : ∀ {xs ys : List A} {k} →
    (xs ⊆ ys × length xs ≡ k) → xs ∈ combinations k ys
  combinations-⊆∧length⇒∈ {xs} {ys} {k} (xs⊆ys , len[xs]≡k) =
    subst (λ v → xs ∈ combinations v ys) len[xs]≡k (combinations-⊆⇒∈ xs⊆ys)

  combinations-∈⇔⊆∧length : ∀ {xs : List A} {k} {ys} →
                            xs ∈ combinations k ys ⇔ (xs ⊆ ys × length xs ≡ k)
  combinations-∈⇔⊆∧length =
    equivalence combinations-∈⇒⊆∧length combinations-⊆∧length⇒∈

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

------------------------------------------------------------------------
-- Properties of `combinationsWithComplement`

module _ {a} {A : Set a} where
  open ≡-Reasoning
  map-proj₁-combinationsWithComplement : ∀ k (xs : List A) →
    map proj₁ (combinationsWithComplement k xs) ≡ combinations k xs
  map-proj₁-combinationsWithComplement 0       xs       = refl
  map-proj₁-combinationsWithComplement (suc k) []       = refl
  map-proj₁-combinationsWithComplement (suc k) (x ∷ xs) = begin
    map proj₁ (map f ys ++ map g zs)
      ≡⟨ Lₚ.map-++-commute proj₁ (map f ys) (map g zs) ⟩
    map proj₁ (map f ys) ++ map proj₁ (map g zs)
      ≡⟨ sym $ Lₚ.map-compose ys ⟨ cong₂ _++_ ⟩ Lₚ.map-compose zs ⟩
    map (proj₁ ∘′ f) ys ++ map (λ v → proj₁ (g v)) zs
      ≡⟨ Lₚ.map-cong lemma₁ ys ⟨ cong₂ _++_ ⟩ Lₚ.map-cong lemma₂ zs ⟩
    map ((x ∷_) ∘′ proj₁) ys ++ map proj₁ zs
      ≡⟨ cong (_++ map proj₁ zs) $ Lₚ.map-compose ys ⟩
    map (x ∷_) (map proj₁ ys) ++ map proj₁ zs
      ≡⟨ cong (map (x ∷_)) (map-proj₁-combinationsWithComplement k xs) ⟨ cong₂ _++_ ⟩ map-proj₁-combinationsWithComplement (suc k) xs ⟩
    map (x ∷_) (combinations k xs) ++ combinations (suc k) xs
      ∎
    where
    ys = combinationsWithComplement k xs
    zs = combinationsWithComplement (suc k) xs
    f g : List A × List A → List A × List A
    f = Prod.map₁ (x ∷_)
    g = Prod.map₂ (x ∷_)
    lemma₁ : ∀ (t : List A × List A) → proj₁ (Prod.map₁ (x ∷_) t) ≡ x ∷ proj₁ t
    lemma₁ t = Lemma.proj₁-map₁ (x ∷_) t
    lemma₂ : ∀ (t : List A × List A) → Lemma.proj₁′ {_} {_} {_} {List A} (Prod.map₂ (x ∷_) t) ≡ proj₁ t
    lemma₂ t = Lemma.proj₁-map₂ (x ∷_) t

  length-combinationsWithComplement : ∀ k (xs : List A) →
    length (combinationsWithComplement k xs) ≡ C (length xs) k
  length-combinationsWithComplement k xs = begin
    length (combinationsWithComplement k xs)
      ≡⟨ sym $ Lₚ.length-map proj₁ (combinationsWithComplement k xs) ⟩
    length (map proj₁ (combinationsWithComplement k xs))
      ≡⟨ cong length $ map-proj₁-combinationsWithComplement k xs ⟩
    length (combinations k xs)
      ≡⟨ length-combinations k xs ⟩
    C (length xs) k
      ∎

  -- unique-combinations : Unique xs → Unique (combinations k xs)
  -- sorted-combinations : Sorted _<_ xs → Sorted {- Lex._<_ _<_ -} (combinations k xs)
  -- filter-combinations = filter P ∘ combinations k xs
  -- each-disjoint-combinationsWithComplement : Unique zs → (xs , ys) ∈ combinationsWithComplement k zs → Disjoint xs ys
  -- combinationsWithComplement-∈⇒⊆ : (xs , ys) ∈ combinationsWithComplement (length xs) zs → xs ⊆ zs × ys ⊆ zs
  -- splits₂-defn : splits₂ xs ≡ zip _,_ (inits xs) (tails xs)
  -- length-splits₂ : length (splits₂ xs) ≡ 1 + length xs
  -- length-splits : length (splits k xs) ≡ C (length xs + k ∸ 1) (length xs)
  -- length-partitionsAll : length (partitionsAll xs) ≡ B (length xs)
  -- length-insertEverywhere : length (insertEverywhere x xs) ≡ 1 + length xs
  -- All-length-insertEverywhere : All (λ ys → length ys ≡ 1 + length xs) (insertEverywhere x xs)
  -- length-permutations : length (permutations xs) ≡ length xs !
