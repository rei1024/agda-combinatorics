------------------------------------------------------------------------
-- Properties of functions
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --exact-split #-}

module Math.Combinatorics.ListFunction.Properties where

-- agda-stdlib
open import Data.List hiding (_∷ʳ_)
import Data.List.Properties as Lₚ
open import Data.List.Membership.Propositional using (_∈_; _∉_)
import Data.List.Membership.Propositional.Properties as ∈ₚ
open import Data.List.Relation.Binary.BagAndSetEquality
open import Data.List.Relation.Binary.Sublist.Propositional using (_⊆_; []; _∷_; _∷ʳ_)
import Data.List.Relation.Binary.Sublist.Propositional.Properties as Sublistₚ
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as Allₚ
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
import Data.List.Relation.Unary.Unique.Propositional as UniqueP
import Data.List.Relation.Unary.Unique.Propositional.Properties as UniquePₚ
import Data.List.Relation.Unary.Unique.Setoid as UniqueS
import Data.List.Relation.Unary.Unique.Setoid.Properties as UniqueSₚ
open import Data.Nat
open import Data.Product as Prod using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Function.Core
open import Function.Equivalence using (_⇔_; equivalence) -- TODO: use new packages
open import Relation.Binary.PropositionalEquality as P

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

  applyEach-cong : ∀ (f g : A → A) (xs : List A) →
    (∀ x → f x ≡ g x) → applyEach f xs ≡ applyEach g xs
  applyEach-cong f g []       f≡g = refl
  applyEach-cong f g (x ∷ xs) f≡g = begin
    (f x ∷ xs) ∷ map (_∷_ x) (applyEach f xs)
      ≡⟨ cong₂ (λ u v → (u ∷ xs) ∷ map (_∷_ x) v) (f≡g x) (applyEach-cong f g xs f≡g) ⟩
    (g x ∷ xs) ∷ map (_∷_ x) (applyEach g xs)
      ∎

------------------------------------------------------------------------
-- Properties of `combinations`

module _ {a} {A : Set a} where
  open ≡-Reasoning

  length-combinations : ∀ (k : ℕ) (xs : List A) →
                        length (combinations k xs) ≡ C (length xs) k
  length-combinations 0       xs       = refl
  length-combinations (suc k) []       = refl
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

  combinations-∈⇔⊆ : ∀ {xs ys : List A} → (xs ∈ combinations (length xs) ys) ⇔ (xs ⊆ ys)
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

  unique-combinations : ∀ k {xs : List A} →
    UniqueP.Unique xs → UniqueP.Unique (combinations k xs)
  unique-combinations 0      {xs}      xs-unique                = [] ∷ []
  unique-combinations (suc k) {[]}     xs-unique                = []
  unique-combinations (suc k) {x ∷ xs} (All[x≢-]xs ∷ xs-unique) =
    UniquePₚ.++⁺ {_} {_} {map (x ∷_) (combinations k xs)} {combinations (suc k) xs}
      (UniquePₚ.map⁺ Lₚ.∷-injectiveʳ (unique-combinations k {xs} xs-unique))
      (unique-combinations (suc k) {xs} xs-unique)
      λ {vs} vs∈map[x∷-]c[k,xs]×vs∈c[1+k,xs] →
      let
        vs∈map[x∷-]c[k,xs] = proj₁ vs∈map[x∷-]c[k,xs]×vs∈c[1+k,xs]
        vs∈c[1+k,xs] = proj₂ vs∈map[x∷-]c[k,xs]×vs∈c[1+k,xs]
        proof = ∈ₚ.∈-map⁻ (x ∷_) vs∈map[x∷-]c[k,xs]
        us = proj₁ proof
        vs≡x∷us : vs ≡ x ∷ us
        vs≡x∷us = proj₂ (proj₂ proof)
        x∈vs : x ∈ vs
        x∈vs = subst (x ∈_) (sym vs≡x∷us) (here refl)
        vs⊆xs : vs ⊆ xs
        vs⊆xs = proj₁ $ combinations-∈⇒⊆∧length {vs} {suc k} {xs} vs∈c[1+k,xs]
        All[x≢-]vs : All (x ≢_) vs
        All[x≢-]vs = Sublistₚ.All-resp-⊆ vs⊆xs All[x≢-]xs
        x∉vs : x ∉ vs
        x∉vs = Allₚ.All¬⇒¬Any All[x≢-]vs
      in x∉vs x∈vs
  {-
  --   unique⇒drop-cons-set : ∀ {a} {A : Set a} {x : A} {xs ys} →
  unique-combinations-set : ∀ k {xs : List A} →
    UniqueP.Unique xs → UniqueS.Unique ([ set ]-Equality A) (combinations k xs)
  unique-combinations-set 0                xs-unique          = [] ∷ []
  unique-combinations-set (suc k) {[]}     xs-unique          = []
  unique-combinations-set (suc k) {x ∷ xs} (this ∷ xs-unique) =
    UniqueSₚ.++⁺ ([ set ]-Equality A)
      (UniqueSₚ.map⁺ ([ set ]-Equality A) ([ set ]-Equality A) (λ → {!   !}) (unique-combinations-set k {xs} xs-unique))
      (unique-combinations-set (suc k) {xs} xs-unique)
      {!   !}
  -- {- x∉xs -} Unique -[ set ] xs → Unique -[ set ] (x ∷ xs)
  -}

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

------------------------------------------------------------------------
-- Properties of `splits₂`

module _ {a} {A : Set a} where
  open ≡-Reasoning
  open Prod using (map₁; map₂)

  length-splits₂ : ∀ (xs : List A) → length (splits₂ xs) ≡ 1 + length xs
  length-splits₂ []       = refl
  length-splits₂ (x ∷ xs) = begin
    1 + length (map (map₁ (x ∷_)) (splits₂ xs))
      ≡⟨ cong (1 +_) $ Lₚ.length-map (map₁ (x ∷_)) (splits₂ xs) ⟩
    1 + length (splits₂ xs)
      ≡⟨ cong (1 +_) $ length-splits₂ xs ⟩
    1 + length (x ∷ xs)
      ∎

  splits₂-defn : ∀ (xs : List A) → splits₂ xs ≡ zip (inits xs) (tails xs)
  splits₂-defn []       = refl
  splits₂-defn (x ∷ xs) = begin
    splits₂ (x ∷ xs) ≡⟨⟩
    ([] , x ∷ xs) ∷ map (map₁ (x ∷_)) (splits₂ xs)
      ≡⟨ cong (([] , x ∷ xs) ∷_) (begin
        map (map₁ (x ∷_)) (splits₂ xs)
          ≡⟨ cong (map (map₁ (x ∷_))) $ splits₂-defn xs ⟩
        map (map₁ (x ∷_)) (zip is ts)
          ≡⟨ Lₚ.map-zipWith _,_ (map₁ (x ∷_)) is ts ⟩
        zipWith (λ ys zs → map₁ (x ∷_) (ys , zs)) is ts
          ≡⟨ sym $ Lₚ.zipWith-map _,_ (x ∷_) id is ts ⟩
        zip (map (x ∷_) is) (map id ts)
          ≡⟨ cong (zip (map (x ∷_) is)) $ Lₚ.map-id ts ⟩
        zip (map (x ∷_) is) ts
          ∎) ⟩
    ([] , x ∷ xs) ∷ zip (map (x ∷_) is) ts
      ∎
    where
    is = inits xs
    ts = tails xs

  All-++-splits₂ : (xs : List A) →
    All (Prod.uncurry (λ ys zs → ys ++ zs ≡ xs)) (splits₂ xs)
  All-++-splits₂ []       = refl ∷ []
  All-++-splits₂ (x ∷ xs) =
    All._∷_ refl $ Allₚ.map⁺ $ All.map (cong (x ∷_)) $ All-++-splits₂ xs

  splits₂-∈⇒++ : {xs ys zs : List A} → (ys , zs) ∈ splits₂ xs → ys ++ zs ≡ xs
  splits₂-∈⇒++ {xs = xs} = All.lookup (All-++-splits₂ xs)

  private
    [],xs∈splits₂[xs] : (xs : List A) → ([] , xs) ∈ splits₂ xs
    [],xs∈splits₂[xs] []       = here refl
    [],xs∈splits₂[xs] (x ∷ xs) = here refl

  ∈-split₂-++ : (xs ys : List A) → (xs , ys) ∈ splits₂ (xs ++ ys)
  ∈-split₂-++ []       ys = [],xs∈splits₂[xs] ys
  ∈-split₂-++ (x ∷ xs) ys =
    Any.there $ ∈ₚ.∈-map⁺ (map₁ (x ∷_)) $ ∈-split₂-++ xs ys

  splits₂-++⇒∈ : {xs ys zs : List A} → xs ++ ys ≡ zs → (xs , ys) ∈ splits₂ zs
  splits₂-++⇒∈ {xs} {ys} {zs} xs++ys≡zs =
    subst (λ v → (xs , ys) ∈ splits₂ v) xs++ys≡zs (∈-split₂-++ xs ys)

  splits₂-∈⇔++ : {xs ys zs : List A} → (xs , ys) ∈ splits₂ zs ⇔ xs ++ ys ≡ zs
  splits₂-∈⇔++ = equivalence splits₂-∈⇒++ splits₂-++⇒∈

module _ {a b} {A : Set a} {B : Set b} where
  open ≡-Reasoning

  {-
  splits₂-map : ∀ (f : A → B) (xs : List A) →
    splits₂ (map f xs) ≡ map (Prod.map (map f) (map f)) (splits₂ xs)
  splits₂-map f []       = refl
  splits₂-map f (x ∷ xs) = {!   !}
  -}
  -- length[xs]<k⇒combinations[k,xs]≡[]
  -- All-unique-combinations : UniqueP.Unique xs → All (UniqueP.Unique) (combinations k xs)
  -- All-unique-combinations-set : UniqueP.Unique xs → All (UniqueS.Unique [ set ]-Equality A) (combinations k xs)
  -- unique-combinations-PW : UniqueS.Unique S xs → UniqueS.Unique (Equality S) (combinations k xs)
  -- unique-combinations-set : UniqueP.Unique xs → Unique (_-[ set ]_) (combinations k xs)
  -- sorted-combinations : Sorted _<_ xs → Sorted {- Lex._<_ _<_ -} (combinations k xs)
  -- All-sorted-combinations : Sorted _<_ xs → All (Sorted _<_) (combinations k xs)
  -- filter-combinations = filter P ∘ combinations k xs
  -- each-disjoint-combinationsWithComplement : Unique zs → (xs , ys) ∈ combinationsWithComplement k zs → Disjoint xs ys
  -- combinationsWithComplement-∈⇒⊆ : (xs , ys) ∈ combinationsWithComplement (length xs) zs → xs ⊆ zs × ys ⊆ zs
  -- length-splits : length (splits k xs) ≡ C (length xs + k ∸ 1) (length xs)
  -- length-partitionsAll : length (partitionsAll xs) ≡ B (length xs)
  -- length-insertEverywhere : length (insertEverywhere x xs) ≡ 1 + length xs
  -- All-length-insertEverywhere : All (λ ys → length ys ≡ 1 + length xs) (insertEverywhere x xs)
  -- length-permutations : length (permutations xs) ≡ length xs !
