{-# OPTIONS --without-K --safe #-}

module Math.Combinatorics.Function.Properties.Lemma where

open import Data.Unit using (tt)
open import Data.Product
open import Data.Sum
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.DivMod
open import Data.Nat.Solver using (module +-*-Solver)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Function
open import Algebra.FunctionProperties

open ≤-Reasoning

1≤n⇒n≢0 : ∀ {n} → 1 ≤ n → n ≢ 0
1≤n⇒n≢0 .{suc _} (s≤s z≤n) ()

-- TODO: use m<n⇒0<n∸m
m<n⇒n∸m≢0 : ∀ {m n} → m < n → n ∸ m ≢ 0
m<n⇒n∸m≢0 {m} {n} m<n n∸m≡0 = (λ x → x (sym n∸m≡0)) $ <⇒≢ $ +-cancelʳ-< 0 (n ∸ m) $ begin-strict
  m           <⟨ m<n ⟩
  n           ≡⟨ sym $ m∸n+n≡m (<⇒≤ m<n) ⟩
  (n ∸ m) + m ∎

≤⇒≡∨< : ∀ {m n} → m ≤ n → (m ≡ n) ⊎ (m < n)
≤⇒≡∨< {m} {n} m≤n with m ≟ n
... | yes m≡n = inj₁ m≡n
... | no  m≢n = inj₂ (≤∧≢⇒< m≤n m≢n)

^-monoˡ-≤ : ∀ n → (_^ n) Preserves _≤_ ⟶ _≤_
^-monoˡ-≤ 0       {m} {o} m≤o = ≤-refl
^-monoˡ-≤ (suc n) {m} {o} m≤o = begin
  m ^ suc n ≡⟨⟩
  m * m ^ n ≤⟨ *-mono-≤ m≤o (^-monoˡ-≤ n m≤o) ⟩
  o * o ^ n ≡⟨⟩
  o ^ suc n ∎

1≤[1+m]^n : ∀ m n → 1 ≤ (1 + m) ^ n
1≤[1+m]^n m zero = ≤-refl
1≤[1+m]^n m (suc n) = begin
  1 * 1             ≤⟨ *-mono-≤ (s≤s {0} {m} z≤n) (1≤[1+m]^n m n) ⟩
  suc m * suc m ^ n ∎

^-monoʳ-≤ : ∀ n → (suc n ^_) Preserves _≤_ ⟶ _≤_
^-monoʳ-≤ n {.0}       {o}        z≤n       = begin
  1         ≤⟨ 1≤[1+m]^n n o ⟩
  suc n ^ o ∎
^-monoʳ-≤ n {.(suc _)} {.(suc _)} (s≤s {m} {o} m≤o) = begin
  suc n ^ suc m     ≡⟨⟩
  suc n * suc n ^ m ≤⟨ *-monoʳ-≤ (suc n) (^-monoʳ-≤ n m≤o) ⟩
  suc n * suc n ^ o ≡⟨⟩
  suc n ^ suc o     ∎

^-mono-≤ : ∀ {m n o p} → m ≤ n → o ≤ p → suc m ^ o ≤ suc n ^ p
^-mono-≤ {m} {n} {o} {p} m≤n o≤p = begin
  suc m ^ o ≤⟨ ^-monoˡ-≤ o (s≤s m≤n) ⟩
  suc n ^ o ≤⟨ ^-monoʳ-≤ n o≤p ⟩
  suc n ^ p ∎

-- ∸-mono-< : _∸_ Preserves₂ _<_ ⟶ _>_ ⟶ _<_
-- TODO: replace with stdlib
∸-monoʳ-< : ∀ {m n} o → n ≤ o → m < n → o ∸ m > o ∸ n
∸-monoʳ-< {m} {n} o n≤o m<n = +-cancelʳ-< (o ∸ n) (o ∸ m) $ begin-strict
  (o ∸ n) + m <⟨ +-monoʳ-< (o ∸ n) m<n ⟩ -- n<m
  (o ∸ n) + n ≡⟨ m∸n+n≡m n≤o ⟩
  o           ≡⟨ sym $ m∸n+n≡m m≤o ⟩
  (o ∸ m) + m ∎
  where
  m≤o : m ≤ o
  m≤o = <⇒≤ $ <-transˡ m<n n≤o

*-cancelʳ-≤′ : ∀ m n {o} → False (o ≟ 0) → m * o ≤ n * o → m ≤ n
*-cancelʳ-≤′ m n {suc o} tt = *-cancelʳ-≤ m n o

-- TODO upadte stdlib
*-cancelʳ-≡′ : ∀ m n {o} → False (o ≟ 0) → m * o ≡ n * o → m ≡ n
*-cancelʳ-≡′ m n {suc o} tt = *-cancelʳ-≡ m n

*-monoʳ-<′ : ∀ n → False (n ≟ 0) → (n *_) Preserves _<_ ⟶ _<_
*-monoʳ-<′ (suc n) tt gt = *-monoʳ-< n gt

*-monoˡ-<′ : ∀ n → False (n ≟ 0) → (_* n) Preserves _<_ ⟶ _<_
*-monoˡ-<′ (suc n) tt gt = *-monoˡ-< n gt

m≡n+o⇒m∸o≡n : ∀ m n o → m ≡ n + o → m ∸ o ≡ n
m≡n+o⇒m∸o≡n m n o m≡n+o = trans (cong (_∸ o) m≡n+o) (m+n∸n≡m n o)

lemma₃ : ∀ m n → (∃ λ o → (n ≡ o + m)) ⊎ (n < m)
lemma₃ m n with compare m n
lemma₃ m              .(suc (m + k)) | less    .m k = inj₁ (suc k , cong suc (+-comm m k))
lemma₃ m              .m             | equal   .m   = inj₁ (0 , +-identityˡ m)
lemma₃ .(suc (n + k)) n              | greater .n k = inj₂ (s≤s (≤-stepsʳ k ≤-refl))

m≡n*o⇒n≡m/o : ∀ m n o → (wit : False (o ≟ 0)) → m ≡ n * o → n ≡ _/_ m o {wit}
m≡n*o⇒n≡m/o m n o@(suc o-1) tt m≡n*o = sym $ begin-equality
  m / o       ≡⟨ cong (_/ o) $ m≡n*o ⟩
  (n * o) / o ≡⟨ m*n/n≡m n o ⟩
  n            ∎

m*n≡o⇒m≡o/n : ∀ m n o → (wit : False (n ≟ 0)) → m * n ≡ o → m ≡ _/_ o n {wit}
m*n≡o⇒m≡o/n m n o wit m*n≡o = m≡n*o⇒n≡m/o o m n wit (sym m*n≡o)

*-pres-≢0 : ∀ {a b} → a ≢ 0 → b ≢ 0 → a * b ≢ 0
*-pres-≢0 {0}     {b} a≢0 b≢0 a*b≡0 = a≢0 refl
*-pres-≢0 {suc a} {0} a≢0 b≢0 a*b≡0 = b≢0 refl

-- TODO numbering
lemma₅ : ∀ m n o p → (m + n) * (o * p) ≡ (o * (m * p)) + n * (o * p)
lemma₅ = solve 4 (λ m n o p →
  (m :+ n) :* (o :* p) := (o :* (m :* p)) :+ (n :* (o :* p))) refl
  where open +-*-Solver

lemma₇ : ∀ m n o → m * n * o ≡ m * o * n
lemma₇ = solve 3 (λ m n o → m :* n :* o := m :* o :* n) refl
  where open +-*-Solver

lemma₈ : ∀ m n o → m * (n * o) ≡ n * m * o
lemma₈ = solve 3 (λ m n o → m :* (n :* o) := n :* m :* o) refl
  where open +-*-Solver

lemma₉ : ∀ m n o p → m * n * (o * p) ≡ (m * o) * (n * p)
lemma₉ = solve 4 (λ m n o p → m :* n :* (o :* p) := (m :* o) :* (n :* p)) refl
  where open +-*-Solver

lemma₁₀ : ∀ m n o p → m * n * o * p ≡ (m * o) * (n * p)
lemma₁₀ = solve 4 (λ m n o p → m :* n :* o :* p := (m :* o) :* (n :* p)) refl
  where open +-*-Solver

lemma₁₁ : ∀ m n o p → (m * n) * (o * p) ≡ m * o * p * n
lemma₁₁ = solve 4 (λ m n o p → (m :* n) :* (o :* p) := m :* o :* p :* n) refl
  where open +-*-Solver

lemma₁₂ : ∀ m n o → m * n * o ≡ n * (m * o)
lemma₁₂ = solve 3 (λ m n o → m :* n :* o := n :* (m :* o)) refl
  where open +-*-Solver

lemma₁₃ : ∀ m n o → m * n * n * o ≡ o * m * n * n
lemma₁₃ = solve 3 (λ m n o → m :* n :* n :* o := o :* m :* n :* n) refl
  where open +-*-Solver
