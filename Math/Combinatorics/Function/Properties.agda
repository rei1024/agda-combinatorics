------------------------------------------------------------------------
-- Properties of combinatorial functions
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --exact-split #-}

module Math.Combinatorics.Function.Properties where

-- stdlib

open import Data.Empty using (⊥-elim)
open import Data.List as List
open import Data.Maybe
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.DivMod
open import Data.Product
open import Data.Sum
open import Data.Unit using (tt)
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable

-- agda-combinatorics
open import Math.Combinatorics.Function
open import Math.Combinatorics.Function using (n!≢0 ; False[n!≟0]) public
import Math.Combinatorics.Function.Properties.Lemma as Lemma

open ≤-Reasoning

private
  _≠0 : ℕ → Set
  n ≠0 = False (n ≟ 0)

------------------------------------------------------------------------
-- Properties of _!

1≤n! : ∀ n → 1 ≤ n !
1≤n! 0       = ≤-refl
1≤n! (suc n) = ≤-trans (1≤n! n) (m≤m+n (n !) _)

2≤[2+n]! : ∀ n → 2 ≤ (2 + n) !
2≤[2+n]! 0       = ≤-refl
2≤[2+n]! (suc n) = ≤-trans (2≤[2+n]! n) (m≤m+n ((2 + n) !) _)

!-mono-< : ∀ {m n} → suc m < n → suc m ! < n !
!-mono-< {0}     {suc zero}    (s≤s ())
!-mono-< {0}     {suc (suc n)} _           = 2≤[2+n]! n
!-mono-< {suc m} {suc n}       (s≤s 1+m<n) =
  *-mono-< (s≤s 1+m<n) (!-mono-< 1+m<n)

!-mono-<-≢0 : ∀ {m n} {wit : m ≠0} → m < n → m ! < n !
!-mono-<-≢0 {suc m} {n} {tt} m<n = !-mono-< m<n

!-mono-<-≤ : ∀ {m n} → m < n → m ! ≤ n !
!-mono-<-≤ {0}     {n} _     = 1≤n! n
!-mono-<-≤ {suc m} {n} 1+m<n = <⇒≤ $ !-mono-< 1+m<n

!-mono-≤ : ∀ {m n} → m ≤ n → m ! ≤ n !
!-mono-≤ {m} {n} m≤n with Lemma.≤⇒≡∨< m≤n
... | inj₁ refl = ≤-refl {m !}
... | inj₂ m<n  = !-mono-<-≤ m<n

!-injective : ∀ {m n} {m≢0 : m ≠0} {n≢0 : n ≠0} → m ! ≡ n ! → m ≡ n
!-injective {m} {n} {m≢0} {n≢0} m!≡n! with <-cmp m n
... | tri< m<n _   _   = ⊥-elim $ <⇒≢ (!-mono-<-≢0 {m} {n} {m≢0} m<n) m!≡n!
... | tri≈ _   m≡n _   = m≡n
... | tri> _   _   n<m = ⊥-elim $ <⇒≢ (!-mono-<-≢0 {n} {m} {n≢0} n<m) (sym m!≡n!)

n!≤n^n : ∀ n → n ! ≤ n ^ n
n!≤n^n 0       = ≤-refl
n!≤n^n (suc n) = begin
  suc n * n !       ≤⟨ *-monoʳ-≤ (suc n) (n!≤n^n n) ⟩
  suc n * n ^ n     ≤⟨ *-monoʳ-≤ (suc n) (Lemma.^-monoˡ-≤ n (≤-step ≤-refl)) ⟩
  suc n * suc n ^ n ∎

2^n≤[1+n]! : ∀ n → 2 ^ n ≤ (suc n) !
2^n≤[1+n]! 0       = ≤-refl
2^n≤[1+n]! (suc n) = begin
  2 ^ suc n               ≡⟨⟩
  2 * 2 ^ n               ≤⟨ *-mono-≤ (m≤m+n 2 n) (2^n≤[1+n]! n) ⟩
  suc (suc n) * (suc n) ! ≡⟨⟩
  (suc (suc n)) !         ∎

[1+n]!/[1+n]≡n! : ∀ n → (suc n) ! div (suc n) ≡ n !
[1+n]!/[1+n]≡n! n =
  sym $ Lemma.m*n≡o⇒m≡o/n (n !) (suc n) ((suc n) !) tt (*-comm (n !) (suc n))

-- m≤n⇒m∣n! : ∀ {m n} → suc m ≤ n → suc m ∣ n !

------------------------------------------------------------------------
-- Properties of P

P[n,1]≡n : ∀ n → P n 1 ≡ n
P[n,1]≡n 0       = refl
P[n,1]≡n (suc n) = *-identityʳ (suc n)

P[n,n]≡n! : ∀ n → P n n ≡ n !
P[n,n]≡n! 0       = refl
P[n,n]≡n! (suc n) = cong (suc n *_) (P[n,n]≡n! n)

n<k⇒P[n,k]≡0 : ∀ {n k} → n < k → P n k ≡ 0
n<k⇒P[n,k]≡0 {0}     {suc k} n<k       = refl
n<k⇒P[n,k]≡0 {suc n} {suc k} (s≤s n<k) = begin-equality
  P (suc n) (suc k) ≡⟨⟩
  suc n * P n k     ≡⟨ cong (suc n *_) $ n<k⇒P[n,k]≡0 n<k ⟩
  suc n * 0         ≡⟨ *-zeroʳ (suc n) ⟩
  0                 ∎

-- m = 3; n = 4; o = 2
-- 7 6 5 4 3 = 7 6 5 * 4 3
P-split : ∀ m n o → P (m + n) (m + o) ≡ P (m + n) m * P n o
P-split 0       n o = sym $ +-identityʳ (P n o)
P-split (suc m) n o = begin-equality
  P (suc m + n) (suc m + o)           ≡⟨⟩
  (suc m + n) * P (m + n) (m + o)     ≡⟨ cong ((suc m + n) *_) $ P-split m n o ⟩
  (suc m + n) * (P (m + n) m * P n o) ≡⟨ sym $ *-assoc (suc m + n) (P (m + n) m) (P n o) ⟩
  P (suc m + n) (suc m) * P n o       ∎

-- proved by P-split, P[n,n]≡n!
-- m = 5; n =
-- 9 8 7 6 5
--         * 4 3 2 1 =
-- 9 8 7 6 5 4 3 2 1
P[m+n,m]*n!≡[m+n]! : ∀ m n → P (m + n) m * n ! ≡ (m + n) !
P[m+n,m]*n!≡[m+n]! m n = begin-equality
  P (m + n) m * n !   ≡⟨ cong (P (m + n) m *_) $ sym $ P[n,n]≡n! n ⟩
  P (m + n) m * P n n ≡⟨ sym $ P-split m n n ⟩
  P (m + n) (m + n)   ≡⟨ P[n,n]≡n! (m + n) ⟩
  (m + n) !           ∎

-- proved by P[m+n,m]*n!≡[m+n]!
P[m+n,n]*m!≡[m+n]! : ∀ m n → P (m + n) n * m ! ≡ (m + n) !
P[m+n,n]*m!≡[m+n]! m n = begin-equality
  P (m + n) n * m ! ≡⟨ cong (λ v → P v n * m !) $ +-comm m n ⟩
  P (n + m) n * m ! ≡⟨ P[m+n,m]*n!≡[m+n]! n m ⟩
  (n + m) !         ≡⟨ cong (_!) $ +-comm n m ⟩
  (m + n) !         ∎

-- proved by P[m+n,m]*n!≡[m+n]!
P[n,k]*[n∸k]!≡n! : ∀ {n k} → k ≤ n → P n k * (n ∸ k) ! ≡ n !
P[n,k]*[n∸k]!≡n! {n} {k} k≤n = begin-equality
  P n k * m !       ≡⟨ cong (λ v → P v k * m !) $ sym $ k+m≡n ⟩
  P (k + m) k * m ! ≡⟨ P[m+n,m]*n!≡[m+n]! k m ⟩
  (k + m) !         ≡⟨ cong (_!) $ k+m≡n ⟩
  n !               ∎
  where
  m = n ∸ k
  k+m≡n : k + m ≡ n
  k+m≡n = m+[n∸m]≡n k≤n

-- proved by P[n,k]*[n∸k]!≡n!
P[n,k]≡n!/[n∸k]! : ∀ {n k} → k ≤ n → P n k ≡ _div_ (n !) ((n ∸ k) !) {False[n!≟0] (n ∸ k)}
P[n,k]≡n!/[n∸k]! {n} {k} k≤n = Lemma.m*n≡o⇒m≡o/n (P n k) ((n ∸ k) !) (n !)
                               (False[n!≟0] (n ∸ k)) (P[n,k]*[n∸k]!≡n! k≤n)

P[m,m∸n]*n!≡m! : ∀ {m n} → n ≤ m → P m (m ∸ n) * n ! ≡ m !
P[m,m∸n]*n!≡m! {m} {n} n≤m = begin-equality
  P m o * n !       ≡⟨ sym $ cong (λ v → P v o * n !) o+n≡m ⟩
  P (o + n) o * n ! ≡⟨ P[m+n,m]*n!≡[m+n]! o n ⟩
  (o + n) !         ≡⟨ cong (_!) o+n≡m ⟩
  m !               ∎
  where
  o = m ∸ n
  o+n≡m : o + n ≡ m
  o+n≡m = m∸n+n≡m n≤m

m!/n!≡P[m,m∸n] : ∀ {m n} → n ≤ m → (m ! / n !) {False[n!≟0] n} ≡ P m (m ∸ n)
m!/n!≡P[m,m∸n] {m} {n} n≤m =
  sym $ Lemma.m≡n*o⇒n≡m/o (m !) (P m (m ∸ n)) (n !) (False[n!≟0] n)
                          (sym $ P[m,m∸n]*n!≡m! n≤m)

-- proved by P-split
-- m = 2; n = 7
-- 9 8 7 = 9 8 * 7
P[m+n,1+m]≡P[m+n,m]*n : ∀ m n → P (m + n) (suc m) ≡ P (m + n) m * n
P[m+n,1+m]≡P[m+n,m]*n m n = begin-equality
  P (m + n) (1 + m)   ≡⟨ cong (P (m + n)) $ +-comm 1 m ⟩
  P (m + n) (m + 1)   ≡⟨ P-split m n 1 ⟩
  P (m + n) m * P n 1 ≡⟨ cong (P (m + n) m *_) $ P[n,1]≡n n ⟩
  P (m + n) m * n     ∎

P[m+n,1+n]≡P[m+n,n]*m : ∀ m n → P (m + n) (suc n) ≡ P (m + n) n * m
P[m+n,1+n]≡P[m+n,n]*m m n = begin-equality
  P (m + n) (suc n) ≡⟨ cong (λ v → P v (suc n)) $ +-comm m n ⟩
  P (n + m) (suc n) ≡⟨ P[m+n,1+m]≡P[m+n,m]*n n m ⟩
  P (n + m) n * m   ≡⟨ cong (λ v → P v n * m) $ +-comm n m ⟩
  P (m + n) n * m   ∎

P[n,1+k]≡P[n,k]*[n∸k] : ∀ n k → P n (suc k) ≡ P n k * (n ∸ k)
P[n,1+k]≡P[n,k]*[n∸k] n k with Lemma.lemma₃ k n
... | inj₁ (m , n≡m+k) = begin-equality
  P n (suc k)       ≡⟨ cong (λ v → P v (suc k)) n≡m+k ⟩
  P (m + k) (suc k) ≡⟨ P[m+n,1+n]≡P[m+n,n]*m m k ⟩
  P (m + k) k * m   ≡⟨ sym $ cong₂ _*_ (cong (λ v → P v k) n≡m+k) n∸k≡m ⟩
  P n k * (n ∸ k)   ∎
  where
  n∸k≡m = Lemma.m≡n+o⇒m∸o≡n n m k n≡m+k
... | inj₂ n<k = begin-equality
  P n (suc k)     ≡⟨ n<k⇒P[n,k]≡0 (≤-step n<k) ⟩
  0               ≡⟨ sym $ *-zeroʳ (P n k) ⟩
  P n k * 0       ≡⟨ sym $ cong (P n k *_) $ m≤n⇒m∸n≡0 (<⇒≤ n<k) ⟩
  P n k * (n ∸ k) ∎

P[n,1+k]≡[n∸k]*P[n,k] : ∀ n k → P n (suc k) ≡ (n ∸ k) * P n k
P[n,1+k]≡[n∸k]*P[n,k] n k = trans (P[n,1+k]≡P[n,k]*[n∸k] n k) (*-comm (P n k) (n ∸ k))

-- proved by P[n,1+k]≡[n∸k]*P[n,k] and n<k⇒P[n,k]≡0
P[1+n,1+k]≡[1+k]*P[n,k]+P[n,1+k] : ∀ n k → P (suc n) (suc k) ≡ suc k * P n k + P n (suc k)
P[1+n,1+k]≡[1+k]*P[n,k]+P[n,1+k] n k with k ≤? n
... | yes k≤n = begin-equality
  suc n * P n k                   ≡⟨ cong (_* P n k) 1+n≡[1+k]+[n∸k] ⟩
  (suc k + (n ∸ k)) * P n k       ≡⟨ *-distribʳ-+ (P n k) (suc k) (n ∸ k) ⟩
  suc k * P n k + (n ∸ k) * P n k ≡⟨ sym $ cong (suc k * P n k +_) $ P[n,1+k]≡[n∸k]*P[n,k] n k ⟩
  suc k * P n k + P n (suc k)     ∎
  where
  1+n≡[1+k]+[n∸k] : suc n ≡ suc k + (n ∸ k)
  1+n≡[1+k]+[n∸k] = sym $ begin-equality
    suc k + (n ∸ k)   ≡⟨ +-assoc 1 k (n ∸ k) ⟩
    suc (k + (n ∸ k)) ≡⟨ cong suc $ m+[n∸m]≡n k≤n ⟩
    suc n             ∎
... | no k≰n = begin-equality
  P (suc n) (suc k)           ≡⟨ n<k⇒P[n,k]≡0 (s≤s n<k) ⟩
  0 + 0                       ≡⟨ sym $ cong (_+ 0) $ *-zeroʳ (suc k) ⟩
  suc k * 0 + 0               ≡⟨ sym $ cong₂ _+_ (cong (suc k *_) (n<k⇒P[n,k]≡0 n<k)) (n<k⇒P[n,k]≡0 (≤-step n<k)) ⟩
  suc k * P n k + P n (suc k) ∎
  where
  n<k : n < k
  n<k = ≰⇒> k≰n

P[1+n,n]≡n! : ∀ n → P (suc n) n ≡ (suc n) !
P[1+n,n]≡n! n = begin-equality
  P (1 + n) n       ≡⟨ cong (λ v → P v n) (+-comm 1 n) ⟩
  P (n + 1) n       ≡⟨ sym $ *-identityʳ (P (n + 1) n) ⟩
  P (n + 1) n * 1   ≡⟨ sym $ P-split n 1 1 ⟩
  P (n + 1) (n + 1) ≡⟨ P[n,n]≡n! (n + 1) ⟩
  (n + 1) !         ≡⟨ cong (_!) (+-comm n 1) ⟩
  (1 + n) !         ∎

P-split-∸-alternative : ∀ {m n o} → o ≤ m → o ≤ n → P m n ≡ P m o * P (m ∸ o) (n ∸ o)
P-split-∸-alternative {m} {n} {o} o≤m o≤n = begin-equality
  P m n               ≡⟨ sym $ cong₂ P o+p≡m o+q≡n ⟩
  P (o + p) (o + q)   ≡⟨ P-split o p q ⟩
  P (o + p) o * P p q ≡⟨ cong (λ v → P v o * P p q) o+p≡m ⟩
  P m o * P p q       ∎
  where
  p = m ∸ o
  q = n ∸ o
  o+p≡m : o + p ≡ m
  o+p≡m = m+[n∸m]≡n o≤m
  o+q≡n : o + q ≡ n
  o+q≡n = m+[n∸m]≡n o≤n

P-split-∸ : ∀ m n o → P m (n + o) ≡ P m n * P (m ∸ n) o
P-split-∸ m n o with n ≤? m
... | yes n≤m = begin-equality
  P m (n + o)         ≡⟨ sym $ cong (λ v → P v (n + o)) n+p≡m ⟩
  P (n + p) (n + o)   ≡⟨ P-split n p o ⟩
  P (n + p) n * P p o ≡⟨ cong (λ v → P v n * P p o) n+p≡m ⟩
  P m n * P p o       ∎
  where
  p = m ∸ n
  n+p≡m : n + p ≡ m
  n+p≡m = m+[n∸m]≡n n≤m
... | no  n≰m = begin-equality
  P m (n + o)         ≡⟨ n<k⇒P[n,k]≡0 m<n+o ⟩
  0                   ≡⟨⟩
  0 * P (m ∸ n) o     ≡⟨ sym $ cong (_* P (m ∸ n) o) $ n<k⇒P[n,k]≡0 m<n ⟩
  P m n * P (m ∸ n) o ∎
  where
  m<n : m < n
  m<n = ≰⇒> n≰m
  m<n+o : m < n + o
  m<n+o = begin-strict
    m     <⟨ m<n ⟩
    n     ≤⟨ m≤m+n n o ⟩
    n + o ∎

P-slide-∸ : ∀ m n o → P m n * P (m ∸ n) o ≡ P m o * P (m ∸ o) n
P-slide-∸ m n o = begin-equality
  P m n * P (m ∸ n) o ≡⟨ sym $ P-split-∸ m n o ⟩
  P m (n + o)         ≡⟨ cong (P m) $ +-comm n o ⟩
  P m (o + n)         ≡⟨ P-split-∸ m o n ⟩
  P m o * P (m ∸ o) n ∎

-- Properties of P and order relation
k≤n⇒1≤P[n,k] : ∀ {n k} → k ≤ n → 1 ≤ P n k
k≤n⇒1≤P[n,k] {n}        {.0}       z≤n               = ≤-refl
k≤n⇒1≤P[n,k] {.(suc n)} {.(suc k)} (s≤s {k} {n} k≤n) = begin
  1             ≤⟨ s≤s z≤n ⟩
  suc n         ≡⟨ sym $ *-identityʳ (suc n) ⟩
  suc n * 1     ≤⟨ *-monoʳ-≤ (suc n) (k≤n⇒1≤P[n,k] {n} {k} k≤n) ⟩
  suc n * P n k ∎

k≤n⇒P[n,k]≢0 : ∀ {n k} → k ≤ n → P n k ≢ 0
k≤n⇒P[n,k]≢0 {n} {k} k≤n P[n,k]≡0 = n≮n 0 $ subst (1 ≤_) P[n,k]≡0 $ k≤n⇒1≤P[n,k] k≤n

P[n,k]≡0⇒n<k : ∀ {n k} → P n k ≡ 0 → n < k
P[n,k]≡0⇒n<k {n} {k} P[n,k]≡0 with n <? k
... | yes n<k = n<k
... | no  n≮k = ⊥-elim $ k≤n⇒P[n,k]≢0 k≤n P[n,k]≡0
  where
  k≤n = ≮⇒≥ n≮k

P[n,k]≢0⇒k≤n : ∀ {n k} → P n k ≢ 0 → k ≤ n
P[n,k]≢0⇒k≤n {n} {k} P[n,k]≢0 with k ≤? n
... | yes k≤n = k≤n
... | no  k≰n = ⊥-elim $ P[n,k]≢0 $ n<k⇒P[n,k]≡0 n<k
  where
  n<k : n < k
  n<k = ≰⇒> k≰n

P-monoʳ-< : ∀ {n k r} → 2 ≤ n → r < n → k < r → P n k < P n r
P-monoʳ-< {suc zero} {k} {r} (s≤s ()) r<n k<r
P-monoʳ-< {n@(suc (suc n-2))} {k} {r} 2≤n r<n k<r = *-cancelʳ-< (P n k) (P n r) $ begin-strict
  P n k * (n ∸ k) ! ≡⟨ P[n,k]*[n∸k]!≡n! k≤n ⟩
  n !               ≡⟨ sym $ P[n,k]*[n∸k]!≡n! r≤n ⟩
  P n r * (n ∸ r) ! <⟨ Lemma.*-monoʳ-<′ (P n r) (fromWitnessFalse P[n,r]≢0)
                     (!-mono-<-≢0 {n ∸ r} {n ∸ k} {fromWitnessFalse n∸r≢0} n∸r<n∸k) ⟩
  P n r * (n ∸ k) ! ∎
  where
  k≤r = <⇒≤ k<r
  r≤n = <⇒≤ r<n
  k≤n = ≤-trans k≤r r≤n

  P[n,r]≢0 : P n r ≢ 0
  P[n,r]≢0 = k≤n⇒P[n,k]≢0 {n} {r} r≤n

  n∸r≢0 : n ∸ r ≢ 0
  n∸r≢0 = Lemma.m<n⇒n∸m≢0 r<n

  n∸r<n∸k : n ∸ r < n ∸ k
  n∸r<n∸k = Lemma.∸-monoʳ-< {k} {r} n r≤n k<r

{-
P-monoʳ-≤ : ∀ {n k r} → r ≤ n → k ≤ r → P n k ≤ P n r
P-monoʳ-≤ = ?
-}

P-monoˡ-< : ∀ {m n k} {wit : k ≠0} → k ≤ m → m < n → P m k < P n k
P-monoˡ-< {suc m} {suc n} {1}             {wit} k≤m (s≤s m<n) = s≤s $ begin-strict
  m * 1 ≡⟨ *-identityʳ m ⟩
  m     <⟨ m<n ⟩
  n     ≡⟨ sym $ *-identityʳ n ⟩
  n * 1 ∎
P-monoˡ-< {suc m} {suc n} {suc (suc k-1)} {wit} (s≤s k≤m) (s≤s m<n) = begin-strict
  suc m * P m (suc k-1) <⟨ *-mono-< (s≤s m<n) (P-monoˡ-< {m} {n} {suc k-1} {tt} k≤m m<n) ⟩
  suc n * P n (suc k-1) ∎

P-monoˡ-≤ : ∀ {m n} k → m ≤ n → P m k ≤ P n k
P-monoˡ-≤ {m} {n} 0       m≤n = ≤-refl
P-monoˡ-≤ {m} {n} k@(suc _) m≤n with k ≤? m
P-monoˡ-≤ {m} {n} k@(suc _) m≤n | yes k≤m with Lemma.≤⇒≡∨< m≤n
P-monoˡ-≤ {m} {n} k@(suc _) m≤n | yes k≤m | inj₁ refl = ≤-refl
P-monoˡ-≤ {m} {n} k@(suc _) m≤n | yes k≤m | inj₂ m<n  = <⇒≤ $ P-monoˡ-< k≤m m<n
P-monoˡ-≤ {m} {n} k@(suc _) m≤n | no k≰m = begin
  P m k ≡⟨ n<k⇒P[n,k]≡0 (≰⇒> k≰m) ⟩
  0     ≤⟨ z≤n ⟩
  P n k ∎

P[n,k]≤n^k : ∀ n k → P n k ≤ n ^ k
P[n,k]≤n^k n       0       = ≤-refl
P[n,k]≤n^k 0       (suc k) = ≤-refl
P[n,k]≤n^k (suc n) (suc k) = begin
  suc n * P n k     ≤⟨ *-monoʳ-≤ (suc n) $ P[n,k]≤n^k n k ⟩
  suc n * n ^ k     ≤⟨ *-monoʳ-≤ (suc n) $ Lemma.^-monoˡ-≤ k $ ≤-step ≤-refl ⟩
  suc n * suc n ^ k ≡⟨⟩
  suc n ^ suc k     ∎

k≤n⇒k!≤P[n,k] : ∀ {n k} → k ≤ n → k ! ≤ P n k
k≤n⇒k!≤P[n,k] {n}     {0}     k≤n       = ≤-refl
k≤n⇒k!≤P[n,k] {suc n} {suc k} (s≤s k≤n) = begin
  suc k * k !   ≤⟨ *-mono-≤ (s≤s k≤n) (k≤n⇒k!≤P[n,k] k≤n) ⟩
  suc n * P n k ∎

P[n,k]≤n! : ∀ n k → P n k ≤ n !
P[n,k]≤n! n       0       = 1≤n! n
P[n,k]≤n! 0       (suc k) = ≤-step ≤-refl
P[n,k]≤n! (suc n) (suc k) = begin
  suc n * P n k ≤⟨ *-monoʳ-≤ (suc n) (P[n,k]≤n! n k) ⟩
  suc n * n !   ∎

P[n,k]≡product[take[k,downFrom[1+n]]] :
  ∀ {n k} → k ≤ n → P n k ≡ product (take k (downFrom (suc n)))
P[n,k]≡product[take[k,downFrom[1+n]]] {n}     {zero}  k≤n       = refl
P[n,k]≡product[take[k,downFrom[1+n]]] {suc n} {suc k} (s≤s k≤n) = begin-equality
  suc n * P n k ≡⟨ cong (suc n *_) $ P[n,k]≡product[take[k,downFrom[1+n]]] k≤n ⟩
  suc n * product (take k (downFrom (suc n))) ∎

------------------------------------------------------------------------
-- Properties of CRec

-- proved by induction and P[1+n,1+k]≡[1+k]*P[n,k]+P[n,1+k]
CRec[n,k]*k!≡P[n,k] : ∀ n k → CRec n k * k ! ≡ P n k
CRec[n,k]*k!≡P[n,k] n       0       = refl
CRec[n,k]*k!≡P[n,k] 0       (suc k) = refl
CRec[n,k]*k!≡P[n,k] (suc n) (suc k) = begin-equality
  CRec (suc n) (suc k) * suc k !                      ≡⟨⟩
  (CRec n k + CRec n (suc k)) * (suc k * k !)         ≡⟨ Lemma.lemma₅ (CRec n k) (CRec n (suc k)) (suc k) (k !) ⟩
  suc k * (CRec n k * k !) + CRec n (suc k) * suc k ! ≡⟨ cong₂ _+_ (cong (suc k *_) $ CRec[n,k]*k!≡P[n,k] n k) (CRec[n,k]*k!≡P[n,k] n (suc k)) ⟩
  suc k * P n k + P n (suc k)                         ≡⟨ sym $ P[1+n,1+k]≡[1+k]*P[n,k]+P[n,1+k] n k ⟩
  P (suc n) (suc k)                                   ∎

CRec[n,k]≡P[n,k]/k! : ∀ n k → CRec n k ≡ _div_ (P n k) (k !) {False[n!≟0] k}
CRec[n,k]≡P[n,k]/k! n k = Lemma.m*n≡o⇒m≡o/n _ _ _ (False[n!≟0] k) (CRec[n,k]*k!≡P[n,k] n k)

------------------------------------------------------------------------
-- Properties of C

C≡CRec : ∀ n k → C n k ≡ CRec n k
C≡CRec n k = sym $ CRec[n,k]≡P[n,k]/k! n k

C[n,0]≡1 : ∀ n → C n 0 ≡ 1
C[n,0]≡1 n = begin-equality
  P n 0 div 1 ≡⟨ n/1≡n (P n 0) ⟩
  P n 0       ∎

C[0,1+k]≡0 : ∀ k → C 0 (suc k) ≡ 0
C[0,1+k]≡0 k = 0/n≡0 (suc k !)

C[1+n,1+k]≡C[n,k]+C[n,1+k] : ∀ n k → C (suc n) (suc k) ≡ C n k + C n (suc k)
C[1+n,1+k]≡C[n,k]+C[n,1+k] n k = begin-equality
  C (suc n) (suc k)         ≡⟨ C≡CRec (suc n) (suc k) ⟩
  CRec n k + CRec n (suc k) ≡⟨ sym $ cong₂ _+_ (C≡CRec n k) (C≡CRec n (suc k)) ⟩
  C n k + C n (suc k)       ∎

n<k⇒C[n,k]≡0 : ∀ {n k} → n < k → C n k ≡ 0
n<k⇒C[n,k]≡0 {n} {k} n<k = begin-equality
  (P n k div k !) {False[n!≟0] k} ≡⟨ cong (λ v → (v div k !) {False[n!≟0] k}) $ n<k⇒P[n,k]≡0 n<k ⟩
  (0 div k !) {False[n!≟0] k}     ≡⟨ 0/n≡0 (k !) ⟩
  0                               ∎

C[n,1]≡n : ∀ n → C n 1 ≡ n
C[n,1]≡n n = begin-equality
  P n 1 div 1 ≡⟨ n/1≡n (P n 1) ⟩
  P n 1       ≡⟨ P[n,1]≡n n ⟩
  n           ∎

C[n,n]≡1 : ∀ n → C n n ≡ 1
C[n,n]≡1 n = begin-equality
  (P n n div n !) {False[n!≟0] n} ≡⟨ cong (λ v → (v div n !) {False[n!≟0] n}) $ P[n,n]≡n! n ⟩
  (n ! div n !) {False[n!≟0] n}   ≡⟨ n/n≡1 (n !) ⟩
  1                               ∎

-- TODO prove directly
-- P n k ∣ k !
C[n,k]*k!≡P[n,k] : ∀ n k → C n k * k ! ≡ P n k
C[n,k]*k!≡P[n,k] n k = trans (cong (_* k !) (C≡CRec n k)) (CRec[n,k]*k!≡P[n,k] n k)

-- proved by C[n,k]*k!≡P[n,k] and P[m+n,n]*m!≡[m+n]!
C[m+n,n]*m!*n!≡[m+n]! : ∀ m n → C (m + n) n * m ! * n ! ≡ (m + n) !
C[m+n,n]*m!*n!≡[m+n]! m n = begin-equality
  C (m + n) n * m ! * n ! ≡⟨ Lemma.lemma₇ (C (m + n) n) (m !) (n !) ⟩
  C (m + n) n * n ! * m ! ≡⟨ cong (_* m !) $ C[n,k]*k!≡P[n,k] (m + n) n ⟩
  P (m + n) n * m !       ≡⟨ P[m+n,n]*m!≡[m+n]! m n ⟩
  (m + n) !               ∎

-- proved by C[m+n,n]*m!*n!≡[m+n]!
C[m+n,m]*m!*n!≡[m+n]! : ∀ m n → C (m + n) m * m ! * n ! ≡ (m + n) !
C[m+n,m]*m!*n!≡[m+n]! m n = begin-equality
  C (m + n) m * m ! * n ! ≡⟨ Lemma.lemma₇ (C (m + n) m) (m !) (n !) ⟩
  C (m + n) m * n ! * m ! ≡⟨ cong (λ v → C v m * n ! * m !) $ +-comm m n ⟩
  C (n + m) m * n ! * m ! ≡⟨ C[m+n,n]*m!*n!≡[m+n]! n m ⟩
  (n + m) !               ≡⟨ cong (_!) $ +-comm n m ⟩
  (m + n) !               ∎

C[n,k]*[n∸k]!*k!≡n! : ∀ {n k} → k ≤ n → C n k * (n ∸ k) ! * k ! ≡ n !
C[n,k]*[n∸k]!*k!≡n! {n} {k} k≤n = begin-equality
  C n k * m ! * k !       ≡⟨ cong (λ v → C v k * m ! * k !) $ sym $ m+k≡n ⟩
  C (m + k) k * m ! * k ! ≡⟨ C[m+n,n]*m!*n!≡[m+n]! m k ⟩
  (m + k) !               ≡⟨ cong (_!) $ m+k≡n ⟩
  n !                     ∎
  where
  m = n ∸ k
  m+k≡n : m + k ≡ n
  m+k≡n = m∸n+n≡m k≤n

private
  -- False[m!*n!≟0]
  proof : ∀ m n → False ((m ! * n !) ≟ 0)
  proof m n = fromWitnessFalse $ Lemma.*-pres-≢0 (n!≢0 m) (n!≢0 n)

C[n,k]≡n!/[[n∸k]!*k!] : ∀ {n k} → k ≤ n →
  C n k ≡ _div_ (n !) ((n ∸ k) ! * k !) {proof (n ∸ k) k}
C[n,k]≡n!/[[n∸k]!*k!] {n} {k} k≤n = Lemma.m*n≡o⇒m≡o/n
  (C n k) ((n ∸ k) ! * k !) (n !) (proof (n ∸ k) k) $ begin-equality
    C n k * ((n ∸ k) ! * k !) ≡⟨ sym $ *-assoc (C n k) ((n ∸ k) !) (k !) ⟩
    C n k * (n ∸ k) ! * k !   ≡⟨ C[n,k]*[n∸k]!*k!≡n! k≤n ⟩
    n !                       ∎

-- proved by C[m+n,n]*m!*n!≡[m+n]! and C[m+n,m]*m!*n!≡[m+n]!
C-inv : ∀ m n → C (m + n) n ≡ C (m + n) m
C-inv m n =
  Lemma.*-cancelʳ-≡′ (C (m + n) n) (C (m + n) m) (False[n!≟0] m) $
  Lemma.*-cancelʳ-≡′ (C (m + n) n * m !) (C (m + n) m * m !) (False[n!≟0] n) $ begin-equality
    C (m + n) n * m ! * n ! ≡⟨ C[m+n,n]*m!*n!≡[m+n]! m n ⟩
    (m + n) !               ≡⟨ sym $ C[m+n,m]*m!*n!≡[m+n]! m n ⟩
    C (m + n) m * m ! * n ! ∎

C-inv-∸ : ∀ {n k} → k ≤ n → C n k ≡ C n (n ∸ k)
C-inv-∸ {n} {k} k≤n = begin-equality
  C n k       ≡⟨ cong (λ v → C v k) $ sym $ m+k≡n ⟩
  C (m + k) k ≡⟨ C-inv m k ⟩
  C (m + k) m ≡⟨ cong (λ v → C v m) $ m+k≡n ⟩
  C n (n ∸ k) ∎
  where
  m = n ∸ k
  m+k≡n : m + k ≡ n
  m+k≡n = m∸n+n≡m k≤n

C[m+n,1+n]*[1+n]≡C[m+n,n]*m : ∀ m n → C (m + n) (suc n) * suc n ≡ C (m + n) n * m
C[m+n,1+n]*[1+n]≡C[m+n,n]*m m n =
  Lemma.*-cancelʳ-≡′ (C (m + n) (suc n) * suc n) (C (m + n) n * m) (False[n!≟0] n) $ begin-equality
  C (m + n) (suc n) * suc n * n ! ≡⟨ *-assoc (C (m + n) (suc n)) (suc n) (n !) ⟩
  C (m + n) (suc n) * suc n !     ≡⟨ C[n,k]*k!≡P[n,k] (m + n) (suc n) ⟩
  P (m + n) (suc n)               ≡⟨ P[m+n,1+n]≡P[m+n,n]*m m n ⟩
  P (m + n) n * m                 ≡⟨ cong (_* m) $ sym $ C[n,k]*k!≡P[n,k] (m + n) n ⟩
  (C (m + n) n * n !) * m         ≡⟨ Lemma.lemma₇ (C (m + n) n) (n !) m ⟩
  C (m + n) n * m * n !           ∎

-- C n k = ((n + 1 - k) / k) * C n (k - 1)
C[n,1+k]*[1+k]≡C[n,k]*[n∸k] : ∀ {n k} → k ≤ n → C n (suc k) * suc k ≡ C n k * (n ∸ k)
C[n,1+k]*[1+k]≡C[n,k]*[n∸k] {n} {k} k≤n = begin-equality
  C n (suc k) * suc k       ≡⟨ cong (λ v → C v (suc k) * suc k) (sym m+k≡n) ⟩
  C (m + k) (suc k) * suc k ≡⟨ C[m+n,1+n]*[1+n]≡C[m+n,n]*m m k ⟩
  C (m + k) k * m           ≡⟨ cong (λ v → C v k * m) m+k≡n ⟩
  C n k * (n ∸ k)           ∎
  where
  m = n ∸ k
  m+k≡n : m + k ≡ n
  m+k≡n = m∸n+n≡m k≤n

-- C n k ≡ (n / k) * C (n - 1) (k - 1)
-- proved by C[n,k]*k!≡P[n,k]
[1+k]*C[1+n,1+k]≡[1+n]*C[n,k] : ∀ n k → suc k * C (suc n) (suc k) ≡ suc n * C n k
[1+k]*C[1+n,1+k]≡[1+n]*C[n,k] n k = Lemma.*-cancelʳ-≡′ (suc k * C (suc n) (suc k)) (suc n * C n k) (False[n!≟0] k) $ begin-equality
  suc k * C (suc n) (suc k) * k ! ≡⟨ sym $ Lemma.lemma₈ (C (suc n) (suc k)) (suc k) (k !) ⟩
  C (suc n) (suc k) * (suc k) !   ≡⟨ C[n,k]*k!≡P[n,k] (suc n) (suc k) ⟩
  P (suc n) (suc k)               ≡⟨⟩
  suc n * P n k                   ≡⟨ cong (suc n *_) $ sym $ C[n,k]*k!≡P[n,k] n k ⟩
  suc n * (C n k * k !)           ≡⟨ sym $ *-assoc (suc n) (C n k) (k !) ⟩
  suc n * C n k * k !             ∎

-- 両辺に n ! * o ! を右から掛ける
C[m,n]*C[m∸n,o]≡C[m,o]*C[m∸o,n] : ∀ m n o → C m n * C (m ∸ n) o ≡ C m o * C (m ∸ o) n
C[m,n]*C[m∸n,o]≡C[m,o]*C[m∸o,n] m n o =
  Lemma.*-cancelʳ-≡′ (C m n * C (m ∸ n) o) (C m o * C (m ∸ o) n) (False[n!≟0] n) $
  Lemma.*-cancelʳ-≡′ (C m n * C (m ∸ n) o * n !) (C m o * C (m ∸ o) n * n !) (False[n!≟0] o) $ begin-equality
  C m n * C (m ∸ n) o * n ! * o !     ≡⟨ Lemma.lemma₁₀ (C m n) (C (m ∸ n) o) (n !) (o !) ⟩
  (C m n * n !) * (C (m ∸ n) o * o !) ≡⟨ cong₂ _*_ (C[n,k]*k!≡P[n,k] m n) (C[n,k]*k!≡P[n,k] (m ∸ n) o) ⟩
  P m n * P (m ∸ n) o                 ≡⟨ P-slide-∸ m n o ⟩
  P m o * P (m ∸ o) n                 ≡⟨ sym $ cong₂ _*_ (C[n,k]*k!≡P[n,k] m o) (C[n,k]*k!≡P[n,k] (m ∸ o) n) ⟩
  (C m o * o !) * (C (m ∸ o) n * n !) ≡⟨ Lemma.lemma₁₁ (C m o) (o !) (C (m ∸ o) n) (n !) ⟩
  C m o * C (m ∸ o) n * n ! * o !     ∎

k≤n⇒1≤C[n,k] : ∀ {n k} → k ≤ n → 1 ≤ C n k
k≤n⇒1≤C[n,k] {n} {k} k≤n = Lemma.*-cancelʳ-≤′ 1 (C n k) (False[n!≟0] k) $ begin
  1 * k !     ≡⟨ *-identityˡ (k !) ⟩
  k !         ≤⟨ k≤n⇒k!≤P[n,k] k≤n ⟩
  P n k       ≡⟨ sym $ C[n,k]*k!≡P[n,k] n k ⟩
  C n k * k ! ∎

k≤n⇒C[n,k]≢0 : ∀ {n k} → k ≤ n → C n k ≢ 0
k≤n⇒C[n,k]≢0 {n} {k} k≤n C[n,k]≡0 = n≮n 0 $ subst (1 ≤_) C[n,k]≡0 $ k≤n⇒1≤C[n,k] k≤n

C[n,k]≡0⇒n<k : ∀ {n k} → C n k ≡ 0 → n < k
C[n,k]≡0⇒n<k {n} {k} C[n,k]≡0 with n <? k
... | yes n<k = n<k
... | no  n≮k = ⊥-elim $ k≤n⇒C[n,k]≢0 (≮⇒≥ n≮k) C[n,k]≡0

C[n,k]≢0⇒k≤n : ∀ {n k} → C n k ≢ 0 → k ≤ n
C[n,k]≢0⇒k≤n {n} {k} C[n,k]≢0 with k ≤? n
... | yes k≤n = k≤n
... | no  k≰n = ⊥-elim $ C[n,k]≢0 $ n<k⇒C[n,k]≡0 (≰⇒> k≰n)

------------------------------------------------------------------------
-- Properties of double factorial

!!-! : ∀ n → suc n !! * n !! ≡ suc n !
!!-! 0             = refl
!!-! 1             = refl
!!-! (suc (suc n)) = begin-equality
  (3 + n) !! * (2 + n) !!                 ≡⟨⟩
  (3 + n) * (1 + n) !! * ((2 + n) * n !!) ≡⟨ Lemma.lemma₉ (3 + n) (suc n !!) (2 + n) (n !!) ⟩
  (3 + n) * (2 + n) * ((1 + n) !! * n !!) ≡⟨ cong ((3 + n) * (2 + n) *_) $ !!-! n ⟩
  (3 + n) * (2 + n) * (suc n !)           ≡⟨ *-assoc (3 + n) (2 + n) (suc n !) ⟩
  (3 + n) !                               ∎

[2*n]!!≡n!*2^n : ∀ n → (2 * n) !! ≡ n ! * 2 ^ n
[2*n]!!≡n!*2^n 0       = refl
[2*n]!!≡n!*2^n (suc n) = begin-equality
  (2 * (1 + n)) !!              ≡⟨ cong (_!!) $ *-distribˡ-+ 2 1 n ⟩
  (2 + (2 * n)) !!              ≡⟨⟩
  (2 + 2 * n) * (2 * n) !!      ≡⟨ cong ((2 + 2 * n) *_) $ [2*n]!!≡n!*2^n n ⟩
  (2 + 2 * n) * (n ! * 2 ^ n)   ≡⟨ cong (_* (n ! * 2 ^ n)) $ trans (sym $ *-distribˡ-+ 2 1 n) (*-comm 2 (suc n)) ⟩
  (suc n * 2) * ((n !) * 2 ^ n) ≡⟨ Lemma.lemma₉ (suc n) 2 (n !) (2 ^ n) ⟩
  (suc n) ! * 2 ^ suc n         ∎

------------------------------------------------------------------------
-- Properties of unsigned Stirling number of the first kind

n<k⇒S1[n,k]≡0 : ∀ {n k} → n < k → S1 n k ≡ 0
n<k⇒S1[n,k]≡0 {0}     {.(suc _)} (s≤s n<k)         = refl
n<k⇒S1[n,k]≡0 {suc n} {.(suc m)} (s≤s {_} {m} n<k) = begin-equality
  n * S1 n (suc m) + S1 n m ≡⟨ cong₂ _+_ (cong (n *_) $ n<k⇒S1[n,k]≡0 (≤-step n<k)) (n<k⇒S1[n,k]≡0 n<k) ⟩
  n * 0 + 0                 ≡⟨ cong (_+ 0) $ *-zeroʳ n ⟩
  0                         ∎

S1[1+n,1]≡n! : ∀ n → S1 (suc n) 1 ≡ n !
S1[1+n,1]≡n! 0       = refl
S1[1+n,1]≡n! (suc n) = begin-equality
  suc n * S1 (suc n) 1 + S1 (suc n) 0 ≡⟨⟩
  suc n * S1 (suc n) 1 + 0            ≡⟨ +-identityʳ (suc n * S1 (suc n) 1) ⟩
  suc n * S1 (suc n) 1                ≡⟨ cong (suc n *_) $ S1[1+n,1]≡n! n ⟩
  (suc n) !                           ∎

S1[n,n]≡1 : ∀ n → S1 n n ≡ 1
S1[n,n]≡1 0       = refl
S1[n,n]≡1 (suc n) = begin-equality
  n * S1 n (suc n) + S1 n n ≡⟨ cong₂ _+_ (cong (n *_) $ n<k⇒S1[n,k]≡0 {n} {suc n} ≤-refl) (S1[n,n]≡1 n) ⟩
  n * 0 + 1                 ≡⟨ cong (_+ 1) $ *-zeroʳ n ⟩
  1                         ∎

S1[1+n,n]≡C[1+n,2] : ∀ n → S1 (suc n) n ≡ C (suc n) 2
S1[1+n,n]≡C[1+n,2] 0       = refl
S1[1+n,n]≡C[1+n,2] (suc n) = begin-equality
  S1 (suc (suc n)) (suc n)                  ≡⟨⟩
  suc n * S1 (suc n) (suc n) + S1 (suc n) n ≡⟨ cong₂ _+_ (cong (suc n *_) (S1[n,n]≡1 (suc n))) (S1[1+n,n]≡C[1+n,2] n) ⟩
  suc n * 1 + C (suc n) 2                   ≡⟨ cong (_+ C (suc n) 2) lemma ⟩
  C (suc n) 1 + C (suc n) 2                 ≡⟨ sym $ C[1+n,1+k]≡C[n,k]+C[n,1+k] (suc n) 1 ⟩
  C (suc (suc n)) 2                         ∎
  where
  lemma : suc n * 1 ≡ C (suc n) 1
  lemma = trans (*-identityʳ (suc n)) (sym $ C[n,1]≡n (suc n))

------------------------------------------------------------------------
-- Properties of Stirling number of the second kind

n<k⇒S2[n,k]≡0 : ∀ {n k} → n < k → S2 n k ≡ 0
n<k⇒S2[n,k]≡0 {.0}       {.(suc _)}       (s≤s z≤n)               = refl
n<k⇒S2[n,k]≡0 {.(suc _)} {.(suc (suc _))} (s≤s (s≤s {n} {k} n≤k)) = begin-equality
  S2 (suc n) (suc (suc k))      ≡⟨⟩
  2+k * S2 n 2+k + S2 n (suc k) ≡⟨ cong₂ _+_ (cong (2+k *_) (n<k⇒S2[n,k]≡0 n<2+k)) (n<k⇒S2[n,k]≡0 n<1+k) ⟩
  2+k * 0 + 0                   ≡⟨ cong (_+ 0) $ *-zeroʳ 2+k ⟩
  0                             ∎
  where
  2+k = suc (suc k)
  n<1+k : n < suc k
  n<1+k = s≤s n≤k
  n<2+k : n < suc (suc k)
  n<2+k = ≤-step n<1+k

S2[n,n]≡1 : ∀ n → S2 n n ≡ 1
S2[n,n]≡1 0       = refl
S2[n,n]≡1 (suc n) = begin-equality
  suc n * S2 n (suc n) + S2 n n ≡⟨ cong₂ _+_ (cong (suc n *_) (n<k⇒S2[n,k]≡0 {n} {suc n} ≤-refl)) (S2[n,n]≡1 n) ⟩
  suc n * 0 + 1                 ≡⟨ cong (_+ 1) $ *-zeroʳ (suc n) ⟩
  1                             ∎

S2[1+n,n]≡C[n,2] : ∀ n → S2 (suc n) n ≡ C (suc n) 2
S2[1+n,n]≡C[n,2] 0       = refl
S2[1+n,n]≡C[n,2] (suc n) = begin-equality
  S2 (suc (suc n)) (suc n)                  ≡⟨⟩
  suc n * S2 (suc n) (suc n) + S2 (suc n) n ≡⟨ cong₂ _+_ (cong (suc n *_) (S2[n,n]≡1 (suc n))) (S2[1+n,n]≡C[n,2] n) ⟩
  suc n * 1 + C (suc n) 2                   ≡⟨ cong (_+ C (suc n) 2) lemma ⟩
  C (suc n) 1 + C (suc n) 2                 ≡⟨ sym $ C[1+n,1+k]≡C[n,k]+C[n,1+k] (suc n) 1 ⟩
  C (suc (suc n)) 2                         ∎
  where
  lemma : suc n * 1 ≡ C (suc n) 1
  lemma = trans (*-identityʳ (suc n)) (sym $ C[n,1]≡n (suc n))

{-
1+S2[1+n,2]≡2^n : ∀ n → 1 + S2 (suc n) 2 ≡ 2 ^ n
1+S2[1+n,2]≡2^n 0       = refl
1+S2[1+n,2]≡2^n (suc n) = {!   !}
-}

------------------------------------------------------------------------
-- Properties of Lah number

L[0,k]≡0 : ∀ k → L 0 k ≡ 0
L[0,k]≡0 0       = refl
L[0,k]≡0 (suc k) = refl

L-rec : ∀ n k → L (suc n) (suc (suc k)) ≡ (n + suc (suc k)) * L n (suc (suc k)) + L n (suc k)
L-rec 0       k = sym $ trans (+-identityʳ (k * 0)) (*-zeroʳ k)
L-rec (suc n) k = refl

{-
n<k⇒L[n,k]≡0 : ∀ {n k} → n < k → L n k ≡ 0
n<k⇒Lnk≡0 (s≤s z≤n)       = refl
n<k⇒Lnk≡0 {.(suc (suc n))} {.(suc (suc k))} (s≤s (s≤s {suc n} {k} n<k)) = begin
  (L (suc n) (suc (suc k)) + (n + suc (suc k)) * L (suc n) (suc (suc k))) + L (suc n) (suc k)
    ≡⟨ cong₂ _+_ (cong₂ _+_ lemma (cong ((n + suc (suc k)) *_) {!   !}))n<k⇒L[n,k]≡0 (s≤s n<k)) ⟩
  0 + (n + suc (suc k)) * 0 + 0 ≡⟨ {!   !} ⟩
  0 ∎
  where
  lemma : L (suc n) (suc (suc k)) ≡ 0
  lemma = n<k⇒L[n,k]≡0 (≤-step (s≤s n<k))

L[n,n] : ∀ n → L (suc n) (suc n) ≡ 1
L[n,n] 0       = refl
L[n,n] (suc n) = {!   !}
-}
------------------------------------------------------------------------
-- Properties of Pochhammer symbol

Poch[0,1+k]≡0 : ∀ k → Poch 0 (suc k) ≡ 0
Poch[0,1+k]≡0 k = refl

Poch[n,1]≡n : ∀ n → Poch n 1 ≡ n
Poch[n,1]≡n 0       = refl
Poch[n,1]≡n (suc n) = cong suc (*-identityʳ n)

Poch[1+n,k]*n!≡[n+k]! : ∀ n k → Poch (suc n) k * n ! ≡ (n + k) !
Poch[1+n,k]*n!≡[n+k]! n 0       = trans (+-identityʳ (n !)) (sym $ cong (_!) $ +-identityʳ n)
Poch[1+n,k]*n!≡[n+k]! n (suc k) = begin-equality
  Poch (suc n) (suc k) * n !         ≡⟨⟩
  suc n * Poch (suc (suc n)) k * n ! ≡⟨ Lemma.lemma₁₂ (suc n) (Poch (suc (suc n)) k) (n !) ⟩
  Poch (suc (suc n)) k * (suc n) !   ≡⟨ Poch[1+n,k]*n!≡[n+k]! (suc n) k ⟩
  (suc n + k) !                      ≡⟨ sym $ cong (_!) $ +-suc n k ⟩
  (n + suc k) !                      ∎

Poch[1,k]≡k! : ∀ k → Poch 1 k ≡ k !
Poch[1,k]≡k! k = Lemma.*-cancelʳ-≡′ (Poch 1 k) (k !) {1 !} tt $ begin-equality
  Poch 1 k * 1 ! ≡⟨ Poch[1+n,k]*n!≡[n+k]! 0 k ⟩
  k !            ≡⟨ sym $ *-identityʳ (k !) ⟩
  k ! * 1 !      ∎

Poch[1+m,n]≡P[m+n,n] : ∀ m n → Poch (suc m) n ≡ P (m + n) n
Poch[1+m,n]≡P[m+n,n] m n = Lemma.*-cancelʳ-≡′ (Poch (suc m) n) (P (m + n) n) (False[n!≟0] m) $ begin-equality
  Poch (suc m) n * m ! ≡⟨ Poch[1+n,k]*n!≡[n+k]! m n ⟩
  (m + n) !            ≡⟨ sym $ P[m+n,n]*m!≡[m+n]! m n ⟩
  P (m + n) n * m !    ∎

Poch[n,k]≡P[n+k∸1,n] : ∀ n k → Poch n k ≡ P (n + k ∸ 1) k
Poch[n,k]≡P[n+k∸1,n] 0       0       = refl
Poch[n,k]≡P[n+k∸1,n] 0       (suc k) = sym $ n<k⇒P[n,k]≡0 {k} {suc k} ≤-refl
Poch[n,k]≡P[n+k∸1,n] (suc n) k       = begin-equality
  Poch (suc n) k      ≡⟨ Poch[1+m,n]≡P[m+n,n] n k ⟩
  P (n + k) k         ≡⟨⟩
  P (suc n + k ∸ 1) k ∎

Poch[1+[n∸k],k]≡P[n,k] : ∀ {n k} → k ≤ n → Poch (suc (n ∸ k)) k ≡ P n k
Poch[1+[n∸k],k]≡P[n,k] {n} {k} k≤n = begin-equality
  Poch (suc m) k ≡⟨ Poch[1+m,n]≡P[m+n,n] m k ⟩
  P (m + k) k    ≡⟨ cong (λ v → P v k) m+k≡n ⟩
  P n k          ∎
  where
  m = n ∸ k
  m+k≡n = m∸n+n≡m k≤n

Poch-split : ∀ m n o → Poch m (n + o) ≡ Poch m n * Poch (m + n) o
Poch-split m 0       o = begin-equality
  Poch m o           ≡⟨ sym $ cong (λ v → Poch v o) $ +-identityʳ m ⟩
  Poch (m + 0) o     ≡⟨ sym $ +-identityʳ (Poch (m + 0) o) ⟩
  Poch (m + 0) o + 0 ∎
Poch-split m (suc n) o = begin-equality
  m * Poch (suc m) (n + o)                  ≡⟨ cong (m *_) $ Poch-split (suc m) n o ⟩
  m * (Poch (suc m) n * Poch (suc m + n) o) ≡⟨ sym $ *-assoc m (Poch (suc m) n) (Poch (suc m + n) o) ⟩
  m * Poch (suc m) n * Poch (suc m + n) o   ≡⟨ cong (λ v → m * Poch (suc m) n * Poch v o) $ sym $ +-suc m n ⟩
  m * Poch (suc m) n * Poch (m + suc n) o   ∎

{-
------------------------------------------------------------------
-- Properties of Multinomial coefficient
MC[xs]≡sum[xs]!/product[map[!]xs] :
  ∀ xs → MC xs ≡ _div_ (sum xs !) (product (List.map (_!) xs)) {?}
MC[xs]≡sum[xs]!/product[map[!]xs] [] = refl
MC[xs]≡sum[xs]!/product[map[!]xs] (x ∷ []) = ?
MC[xs]≡sum[xs]!/product[map[!]xs] (x ∷ x₁ ∷ xs) = ?
-}
