------------------------------------------------------------------------
-- Binomial theorem
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --exact-split #-}

module Math.BinomialTheorem.Nat where

-- agda-stdlib
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Solver
open import Relation.Binary.PropositionalEquality
open import Function

-- agda-combinatorics
open import Math.Combinatorics.Function
open import Math.Combinatorics.Function.Properties

-- agda-misc
open import Math.NumberTheory.Summation.Nat
open import Math.NumberTheory.Summation.Nat.Properties

open ≤-Reasoning

private
  lemma₁ : ∀ x y n k → x * (C n k * (x ^ k * y ^ (n ∸ k))) ≡
                       C n k * (x ^ suc k * y ^ (n ∸ k))
  lemma₁ x y n k = solve 4 (λ m n o p → m :* (n :* (o :* p)) :=
      n :* (m :* o :* p)) refl x (C n k) (x ^ k) (y ^ (n ∸ k))
    where open +-*-Solver

  lemma₂ : ∀ x y n k → y * (C n k * (x ^ k * y ^ (n ∸ k))) ≡
                       C n k * (x ^ k * y ^ suc (n ∸ k))
  lemma₂ x y n k = solve 4 (λ m n o p → m :* (n :* (o :* p)) :=
    n :* (o :* (m :* p)) ) refl y (C n k) (x ^ k) (y ^ (n ∸ k))
    where open +-*-Solver

  glemma₃ : ∀ x y m n → C m m * (x ^ suc n * y ^ (n ∸ n)) ≡ x ^ suc n
  glemma₃ x y m n = begin-equality
    C m m * (x ^ suc n * y ^ (n ∸ n))
      ≡⟨ cong₂ (λ u v → u * (x ^ suc n * y ^ v)) (C[n,n]≡1 m) (n∸n≡0 n) ⟩
    1 * (x ^ suc n * 1)
      ≡⟨ *-identityˡ (x ^ suc n * 1) ⟩
    x ^ suc n * 1
      ≡⟨ *-identityʳ (x ^ suc n) ⟩
    x ^ suc n
      ∎

  lemma₃ : ∀ x y n → C n n * (x ^ suc n * y ^ (n ∸ n)) ≡ x ^ suc n
  lemma₃ x y n = glemma₃ x y n n

  lemma₄ : ∀ {k n} → k < n → suc (n ∸ suc k) ≡ suc n ∸ suc k
  lemma₄ k<n = sym $ +-∸-assoc 1 k<n

  lemma₅ : ∀ n → 1 * (1 * n) ≡ n
  lemma₅ n = trans (*-identityˡ (1 * n)) (*-identityˡ n)

  lemma₆ : ∀ x y n → C (suc n) (suc n) * (x ^ suc n * y ^ (n ∸ n)) ≡ x ^ suc n
  lemma₆ x y n = glemma₃ x y (suc n) n

  lemma₇ : ∀ m n o p → m + n + (o + p) ≡ n + o + (m + p)
  lemma₇ = solve 4 (λ m n o p → m :+ n :+ (o :+ p) := n :+ o :+ (m :+ p) ) refl
    where open +-*-Solver

  lemma₈ : ∀ m n o → m + n + o ≡ n + (o + m)
  lemma₈ = solve 3 (λ m n o → m :+ n :+ o := n :+ (o :+ m)) refl
    where open +-*-Solver

theorem : ∀ x y n →
  (x + y) ^ n ≡ Σ[ k ≤ n ] (C n k * (x ^ k * y ^ (n ∸ k)))
theorem x y 0       = begin-equality
  C 0 0 * ((x ^ 0) * y ^ (0 ∸ 0))
    ≡⟨ sym $ Σ≤[0,f]≈f[0] (λ k → C 0 k * (x ^ k * y ^ (0 ∸ k))) ⟩
  Σ≤ 0 (λ k → C 0 k * (x ^ k * y ^ (0 ∸ k)))
    ∎
theorem x y (suc n) = begin-equality
  (x + y) * (x + y) ^ n
    ≡⟨ cong ((x + y) *_) $ theorem x y n ⟩
  (x + y) * Σ[ k ≤ n ] (C n k * (x ^ k * y ^ (n ∸ k)))
    ≡⟨ *-distribʳ-+ (Σ[ k ≤ n ] (C n k * (x ^ k * y ^ (n ∸ k)))) x y ⟩
  x * Σ[ k ≤ n ] (C n k * (x ^ k * y ^ (n ∸ k))) + y * Σ[ k ≤ n ] (C n k * (x ^ k * y ^ (n ∸ k)))
    ≡⟨ sym $ cong₂ _+_ (Σ≤-*-commute n x (λ k → C n k * (x ^ k * y ^ (n ∸ k)))) (Σ≤-*-commute n y (λ k → C n k * (x ^ k * y ^ (n ∸ k)))) ⟩
  Σ[ k ≤ n ] (x * (C n k * (x ^ k * y ^ (n ∸ k)))) + Σ[ k ≤ n ] (y * (C n k * (x ^ k * y ^ (n ∸ k))))
    ≡⟨ cong₂ _+_ (Σ≤-congˡ n (λ k → lemma₁ x y n k)) (Σ≤-congˡ n (λ k → lemma₂ x y n k)) ⟩
  Σ[ k ≤ n ] (C n k * ((x ^ suc k) * y ^ (n ∸ k))) + Σ[ k ≤ n ] (C n k * (x ^ k * y ^ suc (n ∸ k)))
    ≡⟨ cong (Σ[ k ≤ n ] (C n k * (x ^ suc k * y ^ (n ∸ k))) +_) $ Σ<-push-suc n (λ k → C n k * (x ^ k * y ^ suc (n ∸ k))) ⟩
  Σ[ k < n ] (C n k * ((x ^ suc k) * y ^ (n ∸ k))) + C n n * ((x ^ suc n) * y ^ (n ∸ n))
    + (C n 0 * (x ^ 0 * y ^ (suc (n ∸ 0))) + Σ[ k < n ] (C n (suc k) * (x ^ suc k * y ^ suc (n ∸ suc k))))
    ≡⟨⟩
  Σ[ k < n ] (C n k * ((x ^ suc k) * y ^ (n ∸ k))) + C n n * ((x ^ suc n) * y ^ (n ∸ n))
    + (1 * (1 * y ^ suc n) + Σ[ k < n ] (C n (suc k) * (x ^ suc k * y ^ suc (n ∸ suc k))))
    ≡⟨ cong₂ _+_ (cong (Σ[ k < n ] (C n k * (x ^ suc k * y ^ (n ∸ k))) +_) $ lemma₃ x y n)
                 (cong₂ _+_ (lemma₅ (y ^ suc n))
                    (Σ<-congˡ-with-< n $ λ k k<n → cong (λ v → C n (suc k) * (x ^ suc k * y ^ v)) $ lemma₄ k<n)) ⟩
  Σ[ k < n ] (C n k * (x ^ suc k * y ^ (n ∸ k))) + x ^ suc n
    + (y ^ suc n + Σ[ k < n ] (C n (suc k) * (x ^ suc k * y ^ (n ∸ k))))
    ≡⟨ lemma₇ (Σ[ k < n ] (C n k * (x ^ suc k * y ^ (n ∸ k)))) (x ^ suc n) (y ^ suc n) (Σ[ k < n ] (C n (suc k) * (x ^ suc k * y ^ (n ∸ k)))) ⟩
  x ^ suc n + y ^ suc n + (Σ[ k < n ] (C n k * (x ^ suc k * y ^ (n ∸ k))) +
                          Σ[ k < n ] (C n (suc k) * (x ^ suc k * y ^ (n ∸ k))))
   ≡⟨ cong (λ v → (x ^ suc n + y ^ suc n) + v) $ lemma ⟩
  x ^ suc n + y ^ suc n + Σ[ k < n ] (C (suc n) (suc k) * (x ^ suc k * y ^ (n ∸ k)))
    ≡⟨ lemma₈ (x ^ suc n) (y ^ suc n) (Σ[ k < n ] (C (suc n) (suc k) * (x ^ suc k * y ^ (n ∸ k)))) ⟩
  y ^ suc n + (Σ[ k < n ] (C (suc n) (suc k) * (x ^ suc k * y ^ (n ∸ k))) + x ^ suc n)
    ≡⟨ cong (λ v → y ^ suc n + (Σ[ k < n ] (C (suc n) (suc k) * (x ^ suc k * y ^ (n ∸ k))) + v)) $ sym $ lemma₆ x y n ⟩
  y ^ suc n + (Σ[ k < n ] (C (suc n) (suc k) * (x ^ suc k * y ^ (n ∸ k))) + C (suc n) (suc n) * (x ^ suc n * y ^ (n ∸ n)))
    ≡⟨⟩
  y ^ suc n + Σ[ k ≤ n ] (C (suc n) (suc k) * (x ^ suc k * y ^ (n ∸ k)))
   ≡⟨ cong (_+ Σ[ k ≤ n ] (C (suc n) (suc k) * (x ^ suc k * y ^ (n ∸ k)))) $ sym $ lemma₅ (y ^ suc n) ⟩
  1 * (1 * y ^ suc n) + Σ[ k ≤ n ] (C (suc n) (suc k) * (x ^ suc k * y ^ (n ∸ k)))
   ≡⟨ sym $ Σ≤-push-suc n (λ k → C (suc n) k * (x ^ k * y ^ (suc n ∸ k))) ⟩
  Σ≤ (suc n) (λ k → C (suc n) k * (x ^ k * y ^ (suc n ∸ k)))
    ∎
  where
  lemma : Σ[ k < n ] (C n k * (x ^ suc k * y ^ (n ∸ k))) +
          Σ[ k < n ] (C n (suc k) * (x ^ suc k * y ^ (n ∸ k))) ≡
          Σ[ k < n ] (C (suc n) (suc k) * (x ^ suc k * y ^ (n ∸ k)))
  lemma = begin-equality
    Σ[ k < n ] (C n k * z k) + Σ[ k < n ] (C n (suc k) * z k)
      ≡⟨ sym $ Σ<-distrib-+ n (λ k → C n k * z k) (λ k → C n (suc k) * z k) ⟩
    Σ[ k < n ] (C n k * z k + C n (suc k) * z k)
      ≡⟨ Σ<-congˡ n (λ k → sym $ *-distribʳ-+ (z k) (C n k) (C n (suc k))) ⟩
    Σ[ k < n ] ((C n k + C n (suc k)) * z k)
      ≡⟨ Σ<-congˡ n (λ k → cong (_* z k) $ sym $ C[1+n,1+k]≡C[n,k]+C[n,1+k] n k) ⟩
    Σ[ k < n ] (C (suc n) (suc k) * z k) ∎
    where
    z = λ k → x ^ suc k * y ^ (n ∸ k)

Σ[k≤n]C[n,k]≡2^n : ∀ n → Σ[ k ≤ n ] C n k ≡ 2 ^ n
Σ[k≤n]C[n,k]≡2^n n = begin-equality
  Σ[ k ≤ n ] (C n k)
    ≡⟨ sym $ Σ≤-congˡ n (λ k → begin-equality
        C n k * (1 ^ k * 1 ^ (n ∸ k)) ≡⟨ cong (C n k *_) $ cong₂ _*_ (^-zeroˡ k) (^-zeroˡ (n ∸ k)) ⟩
        C n k * (1 * 1) ≡⟨ *-identityʳ (C n k) ⟩
        C n k ∎ ) ⟩
  Σ[ k ≤ n ] (C n k * (1 ^ k * 1 ^ (n ∸ k)))
    ≡⟨ sym $ theorem 1 1 n ⟩
  (1 + 1) ^ n
    ∎
