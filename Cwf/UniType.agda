module Cwf.UniType where

open import Base.Core using (_,_)
open import Base.FinFun

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Size

data _∨_ (A B : Set) : Set where
  inl : A → A ∨ B
  inr : B → A ∨ B

data _∧_ (A B : Set) : Set where
  ∧-intro : A → B → A ∧ B

data absurd : Set where

data Nbh : Size → Set where
  ⊥ : ∀ {i} → Nbh i
  0ₙ : ∀ {i} → Nbh i
  sᵤ : ∀ {i} → Nbh i → Nbh i
  ℕ : ∀ {i} → Nbh i
  𝒰 : ∀ {i} → Nbh i
  λᵤ : ∀ {i} → FinFun (Nbh i) (Nbh i) → Nbh (↑ i)
  Π : ∀ {i} → Nbh i → FinFun (Nbh i) (Nbh i) → Nbh (↑ i)

sameBranch : ∀ {i} → Nbh i → Nbh i → Bool
sameBranch ⊥ y = true
sameBranch 0ₙ ⊥ = true
sameBranch 0ₙ 0ₙ = true
sameBranch 0ₙ (sᵤ _) = false
sameBranch 0ₙ ℕ = false
sameBranch 0ₙ 𝒰 = false
sameBranch 0ₙ (λᵤ _) = false
sameBranch 0ₙ (Π _ _) = false
sameBranch (sᵤ _) ⊥ = true
sameBranch (sᵤ _) 0ₙ = false
sameBranch (sᵤ _) (sᵤ _) = true
sameBranch (sᵤ _) ℕ = false
sameBranch (sᵤ _) 𝒰 = false
sameBranch (sᵤ _) (λᵤ _) = false
sameBranch (sᵤ _) (Π _ _) = false
sameBranch ℕ ⊥ = true
sameBranch ℕ 0ₙ = false
sameBranch ℕ (sᵤ _) = false
sameBranch ℕ ℕ = true
sameBranch ℕ 𝒰 = false
sameBranch ℕ (λᵤ _) = false
sameBranch ℕ (Π _ _) = false
sameBranch 𝒰 ⊥ = true
sameBranch 𝒰 0ₙ = false
sameBranch 𝒰 (sᵤ _) = false
sameBranch 𝒰 ℕ = false
sameBranch 𝒰 𝒰 = true
sameBranch 𝒰 (λᵤ _) = false
sameBranch 𝒰 (Π _ _) = false
sameBranch (λᵤ _) ⊥ = true
sameBranch (λᵤ _) 0ₙ = false
sameBranch (λᵤ _) (sᵤ _) = false
sameBranch (λᵤ _) ℕ = false
sameBranch (λᵤ _) 𝒰 = false
sameBranch (λᵤ _) (λᵤ _) = true
sameBranch (λᵤ _) (Π _ _) = false
sameBranch (Π _ _) ⊥ = true
sameBranch (Π _ _) 0ₙ = false
sameBranch (Π _ _) (sᵤ _) = false
sameBranch (Π _ _) ℕ = false
sameBranch (Π _ _) 𝒰 = false
sameBranch (Π _ _) (λᵤ _) = false
sameBranch (Π _ _) (Π _ _) = true

data Con : ∀ {i} → Nbh i → Nbh i → Set
data ConFinFun : ∀ {i} → FinFun (Nbh i) (Nbh i) → Set
data ¬Con : ∀ {i} → Nbh i → Nbh i → Set
data ¬ConFinFun : ∀ {i} → FinFun (Nbh i) (Nbh i) → Set
-- This is a record that proves that there exist pairs (x , y) ∈ 𝑓 and
-- (x′ , y′) ∈ 𝑓 such that x and x′ are consistent but y and y′ are not.
record ¬CffProof (i : Size) (𝑓 : FinFun (Nbh i) (Nbh i)) : Set

data Con where
  con-⊥₁ : ∀ {i} → {x : Nbh i} → Con ⊥ x
  con-⊥₂ : ∀ {i} → {x : Nbh i} → Con x ⊥
  con-refl-0 : ∀ {i} → Con (0ₙ {i}) 0ₙ
  con-s : ∀ {i} → {x y : Nbh i} → Con x y → Con (sᵤ x) (sᵤ y)
  con-refl-ℕ : ∀ {i} → Con (ℕ {i}) ℕ
  con-refl-𝒰 : ∀ {i} → Con (𝒰 {i}) 𝒰
  con-λ : ∀ {i} → {𝑓 𝑔 : FinFun (Nbh i) (Nbh i)} → ConFinFun (𝑓 ∪ 𝑔) →
          Con (λᵤ 𝑓) (λᵤ 𝑔)
  con-Π : ∀ {i} → {x y : Nbh i} → {𝑓 𝑔 : FinFun (Nbh i) (Nbh i)} →
          Con x y → ConFinFun (𝑓 ∪ 𝑔) → Con (Π x 𝑓) (Π y 𝑔)

data ConFinFun where
  cff : ∀ {i} → {𝑓 : FinFun (Nbh i) (Nbh i)} →
        ({x y x′ y′ : Nbh i} → (x , y) ∈ 𝑓 → (x′ , y′) ∈ 𝑓 →
        ¬Con x x′ ∨ Con y y′) → ConFinFun 𝑓

data ¬Con where
  ¬con-s : ∀ {i} → {x y : Nbh i} → ¬Con x y → ¬Con (sᵤ x) (sᵤ y)
  ¬con-λ : ∀ {i} → {𝑓 𝑔 : FinFun (Nbh i) (Nbh i)} →
           ¬ConFinFun (𝑓 ∪ 𝑔) → ¬Con (λᵤ 𝑓) (λᵤ 𝑔)
  ¬con-Π₁ : ∀ {i} → {x y : Nbh i} → {𝑓 𝑔 : FinFun (Nbh i) (Nbh i)} →
            ¬Con x y → ¬Con (Π x 𝑓) (Π y 𝑔)
  ¬con-Π₂ : ∀ {i} → {x y : Nbh i} → {𝑓 𝑔 : FinFun (Nbh i) (Nbh i)} →
            ¬ConFinFun (𝑓 ∪ 𝑔) → ¬Con (Π x 𝑓) (Π y 𝑔)
  ¬con-br : ∀ {i} → {x y : Nbh i} → sameBranch x y ≡ false →
            ¬Con x y

record ¬CffProof i 𝑓 where
  inductive
  field
    x y x′ y′ : Nbh i
    xy∈𝑓 : (x , y) ∈ 𝑓
    x′y′∈𝑓 : (x′ , y′) ∈ 𝑓
    conxx′ : Con x x′
    ¬conyy′ : ¬Con y y′

data ¬ConFinFun where
  ¬cff : ∀ {i 𝑓} → ¬CffProof i 𝑓 → ¬ConFinFun 𝑓
