module Cwf.UniType where

open import Base.Core using (_,_)
open import Base.FinFun

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
  ℕ : ∀ {i} → Nbh i
  λᵤ : ∀ {i} → (𝑓 : FinFun (Nbh i) (Nbh i)) → Nbh (↑ i)

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
  con-refl-ℕ : ∀ {i} → Con (ℕ {i}) ℕ
  con-λ : ∀ {i} → {𝑓 𝑔 : FinFun (Nbh i) (Nbh i)} → ConFinFun (𝑓 ∪ 𝑔) →
          Con (λᵤ 𝑓) (λᵤ 𝑔)

data ConFinFun where
  cff : ∀ {i} → {𝑓 : FinFun (Nbh i) (Nbh i)} →
        ({x y x′ y′ : Nbh i} → (x , y) ∈ 𝑓 → (x′ , y′) ∈ 𝑓 →
        ¬Con x x′ ∨ Con y y′) → ConFinFun 𝑓

data ¬Con where
  ¬con-0λ : ∀ {i} → {𝑓 : FinFun (Nbh i) (Nbh i)} → ¬Con 0ₙ (λᵤ 𝑓)
  ¬con-0ℕ : ∀ {i} → ¬Con (0ₙ {i}) ℕ
  ¬con-ℕλ : ∀ {i} → {𝑓 : FinFun (Nbh i) (Nbh i)} → ¬Con ℕ (λᵤ 𝑓)
  ¬con-sym : ∀ {i} → {x y : Nbh i} → ¬Con x y → ¬Con y x
  ¬con-λ : ∀ {i} → {𝑓 𝑔 : FinFun (Nbh i) (Nbh i)} →
           ¬ConFinFun (𝑓 ∪ 𝑔) → ¬Con (λᵤ 𝑓) (λᵤ 𝑔)

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
