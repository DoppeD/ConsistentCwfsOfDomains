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
  sᵤ : ∀ {i} → Nbh i → Nbh i
  ℕ : ∀ {i} → Nbh i
  𝒰 : ∀ {i} → Nbh i
  λᵤ : ∀ {i} → FinFun (Nbh i) (Nbh i) → Nbh (↑ i)
  Π : ∀ {i} → Nbh i → FinFun (Nbh i) (Nbh i) → Nbh i

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

-- Perhaps we should introduce a function sameBranch : Nbh → Nbh → Bool
-- such that sameBranch x y ≡ true iff x and y start with the same constructor
-- or at least one is ⊥? That way we can remove most of the below constructors.
data ¬Con where
  ¬con-0ℕ : ∀ {i} → ¬Con (0ₙ {i}) ℕ
  ¬con-0λ : ∀ {i} → {𝑓 : FinFun (Nbh i) (Nbh i)} → ¬Con 0ₙ (λᵤ 𝑓)
  ¬con-ℕλ : ∀ {i} → {𝑓 : FinFun (Nbh i) (Nbh i)} → ¬Con ℕ (λᵤ 𝑓)
  ¬con-𝒰0 : ∀ {i} → ¬Con (𝒰 {i}) 0ₙ
  ¬con-𝒰ℕ : ∀ {i} → ¬Con (𝒰 {i}) ℕ
  ¬con-𝒰λ : ∀ {i} → {𝑓 : FinFun (Nbh i) (Nbh i)} → ¬Con 𝒰 (λᵤ 𝑓)
  ¬con-sym : ∀ {i} → {x y : Nbh i} → ¬Con x y → ¬Con y x
  ¬con-s : ∀ {i} → {x y : Nbh i} → ¬Con x y → ¬Con (sᵤ x) (sᵤ y)
  ¬con-sℕ : ∀ {i} → {x : Nbh i} → ¬Con (sᵤ x) ℕ
  ¬con-s𝒰 : ∀ {i} → {x : Nbh i} → ¬Con (sᵤ x) 𝒰
  ¬con-s0 : ∀ {i} → {x : Nbh i} → ¬Con (sᵤ x) 0ₙ
  ¬con-sλ : ∀ {i} → {x : Nbh (↑ i)} → {𝑓 : FinFun (Nbh i) (Nbh i)} →
            ¬Con (sᵤ x) (λᵤ 𝑓)
  ¬con-λ : ∀ {i} → {𝑓 𝑔 : FinFun (Nbh i) (Nbh i)} →
           ¬ConFinFun (𝑓 ∪ 𝑔) → ¬Con (λᵤ 𝑓) (λᵤ 𝑔)
  ¬con-Π₁ : ∀ {i} → {x y : Nbh i} → {𝑓 𝑔 : FinFun (Nbh i) (Nbh i)} →
            ¬Con x y → ¬Con (Π x 𝑓) (Π y 𝑔)
  ¬con-Π₂ : ∀ {i} → {x y : Nbh i} → {𝑓 𝑔 : FinFun (Nbh i) (Nbh i)} →
            ¬ConFinFun (𝑓 ∪ 𝑔) → ¬Con (Π x 𝑓) (Π y 𝑔)
  ¬con-Πℕ : ∀ {i} → {x : Nbh i} → {𝑓 : FinFun (Nbh i) (Nbh i)} →
            ¬Con (Π x 𝑓) ℕ
  ¬con-Π0 : ∀ {i} → {x : Nbh i} → {𝑓 : FinFun (Nbh i) (Nbh i)} →
            ¬Con (Π x 𝑓) 0ₙ
  ¬con-Π𝒰 : ∀ {i} → {x : Nbh i} → {𝑓 : FinFun (Nbh i) (Nbh i)} →
            ¬Con (Π x 𝑓) 𝒰
  ¬con-Πλ : ∀ {i} → {x : Nbh (↑ i)} → {𝑓 : FinFun (Nbh (↑ i)) (Nbh (↑ i))} →
            {𝑔 : FinFun (Nbh i) (Nbh i)} → ¬Con (Π x 𝑓) (λᵤ 𝑔)
  ¬con-Πs : ∀ {i} → {x y : Nbh i} → {𝑓 𝑔 : FinFun (Nbh i) (Nbh i)} →
            ¬Con (Π x 𝑓) (sᵤ y)

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
