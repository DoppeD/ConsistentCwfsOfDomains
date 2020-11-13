module Cwf.UniType.Definition where

open import Base.Core
open import Base.FinFun

open import Agda.Builtin.Size

{-# NO_POSITIVITY_CHECK #-}
data Nbh : {Size} → Set
data Con : ∀ {i} → Nbh {i} → Nbh {i} → Set
data ConFinFun : ∀ {i} → FinFun (Nbh {i}) (Nbh {i}) → Set

data Nbh where
  ⊥ : ∀ {i} → Nbh {i}
  0ₙ : ∀ {i} → Nbh {i}
  sᵤ : ∀ {i} → Nbh {i} → Nbh {i}
  ℕ : ∀ {i} → Nbh {i}
  𝒰 : ∀ {i} → Nbh {i}
  λᵤ : ∀ {i} → (𝑓 : FinFun (Nbh {i}) (Nbh {i})) → ConFinFun 𝑓 → Nbh {↑ i}
  Π : ∀ {i} → Nbh {i} → (𝑓 : FinFun (Nbh {i}) (Nbh {i})) →
      ConFinFun 𝑓 → Nbh {↑ i}

data Con where
  con-⊥₁ : ∀ {i} → {x : Nbh {i}} → Con ⊥ x
  con-⊥₂ : ∀ {i} → {x : Nbh {i}} → Con x ⊥
  con-refl-0 : ∀ {i} → Con (0ₙ {i}) 0ₙ
  con-s : ∀ {i} → {x y : Nbh {i}} → Con x y → Con (sᵤ x) (sᵤ y)
  con-refl-ℕ : ∀ {i} → Con (ℕ {i}) ℕ
  con-refl-𝒰 : ∀ {i} → Con (𝒰 {i}) 𝒰
  con-λ : ∀ {i} → {𝑓 𝑔 : FinFun (Nbh {i}) (Nbh {i})} → ∀ {con𝑓 con𝑔} →
          ConFinFun (𝑓 ∪ 𝑔) → Con (λᵤ 𝑓 con𝑓) (λᵤ 𝑔 con𝑔)
  con-Π : ∀ {i} → {x y : Nbh {i}} → {𝑓 𝑔 : FinFun (Nbh {i}) (Nbh {i})} →
          ∀ {con𝑓 con𝑔} → Con x y → ConFinFun (𝑓 ∪ 𝑔) →
          Con (Π x 𝑓 con𝑓) (Π y 𝑔 con𝑔)

data ConFinFun where
  cff : ∀ {i} → {𝑓 : FinFun (Nbh {i}) (Nbh {i})} →
        ({x y x′ y′ : Nbh {i}} → (x , y) ∈ 𝑓 → (x′ , y′) ∈ 𝑓 →
        Con x x′ → Con y y′) → ConFinFun 𝑓

subsetIsCon' : ∀ {i} → {𝑓 𝑓′ : FinFun (Nbh {i}) (Nbh {i})} → 𝑓 ⊆ 𝑓′ →
               ConFinFun 𝑓′ → ∀ {x y x′ y′ : Nbh {i}} →
               (x , y) ∈ 𝑓 → (x′ , y′) ∈ 𝑓 → Con x x′ → Con y y′
subsetIsCon' 𝑓⊆𝑓′ (cff p) xy∈𝑓 x′y′∈𝑓
  = p (𝑓⊆𝑓′ xy∈𝑓) (𝑓⊆𝑓′ x′y′∈𝑓)

subsetIsCon : ∀ {i} → {𝑓 𝑓′ : FinFun (Nbh {i}) (Nbh {i})} → 𝑓 ⊆ 𝑓′ →
              ConFinFun 𝑓′ → ConFinFun 𝑓
subsetIsCon 𝑓⊆𝑓′ cff𝑓′ = cff (subsetIsCon' 𝑓⊆𝑓′ cff𝑓′)
