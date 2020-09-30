{-# OPTIONS --safe #-}

module Scwf.DomainScwf.Comprehension.Morphism.Relation where

open import Base.Core
open import Base.Variables
open import Scwf.DomainScwf.Appmap.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Definition

open import Agda.Builtin.Nat

data ⟨⟩↦ (γ : tAppmap Δ Γ) (𝑡 : tAppmap Δ [ 𝐴 ]) :
         Valuation Δ → Valuation (𝐴 :: Γ) → Set where
  ⟨⟩↦-intro : ∀ {𝑥 𝑦} → [ γ ] 𝑥 ↦ (ctTail 𝑦) →
              [ 𝑡 ] 𝑥 ↦ ⟪ ctHead 𝑦 ⟫ → ⟨⟩↦ γ 𝑡 𝑥 𝑦

-- Some simplifying notation.
[⟨_,_⟩]_↦_ : (γ : tAppmap Δ Γ) → (𝑡 : tAppmap Δ [ 𝐴 ]) →
             Valuation Δ → Valuation (𝐴 :: Γ) → Set
[⟨ γ , 𝑡 ⟩] 𝑥 ↦ 𝑦 = ⟨⟩↦ γ 𝑡 𝑥 𝑦
