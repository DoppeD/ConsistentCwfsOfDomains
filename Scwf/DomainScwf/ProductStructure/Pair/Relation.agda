{-# OPTIONS --safe #-}

module Scwf.DomainScwf.ProductStructure.Pair.Relation where

open import Base.Core
open import Base.Variables
open import Appmap.Definition
open import Scwf.DomainScwf.Appmap.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.ProductStructure.NbhSys.Definition
open import Scwf.DomainScwf.ProductStructure.NbhSys.Instance

open import Agda.Builtin.Sigma

data <>↦ (𝑡 : tAppmap Γ [ 𝐴 ]) (𝑢 : tAppmap Γ [ 𝐵 ]) :
         Valuation Γ → Valuation [ 𝐴 × 𝐵 ] → Set where
  <>↦-intro₁ : ∀ {𝑥} → <>↦ 𝑡 𝑢 𝑥 ⟪ ⊥ₓ ⟫
  <>↦-intro₂ : ∀ {𝑥 y₁ y₂} → [ 𝑡 ] 𝑥 ↦ ⟪ y₁ ⟫ →
               [ 𝑢 ] 𝑥 ↦ ⟪ y₂ ⟫ →
               <>↦ 𝑡 𝑢 𝑥 ⟪ < y₁ , y₂ > ⟫
