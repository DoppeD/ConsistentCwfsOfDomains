{-# OPTIONS --safe #-}

module Scwf.DomainScwf.ProductStructure.fst.Relation where

open import Appmap.Definition
open import Base.Core
open import Base.Variables
open import NbhSys.Definition
open import Scwf.DomainScwf.Appmap.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.ProductStructure.NbhSys.Definition
open import Scwf.DomainScwf.ProductStructure.NbhSys.Instance

data fst↦ (𝑡 : tAppmap Γ [ 𝐴 × 𝐵 ]) :
          Valuation Γ → Valuation [ 𝐴 ] → Set where
  fst-intro₁ : ∀ 𝑥 y → [ 𝐴 ] y ⊑ NbhSys.⊥ 𝐴 → fst↦ 𝑡 𝑥 ⟪ y ⟫
  fst-intro₂ : ∀ 𝑥 y₁ y₂ → [ 𝑡 ] 𝑥 ↦ ⟪ < y₁ , y₂ > ⟫ →
               fst↦ 𝑡 𝑥 ⟪ y₁ ⟫
