{-# OPTIONS --safe #-}

module Scwf.DomainScwf.Appmap.Composition.Relation where

open import Base.Core
open import Base.Variables
open import Scwf.DomainScwf.Appmap.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Definition

data _∘↦_ (δ : tAppmap Δ Θ) (γ : tAppmap Γ Δ) :
          Valuation Γ → Valuation Θ → Set where
  ∘↦-intro : ∀ {𝑥 𝑦 𝑧} → [ γ ] 𝑥 ↦ 𝑦 → [ δ ] 𝑦 ↦ 𝑧 →
             _∘↦_ δ γ 𝑥 𝑧
