{-# OPTIONS --safe #-}

module Scwf.DomainScwf.Comprehension.p.Relation where

open import Base.Core
open import Base.Variables
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Relation

data _p↦_ : Valuation (𝐴 :: Γ) → Valuation Γ → Set where
  p↦-intro : {𝑥 : Valuation (𝐴 :: Γ)} → ∀ {𝑦} →
             ⊑ᵥ Γ 𝑦 (ctTail 𝑥) → 𝑥 p↦ 𝑦
