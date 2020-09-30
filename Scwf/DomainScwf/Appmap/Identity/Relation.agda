{-# OPTIONS --safe #-}

module Scwf.DomainScwf.Appmap.Identity.Relation where

open import Base.Core
open import Base.Variables
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Relation

data _id↦_ : Valuation Γ → Valuation Γ → Set where
  id↦-intro : ∀ {𝑥 𝑦} → ⊑ᵥ Γ 𝑦 𝑥 → 𝑥 id↦ 𝑦
