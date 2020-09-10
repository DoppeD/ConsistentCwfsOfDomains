{-# OPTIONS --safe #-}

open import NbhSys.Definition

module Scwf.DomainScwf.ProductStructure.NbhSys.Relation
  (𝒟 𝒟′ : NbhSys) where

open import Base.Core
open import Scwf.DomainScwf.ProductStructure.NbhSys.Definition 𝒟 𝒟′

data _⊑ₓ_ : ProdNbh → ProdNbh → Set where
  ⊑ₓ-intro₁ : ∀ {x} → ⊥ₓ ⊑ₓ x
  ⊑ₓ-intro₂ : ∀ x y x′ y′ → [ 𝒟 ] x ⊑ y →
              [ 𝒟′ ] x′ ⊑ y′ →
              < x , x′ > ⊑ₓ < y , y′ >
