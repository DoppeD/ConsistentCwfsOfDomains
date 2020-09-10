{-# OPTIONS --safe #-}

module Appmap.Equivalence where

open import Appmap.Definition
open import Base.Core
open import NbhSys.Definition

private
  variable
    𝒟 𝒟′ : NbhSys

data _≼_ : Rel (Appmap 𝒟 𝒟′) where
  ≼-intro : {γ δ : Appmap 𝒟 𝒟′} →
            (∀ x y → [ γ ] x ↦ y → [ δ ] x ↦ y) → γ ≼ δ

-- Two binary relations are equivalent iff they contain exactly
-- the same pairs.
data _≈_ : Rel (Appmap 𝒟 𝒟′) where
  ≈-intro : {γ δ : Appmap 𝒟 𝒟′} → γ ≼ δ → δ ≼ γ → γ ≈ δ

≈Reflexive : Reflexive (_≈_ {𝒟} {𝒟′})
≈Reflexive = ≈-intro (≼-intro λ _ _ γx↦y → γx↦y)
                     (≼-intro λ x y γx↦y → γx↦y)

≈Symmetric : Symmetric (_≈_ {𝒟} {𝒟′})
≈Symmetric (≈-intro (≼-intro p) (≼-intro q))
  = ≈-intro (≼-intro q) (≼-intro p)

≈Transitive : Transitive (_≈_ {𝒟} {𝒟′})
≈Transitive (≈-intro (≼-intro p₁) (≼-intro q₁))
            (≈-intro (≼-intro p₂) (≼-intro q₂))
  = ≈-intro (≼-intro λ x y kx↦y → p₂ x y (p₁ x y kx↦y))
            (≼-intro λ x y kx↦y → q₁ x y (q₂ x y kx↦y))

≈IsEquiv : IsEquivalence (_≈_ {𝒟} {𝒟′})
≈IsEquiv = record { refl = ≈Reflexive
                  ; sym = ≈Symmetric
                  ; trans = ≈Transitive
                  }
