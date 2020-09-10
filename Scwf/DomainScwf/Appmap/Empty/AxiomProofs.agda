{-# OPTIONS --safe #-}

module Scwf.DomainScwf.Appmap.Empty.AxiomProofs where

open import Base.Core
open import Base.Variables
open import Scwf.DomainScwf.Appmap.Empty.Relation
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Relation

empty↦-mono : ∀ {𝑥 𝑦 𝑧} → ⊑ᵥ Γ 𝑥 𝑦 → 𝑥 empty↦ 𝑧 →
              𝑦 empty↦ 𝑧
empty↦-mono {𝑧 = ⟪⟫} _ _ = empty↦-intro

empty↦-↓closed : {𝑥 : Valuation Γ} → ∀ {𝑦 𝑧} →
                 ⊑ᵥ [] 𝑦 𝑧 → 𝑥 empty↦ 𝑧 →
                 𝑥 empty↦ 𝑦
empty↦-↓closed {𝑦 = ⟪⟫} _ _ = empty↦-intro

empty↦-↑directed : {𝑥 : Valuation Γ} → ∀ {𝑦 𝑧} →
                   𝑥 empty↦ 𝑦 → 𝑥 empty↦ 𝑧 → (con : ValCon [] 𝑦 𝑧) →
                   𝑥 empty↦ (𝑦 ⊔ᵥ 𝑧 [ con ])
empty↦-↑directed {𝑦 = ⟪⟫} {⟪⟫} _ _ _ = empty↦-intro

empty↦-con : {𝑥 : Valuation Γ} → ∀ {𝑦 𝑥′ 𝑦′} →
             𝑥 empty↦ 𝑦 → 𝑥′ empty↦ 𝑦′ → ValCon Γ 𝑥 𝑥′ →
             ValCon [] 𝑦 𝑦′
empty↦-con {𝑦 = ⟪⟫} {𝑦′ = ⟪⟫} x x₁ x₂ = con-nil
