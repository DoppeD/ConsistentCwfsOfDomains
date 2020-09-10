{-# OPTIONS --safe #-}

module Scwf.DomainScwf.Comprehension.q.AxiomProofs where

open import Base.Core
open import Base.Variables
open import NbhSys.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Relation
open import Scwf.DomainScwf.Comprehension.q.Relation

q↦-mono : ∀ {𝑥 𝑦} → {𝑧 : Valuation [ 𝐴 ]} →
          ⊑ᵥ (𝐴 :: Γ) 𝑥 𝑦 → 𝑥 q↦ 𝑧 →
          𝑦 q↦ 𝑧
q↦-mono {𝐴} {𝑦 = 𝑦} {𝑧} (⊑ᵥ-cons _ _ _ x⊑y _)
  (q↦-intro _ _ z⊑x)
  = q↦-intro 𝑦 𝑧 (NbhSys.⊑-trans 𝐴 z⊑x x⊑y)

q↦-bottom : {𝑥 : Valuation (𝐴 :: Γ)} → 𝑥 q↦ ⊥ᵥ
q↦-bottom {𝐴 = 𝐴} {𝑥 = 𝑥} = q↦-intro 𝑥 ⊥ᵥ (NbhSys.⊑-⊥ 𝐴)

q↦-↓closed : {𝑥 : Valuation (𝐴 :: Γ)} → ∀ {𝑦 𝑧} →
             ⊑ᵥ [ 𝐴 ] 𝑦 𝑧 → 𝑥 q↦ 𝑧 → 𝑥 q↦ 𝑦
q↦-↓closed {𝐴 = 𝐴} {𝑥 = 𝑥} {𝑦} (⊑ᵥ-cons _ _ _ y⊑z _)
  (q↦-intro _ _ z⊑x)
  = q↦-intro 𝑥 𝑦 (NbhSys.⊑-trans 𝐴 y⊑z z⊑x)

q↦-↑directed : {𝑥 : Valuation (𝐴 :: Γ)} → ∀ {𝑦 𝑧} →
               𝑥 q↦ 𝑦 → 𝑥 q↦ 𝑧 → 𝑥 q↦ (𝑦 ⊔ᵥ 𝑧)
q↦-↑directed {𝐴 = 𝐴} {𝑥 = ⟪ x , 𝑥 ⟫} {⟪ y , ⟪⟫ ⟫}
  {⟪ z , ⟪⟫ ⟫} (q↦-intro _ _ y⊑x) (q↦-intro _ _ z⊑x)
  = q↦-intro ⟪ x , 𝑥 ⟫ (⟪ y ⟫ ⊔ᵥ ⟪ z ⟫) y⊔z⊑x
  where y⊔z⊑x = NbhSys.⊑-⊔ 𝐴 y⊑x z⊑x
