{-# OPTIONS --safe #-}

module Scwf.DomainScwf.Comprehension.p.AxiomProofs where

open import Base.Core
open import Base.Variables
open import NbhSys.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Instance
open import Scwf.DomainScwf.Appmap.Valuation.Relation
open import Scwf.DomainScwf.Comprehension.p.Relation

p↦-mono : ∀ {𝑥 𝑦 𝑧} → ⊑ᵥ (𝐴 :: Γ) 𝑥 𝑦 → 𝑥 p↦ 𝑧 → 𝑦 p↦ 𝑧
p↦-mono {𝑦 = 𝑦} {𝑧} (⊑ᵥ-cons _ _ _ _ 𝑥⊑𝑦) (p↦-intro _ _ 𝑧⊑𝑥)
  = p↦-intro 𝑦 𝑧 𝑧⊑tail𝑦
  where 𝑧⊑tail𝑦 = NbhSys.⊑-trans (ValNbhSys _) 𝑧⊑𝑥 𝑥⊑𝑦

p↦-bottom : {𝑥 : Valuation (𝐴 :: Γ)} → 𝑥 p↦ ⊥ᵥ
p↦-bottom {𝑥 = 𝑥} = p↦-intro 𝑥 ⊥ᵥ (NbhSys.⊑-⊥ (ValNbhSys _))

p↦-↓closed : {𝑥 : Valuation (𝐴 :: Γ)} → ∀ {𝑦 𝑧} →
             ⊑ᵥ Γ 𝑦 𝑧 → 𝑥 p↦ 𝑧 → 𝑥 p↦ 𝑦
p↦-↓closed {𝑥 = 𝑥} {𝑦} 𝑦⊑𝑧 (p↦-intro _ _ 𝑧⊑𝑥)
  = p↦-intro 𝑥 𝑦 (NbhSys.⊑-trans (ValNbhSys _) 𝑦⊑𝑧 𝑧⊑𝑥)

p↦-↑directed : {𝑥 : Valuation (𝐴 :: Γ)} → ∀ {𝑦 𝑧} →
               𝑥 p↦ 𝑦 → 𝑥 p↦ 𝑧 → 𝑥 p↦ (𝑦 ⊔ᵥ 𝑧)
p↦-↑directed {Γ = Γ} {𝑥 = 𝑥} {𝑦} {𝑧}
  (p↦-intro _ _ 𝑦⊑𝑥) (p↦-intro _ _ 𝑧⊑𝑥)
  = p↦-intro 𝑥 (𝑦 ⊔ᵥ 𝑧) 𝑦⊔𝑧⊑tail𝑥
  where 𝑦⊔𝑧⊑tail𝑥 = NbhSys.⊑-⊔ (ValNbhSys _) 𝑦⊑𝑥 𝑧⊑𝑥
