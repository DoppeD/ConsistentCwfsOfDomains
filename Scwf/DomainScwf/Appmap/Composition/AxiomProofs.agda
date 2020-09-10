{-# OPTIONS --safe #-}

open import Base.Variables
open import Scwf.DomainScwf.Appmap.Definition

module Scwf.DomainScwf.Appmap.Composition.AxiomProofs
  (δ : tAppmap Δ Θ) (γ : tAppmap Γ Δ) where

open import Base.Core
open import NbhSys.Definition
open import NbhSys.Lemmata
open import Scwf.DomainScwf.Appmap.Composition.Relation
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Instance
open import Scwf.DomainScwf.Appmap.Valuation.Relation

∘↦-mono : ∀ {𝑥 𝑦 𝑧} → ⊑ᵥ Γ 𝑥 𝑦 →
          _∘↦_ δ γ 𝑥 𝑧 → _∘↦_ δ γ 𝑦 𝑧
∘↦-mono {𝑦 = 𝑦} {𝑧} 𝑥⊑𝑦 (∘↦-intro _ y _ γ𝑥↦y δy↦𝑧)
  = ∘↦-intro 𝑦 y 𝑧 (Appmap.↦-mono γ 𝑥⊑𝑦 γ𝑥↦y) δy↦𝑧

∘↦-bottom : ∀ {𝑥} → _∘↦_ δ γ 𝑥 ⊥ᵥ
∘↦-bottom {𝑥 = 𝑥}
  = ∘↦-intro 𝑥 ⊥ᵥ ⊥ᵥ (Appmap.↦-bottom γ) (Appmap.↦-bottom δ)

∘↦-↓closed : ∀ {𝑥 𝑧 𝑤} → ⊑ᵥ Θ 𝑧 𝑤 →
             _∘↦_ δ γ 𝑥 𝑤 → _∘↦_ δ γ 𝑥 𝑧
∘↦-↓closed {𝑥 = 𝑥} {𝑧} 𝑧⊑𝑤 (∘↦-intro _ y _ γ𝑥↦y δy↦𝑤)
  = ∘↦-intro 𝑥 y 𝑧 γ𝑥↦y (Appmap.↦-↓closed δ 𝑧⊑𝑤 δy↦𝑤)

∘↦-↑directed : ∀ {𝑥 𝑧 𝑤} → _∘↦_ δ γ 𝑥 𝑧 → _∘↦_ δ γ 𝑥 𝑤 →
               _∘↦_ δ γ 𝑥 (𝑧 ⊔ᵥ 𝑤)
∘↦-↑directed {𝑥 = 𝑥} {𝑧} {𝑤}
  (∘↦-intro _ 𝑦 _ γ𝑥↦𝑦 δ𝑦↦𝑧) (∘↦-intro _ 𝑦' _ γ𝑥↦𝑦' δ𝑦'↦𝑤)
  = ∘↦-intro 𝑥 (𝑦 ⊔ᵥ 𝑦') (𝑧 ⊔ᵥ 𝑤) γ𝑥↦𝑦⊔𝑦' δ𝑦⊔𝑦'↦𝑧⊔𝑤
    where γ𝑥↦𝑦⊔𝑦' = Appmap.↦-↑directed γ γ𝑥↦𝑦 γ𝑥↦𝑦'
          𝑦⊑𝑦⊔𝑦′ = NbhSys.⊑-⊔-fst (ValNbhSys Δ)
          δ𝑦⊔𝑦'↦𝑧 = Appmap.↦-mono δ 𝑦⊑𝑦⊔𝑦′ δ𝑦↦𝑧
          𝑦′⊑𝑦⊔𝑦′ = NbhSys.⊑-⊔-snd (ValNbhSys Δ)
          δ𝑦⊔𝑦'↦𝑤 = Appmap.↦-mono δ 𝑦′⊑𝑦⊔𝑦′ δ𝑦'↦𝑤
          δ𝑦⊔𝑦'↦𝑧⊔𝑤 = Appmap.↦-↑directed δ δ𝑦⊔𝑦'↦𝑧 δ𝑦⊔𝑦'↦𝑤
