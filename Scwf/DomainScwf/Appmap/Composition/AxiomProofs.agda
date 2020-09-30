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
open import Scwf.DomainScwf.Appmap.Valuation.Lemmata
open import Scwf.DomainScwf.Appmap.Valuation.Relation

∘↦-mono : ∀ {𝑥 𝑦 𝑧} → ⊑ᵥ Γ 𝑥 𝑦 →
          _∘↦_ δ γ 𝑥 𝑧 → _∘↦_ δ γ 𝑦 𝑧
∘↦-mono {𝑦 = 𝑦} {𝑧} 𝑥⊑𝑦 (∘↦-intro γ𝑥↦y δy↦𝑧)
  = ∘↦-intro (Appmap.↦-mono γ 𝑥⊑𝑦 γ𝑥↦y) δy↦𝑧

∘↦-bottom : ∀ {𝑥} → _∘↦_ δ γ 𝑥 ⊥ᵥ
∘↦-bottom {𝑥 = 𝑥}
  = ∘↦-intro (Appmap.↦-bottom γ) (Appmap.↦-bottom δ)

∘↦-↓closed : ∀ {𝑥 𝑧 𝑤} → ⊑ᵥ Θ 𝑧 𝑤 →
             _∘↦_ δ γ 𝑥 𝑤 → _∘↦_ δ γ 𝑥 𝑧
∘↦-↓closed {𝑥 = 𝑥} {𝑧} 𝑧⊑𝑤 (∘↦-intro γ𝑥↦y δy↦𝑤)
  = ∘↦-intro γ𝑥↦y (Appmap.↦-↓closed δ 𝑧⊑𝑤 δy↦𝑤)

∘↦-↑directed : ∀ {𝑥 𝑧 𝑤} → _∘↦_ δ γ 𝑥 𝑧 → _∘↦_ δ γ 𝑥 𝑤 →
               (con : ValCon Θ 𝑧 𝑤) →
               _∘↦_ δ γ 𝑥 (𝑧 ⊔ᵥ 𝑤 [ con ])
∘↦-↑directed  (∘↦-intro γ𝑥↦𝑦 δ𝑦↦𝑧)
  (∘↦-intro γ𝑥↦𝑦' δ𝑦'↦𝑤) con𝑧𝑤
  = ∘↦-intro γ𝑥↦𝑦⊔𝑦' δ𝑦⊔𝑦'↦𝑧⊔𝑤
    where con𝑦𝑦′ = Appmap.↦-con γ γ𝑥↦𝑦 γ𝑥↦𝑦' valConRefl
          γ𝑥↦𝑦⊔𝑦' = Appmap.↦-↑directed γ γ𝑥↦𝑦 γ𝑥↦𝑦' con𝑦𝑦′
          𝑦⊑𝑦⊔𝑦′ = NbhSys.⊑-⊔-fst (ValNbhSys Δ) con𝑦𝑦′
          δ𝑦⊔𝑦'↦𝑧 = Appmap.↦-mono δ 𝑦⊑𝑦⊔𝑦′ δ𝑦↦𝑧
          𝑦′⊑𝑦⊔𝑦′ = NbhSys.⊑-⊔-snd (ValNbhSys Δ) con𝑦𝑦′
          δ𝑦⊔𝑦'↦𝑤 = Appmap.↦-mono δ 𝑦′⊑𝑦⊔𝑦′ δ𝑦'↦𝑤
          δ𝑦⊔𝑦'↦𝑧⊔𝑤 = Appmap.↦-↑directed δ δ𝑦⊔𝑦'↦𝑧 δ𝑦⊔𝑦'↦𝑤 con𝑧𝑤

∘↦-con : ∀ {𝑥 𝑦 𝑥′ 𝑦′} → _∘↦_ δ γ 𝑥 𝑦 → _∘↦_ δ γ 𝑥′ 𝑦′ →
         ValCon Γ 𝑥 𝑥′ → ValCon Θ 𝑦 𝑦′
∘↦-con {𝑦 = ⟪⟫} {𝑦′ = ⟪⟫} _ _ _ = con-nil
∘↦-con {𝑦 = ⟪ y , 𝑦 ⟫} {𝑦′ = ⟪ y′ , 𝑦′ ⟫}
  (∘↦-intro γ𝑥↦𝑧 δ𝑧↦𝑦) (∘↦-intro γ𝑥′↦𝑧′ δ𝑧′↦𝑦′) con𝑥𝑥′
  with (Appmap.↦-con δ δ𝑧↦𝑦 δ𝑧′↦𝑦′ con𝑧𝑧′)
  where con𝑧𝑧′ = Appmap.↦-con γ γ𝑥↦𝑧 γ𝑥′↦𝑧′ con𝑥𝑥′
... | con-tup conyy′ con𝑦𝑦′
  = con-tup conyy′ con𝑦𝑦′
