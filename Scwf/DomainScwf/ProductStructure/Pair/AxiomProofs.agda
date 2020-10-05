{-# OPTIONS --safe #-}

open import Base.Core
open import Base.Variables
open import Scwf.DomainScwf.Appmap.Definition

module Scwf.DomainScwf.ProductStructure.Pair.AxiomProofs
  (𝑡 : Term Γ 𝐴)
  (𝑢 : Term Γ 𝐵) where

open import NbhSys.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Relation
open import Scwf.DomainScwf.ProductStructure.NbhSys.Definition
open import Scwf.DomainScwf.ProductStructure.NbhSys.Instance
open import Scwf.DomainScwf.ProductStructure.NbhSys.Relation
open import Scwf.DomainScwf.ProductStructure.Pair.Relation

<>↦-mono : ∀ {𝑥 𝑦 z} → ⊑ᵥ Γ 𝑥 𝑦 → <>↦ 𝑡 𝑢 𝑥 z →
           <>↦ 𝑡 𝑢 𝑦 z
<>↦-mono 𝑥⊑𝑦 <>↦-intro₁ = <>↦-intro₁
<>↦-mono 𝑥⊑𝑦 (<>↦-intro₂ 𝑡𝑥↦z₁ 𝑢𝑥↦z₂)
  = <>↦-intro₂ 𝑡𝑦↦z₁ 𝑢𝑦↦z₂
  where 𝑡𝑦↦z₁ = Appmap.↦-mono 𝑡 𝑥⊑𝑦 𝑡𝑥↦z₁
        𝑢𝑦↦z₂ = Appmap.↦-mono 𝑢 𝑥⊑𝑦 𝑢𝑥↦z₂

<>↦-bottom : ∀ {𝑥} → <>↦ 𝑡 𝑢 𝑥 ⊥ₓ
<>↦-bottom = <>↦-intro₁

<>↦-↓closed : ∀ {𝑥 y z} → [ 𝐴 × 𝐵 ] y ⊑ z →
              <>↦ 𝑡 𝑢 𝑥 z → <>↦ 𝑡 𝑢 𝑥 y
<>↦-↓closed {z = ⊥ₓ} ⊑ₓ-intro₁ _ = <>↦-intro₁
<>↦-↓closed {z = < z₁ , z₂ >} ⊑ₓ-intro₁ _ = <>↦-intro₁
<>↦-↓closed (⊑ₓ-intro₂ y₁⊑z₁ y₂⊑z₂) (<>↦-intro₂ 𝑡𝑥↦y₁ 𝑢𝑥↦y₂)
  = <>↦-intro₂ t𝑡𝑥↦y₁ t𝑢𝑥↦y₂
  where t𝑡𝑥↦y₁ = Appmap.↦-↓closed 𝑡 y₁⊑z₁ 𝑡𝑥↦y₁
        t𝑢𝑥↦y₂ = Appmap.↦-↓closed 𝑢 y₂⊑z₂ 𝑢𝑥↦y₂

<>↦-↑directed : ∀ {𝑥 y z} → <>↦ 𝑡 𝑢 𝑥 y → <>↦ 𝑡 𝑢 𝑥 z →
                ∀ conyz → <>↦ 𝑡 𝑢 𝑥 ([ 𝐴 × 𝐵 ] y ⊔ z [ conyz ])
<>↦-↑directed <>↦-intro₁ <>↦-intro₁ _
  = <>↦-intro₁
<>↦-↑directed {𝑥 = 𝑥} <>↦-intro₁ (<>↦-intro₂ 𝑡𝑥↦z₁ 𝑢𝑥↦z₂) _
  = <>↦-intro₂ 𝑡𝑥↦z₁ 𝑢𝑥↦z₂
<>↦-↑directed {𝑥 = 𝑥} (<>↦-intro₂ 𝑡𝑥↦y₁ 𝑢𝑥↦y₂) <>↦-intro₁ _
  = <>↦-intro₂ 𝑡𝑥↦y₁ 𝑢𝑥↦y₂
<>↦-↑directed {𝑥 = 𝑥} (<>↦-intro₂ 𝑡𝑥↦y₁ 𝑢𝑥↦y₂)
  (<>↦-intro₂ 𝑡𝑥↦z₁ 𝑢𝑥↦z₂)
  (con-pair cony₁z₁ cony₂z₂)
  = <>↦-intro₂ 𝑡𝑥↦y₁⊔z₁ 𝑢𝑥↦y₂⊔z₂
  where 𝑡𝑥↦y₁⊔z₁ = Appmap.↦-↑directed 𝑡 𝑡𝑥↦y₁ 𝑡𝑥↦z₁ cony₁z₁
        𝑢𝑥↦y₂⊔z₂ = Appmap.↦-↑directed 𝑢 𝑢𝑥↦y₂ 𝑢𝑥↦z₂ cony₂z₂

<>↦-con : ∀ {𝑥 y 𝑥′ y′} → <>↦ 𝑡 𝑢 𝑥 y → <>↦ 𝑡 𝑢 𝑥′ y′ →
          ValCon Γ 𝑥 𝑥′ → NbhSys.Con (𝐴 × 𝐵) y y′
<>↦-con <>↦-intro₁ <>↦-intro₁ _ = conₓ-⊥₁
<>↦-con <>↦-intro₁ (<>↦-intro₂ _ _) _ = conₓ-⊥₂
<>↦-con (<>↦-intro₂ _ _) <>↦-intro₁ _ = conₓ-⊥₁
<>↦-con (<>↦-intro₂ 𝑡𝑥↦y₁ 𝑢𝑥↦y₂) (<>↦-intro₂ 𝑡𝑥↦y₃ 𝑢𝑥↦y₄) con𝑥𝑥′
  = cony₁y₂y₃y₄
  where cony₁y₂ = Appmap.↦-con 𝑡 𝑡𝑥↦y₁ 𝑡𝑥↦y₃ con𝑥𝑥′
        cony₃y₄ = Appmap.↦-con 𝑢 𝑢𝑥↦y₂ 𝑢𝑥↦y₄ con𝑥𝑥′
        cony₁y₂y₃y₄ = con-pair cony₁y₂ cony₃y₄
