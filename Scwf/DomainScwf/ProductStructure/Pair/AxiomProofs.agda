{-# OPTIONS --safe #-}

open import Base.Core
open import Base.Variables
open import Scwf.DomainScwf.Appmap.Definition

module Scwf.DomainScwf.ProductStructure.Pair.AxiomProofs
  (𝑡 : tAppmap Γ [ 𝐴 ])
  (𝑢 : tAppmap Γ [ 𝐵 ]) where

open import NbhSys.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Relation
open import Scwf.DomainScwf.ProductStructure.NbhSys.Definition
open import Scwf.DomainScwf.ProductStructure.NbhSys.Instance
open import Scwf.DomainScwf.ProductStructure.NbhSys.Relation
open import Scwf.DomainScwf.ProductStructure.Pair.Relation

<>↦-mono : ∀ {𝑥 𝑦 𝑧} → ⊑ᵥ Γ 𝑥 𝑦 → <>↦ 𝑡 𝑢 𝑥 𝑧 →
           <>↦ 𝑡 𝑢 𝑦 𝑧
<>↦-mono {𝑦 = 𝑦} 𝑥⊑𝑦 <>↦-intro₁ = <>↦-intro₁
<>↦-mono {𝑦 = 𝑦} 𝑥⊑𝑦 (<>↦-intro₂ _ z₁ z₂ 𝑡𝑥↦z₁ 𝑢𝑥↦z₂)
  = <>↦-intro₂ 𝑦 z₁ z₂ 𝑡𝑦↦z₁ 𝑢𝑦↦z₂
  where 𝑡𝑦↦z₁ = Appmap.↦-mono 𝑡 𝑥⊑𝑦 𝑡𝑥↦z₁
        𝑢𝑦↦z₂ = Appmap.↦-mono 𝑢 𝑥⊑𝑦 𝑢𝑥↦z₂

<>↦-bottom : ∀ {𝑥} → <>↦ 𝑡 𝑢 𝑥 ⟪ NbhSys.⊥ (𝐴 × 𝐵) ⟫
<>↦-bottom = <>↦-intro₁

<>↦-↓closed : ∀ {𝑥 𝑦 𝑧} → ⊑ᵥ [ 𝐴 × 𝐵 ] 𝑦 𝑧 →
              <>↦ 𝑡 𝑢 𝑥 𝑧 → <>↦ 𝑡 𝑢 𝑥 𝑦
<>↦-↓closed {𝑦 = ⟪ < y₁ , y₂ > , ⟪⟫ ⟫}
  (⊑ᵥ-cons _ _ _ () ⊑ᵥ-nil) <>↦-intro₁
<>↦-↓closed {𝑦 = ⟪ ⊥ₓ , ⟪⟫ ⟫}
  (⊑ᵥ-cons _ _ _ _ ⊑ᵥ-nil) <>↦-intro₁
  = <>↦-intro₁
<>↦-↓closed {𝑦 = ⟪ ⊥ₓ , ⟪⟫ ⟫}
  (⊑ᵥ-cons _ _ _ _ ⊑ᵥ-nil) (<>↦-intro₂ _ _ _ _ _)
  = <>↦-intro₁
<>↦-↓closed {𝑥 = 𝑥} {⟪ < y₁ , y₂ > , ⟪⟫ ⟫}
  (⊑ᵥ-cons _ _ _ (⊑ₓ-intro₂ _ _ _ _ y₁⊑z₁ y₂⊑z₂) ⊑ᵥ-nil)
  (<>↦-intro₂ _ z₁ z₂ 𝑡𝑥↦y₁ 𝑢𝑥↦y₂)
  = <>↦-intro₂ 𝑥 y₁ y₂ t𝑡𝑥↦y₁ t𝑢𝑥↦y₂
  where ty₁⊑z₁ = ⊑ᵥ-cons [ 𝐴 ] ⟪ y₁ ⟫ ⟪ z₁ ⟫ y₁⊑z₁ ⊑ᵥ-nil
        t𝑡𝑥↦y₁ = Appmap.↦-↓closed 𝑡 ty₁⊑z₁ 𝑡𝑥↦y₁
        ty₂⊑z₂ = ⊑ᵥ-cons [ 𝐵 ] ⟪ y₂ ⟫ ⟪ z₂ ⟫ y₂⊑z₂ ⊑ᵥ-nil
        t𝑢𝑥↦y₂ = Appmap.↦-↓closed 𝑢 ty₂⊑z₂ 𝑢𝑥↦y₂

<>↦-↑directed : ∀ {𝑥 𝑦 𝑧} → <>↦ 𝑡 𝑢 𝑥 𝑦 → <>↦ 𝑡 𝑢 𝑥 𝑧 →
                (con : ValCon [ 𝐴 × 𝐵 ] 𝑦 𝑧) →
                <>↦ 𝑡 𝑢 𝑥 (𝑦 ⊔ᵥ 𝑧 [ con ])
<>↦-↑directed <>↦-intro₁ <>↦-intro₁ (con-tup _ _ _ _ _ _)
  = <>↦-intro₁
<>↦-↑directed {𝑥 = 𝑥} <>↦-intro₁
  (<>↦-intro₂ _ z₁ z₂ 𝑡𝑥↦z₁ 𝑢𝑥↦z₂) (con-tup _ _ _ _ _ _)
  = <>↦-intro₂ 𝑥 z₁ z₂ 𝑡𝑥↦z₁ 𝑢𝑥↦z₂
<>↦-↑directed {𝑥 = 𝑥} (<>↦-intro₂ _ y₁ y₂ 𝑡𝑥↦y₁ 𝑢𝑥↦y₂)
  <>↦-intro₁ (con-tup _ _ _ _ _ _)
  = <>↦-intro₂ 𝑥 y₁ y₂ 𝑡𝑥↦y₁ 𝑢𝑥↦y₂
<>↦-↑directed {𝑥 = 𝑥} (<>↦-intro₂ _ y₁ y₂ 𝑡𝑥↦y₁ 𝑢𝑥↦y₂)
  (<>↦-intro₂ _ z₁ z₂ 𝑡𝑥↦z₁ 𝑢𝑥↦z₂)
  (con-tup _ _ (con-pair cony₁z₁ cony₂z₂) _ _ _)
  = <>↦-intro₂ 𝑥 [ 𝐴 ] y₁ ⊔ z₁ [ cony₁z₁ ] [ 𝐵 ] y₂ ⊔ z₂ [ cony₂z₂ ] 𝑡𝑥↦y₁⊔z₁ 𝑢𝑥↦y₂⊔z₂
  where 𝑡𝑥↦y₁⊔z₁ = Appmap.↦-↑directed 𝑡 𝑡𝑥↦y₁ 𝑡𝑥↦z₁ (toValCon cony₁z₁)
        𝑢𝑥↦y₂⊔z₂ = Appmap.↦-↑directed 𝑢 𝑢𝑥↦y₂ 𝑢𝑥↦z₂ (toValCon cony₂z₂)
