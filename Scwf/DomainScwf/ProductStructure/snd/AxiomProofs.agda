{-# OPTIONS --safe #-}

open import Base.Core
open import Base.Variables
open import Scwf.DomainScwf.Appmap.Definition
open import Scwf.DomainScwf.ProductStructure.NbhSys.Instance

module Scwf.DomainScwf.ProductStructure.snd.AxiomProofs
  (𝑡 : Term Γ (𝐴 × 𝐵)) where

open import NbhSys.Definition
open import NbhSys.Lemmata
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Lemmata
open import Scwf.DomainScwf.Appmap.Valuation.Relation
open import Scwf.DomainScwf.ProductStructure.NbhSys.Definition
open import Scwf.DomainScwf.ProductStructure.NbhSys.Relation
open import Scwf.DomainScwf.ProductStructure.snd.Relation

snd↦-mono : ∀ {𝑥 𝑦 z} → ⊑ᵥ Γ 𝑥 𝑦 → snd↦ 𝑡 𝑥 z →
            snd↦ 𝑡 𝑦 z
snd↦-mono _ (snd-intro₁ z⊑⊥)
  = snd-intro₁ z⊑⊥
snd↦-mono 𝑥⊑𝑦 (snd-intro₂ 𝑡𝑥↦z₁z₂)
  = snd-intro₂ 𝑡𝑦↦z₁z₂
    where 𝑡𝑦↦z₁z₂ = Appmap.↦-mono 𝑡 𝑥⊑𝑦 𝑡𝑥↦z₁z₂

snd↦-bottom : ∀ {𝑥} → snd↦ 𝑡 𝑥 (NbhSys.⊥ 𝐵)
snd↦-bottom = snd-intro₁ (NbhSys.⊑-refl 𝐵)

snd↦-↓closed : ∀ {𝑥 y z} → [ 𝐵 ] y ⊑ z → snd↦ 𝑡 𝑥 z →
               snd↦ 𝑡 𝑥 y
snd↦-↓closed y⊑z (snd-intro₁ z⊑⊥)
  = snd-intro₁ (NbhSys.⊑-trans 𝐵 y⊑z z⊑⊥)
snd↦-↓closed y⊑z₂ (snd-intro₂ 𝑡𝑥↦z₁z₂)
  = snd-intro₂ 𝑡𝑥↦z₁y
  where z₁y⊑z₁z₂ = ⊑ₓ-intro₂ (NbhSys.⊑-refl 𝐴) y⊑z₂
        𝑡𝑥↦z₁y = Appmap.↦-↓closed 𝑡 z₁y⊑z₁z₂ 𝑡𝑥↦z₁z₂

snd↦-↑directed : ∀ {𝑥 y z} → snd↦ 𝑡 𝑥 y → snd↦ 𝑡 𝑥 z →
                 ∀ conyz → snd↦ 𝑡 𝑥 ([ 𝐵 ] y ⊔ z [ conyz ])
snd↦-↑directed (snd-intro₁ y⊑⊥) (snd-intro₁ z⊑⊥) conyz
  = snd-intro₁ (NbhSys.⊑-⊔ 𝐵 y⊑⊥ z⊑⊥ conyz)
snd↦-↑directed (snd-intro₂ 𝑡𝑥↦y₁y₂) (snd-intro₁ z⊑⊥) cony₂z
  = snd-intro₂ 𝑡𝑥↦y₁y₂⊔z
  where z⊑y₂ = NbhSys.⊑-trans 𝐵 z⊑⊥ (NbhSys.⊑-⊥ 𝐵)
        y₂⊔z⊑y₂ = NbhSys.⊑-⊔ 𝐵 (NbhSys.⊑-refl 𝐵) z⊑y₂ cony₂z
        y₁y₂⊔z⊑y₁y₂ = ⊑ₓ-intro₂ (NbhSys.⊑-refl 𝐴) y₂⊔z⊑y₂
        𝑡𝑥↦y₁y₂⊔z = Appmap.↦-↓closed 𝑡 y₁y₂⊔z⊑y₁y₂ 𝑡𝑥↦y₁y₂
snd↦-↑directed (snd-intro₁ y⊑⊥) (snd-intro₂ 𝑡𝑥↦z₁z₂) conyz₂
  = snd-intro₂ 𝑡𝑥↦z₁y⊔z₂
  where y⊑z₂ = NbhSys.⊑-trans 𝐵 y⊑⊥ (NbhSys.⊑-⊥ 𝐵)
        y⊔z₂⊑z₂ = NbhSys.⊑-⊔ 𝐵 y⊑z₂ (NbhSys.⊑-refl 𝐵) conyz₂
        z₁y⊔z₂⊑z₂z₂ = ⊑ₓ-intro₂ (NbhSys.⊑-refl 𝐴) y⊔z₂⊑z₂
        𝑡𝑥↦z₁y⊔z₂ = Appmap.↦-↓closed 𝑡 z₁y⊔z₂⊑z₂z₂ 𝑡𝑥↦z₁z₂
snd↦-↑directed (snd-intro₂ 𝑡𝑥↦y₁y₂) (snd-intro₂ 𝑡𝑥↦z₁z₂) cony₂z₂
  with (Appmap.↦-con 𝑡 𝑡𝑥↦y₁y₂ 𝑡𝑥↦z₁z₂ valConRefl)
... | con-pair cony₁z₁ _
  = snd-intro₂ 𝑡𝑥↦⊔
  where 𝑡𝑥↦⊔ = Appmap.↦-↑directed 𝑡 𝑡𝑥↦y₁y₂ 𝑡𝑥↦z₁z₂
               (con-pair cony₁z₁ cony₂z₂)

snd↦-con : ∀ {𝑥 𝑦 𝑥′ 𝑦′} → snd↦ 𝑡 𝑥 𝑦 → snd↦ 𝑡 𝑥′ 𝑦′ →
           ValCon Γ 𝑥 𝑥′ → NbhSys.Con 𝐵 𝑦 𝑦′
snd↦-con (snd-intro₁ y⊑⊥) (snd-intro₁ y′⊑⊥) _
  = NbhSys.Con-⊔ 𝐵 y⊑⊥ y′⊑⊥
snd↦-con (snd-intro₁ y⊑⊥) (snd-intro₂ _) _
  = NbhSys.Con-⊔ 𝐵 y⊑y′₁ (NbhSys.⊑-refl 𝐵)
  where y⊑y′₁ = NbhSys.⊑-trans 𝐵 y⊑⊥ (NbhSys.⊑-⊥ 𝐵)
snd↦-con (snd-intro₂ _) (snd-intro₁ y′⊑⊥) _
  = NbhSys.Con-⊔ 𝐵 (NbhSys.⊑-refl 𝐵) y′₁⊑y
  where y′₁⊑y = NbhSys.⊑-trans 𝐵 y′⊑⊥ (NbhSys.⊑-⊥ 𝐵)
snd↦-con (snd-intro₂ 𝑡𝑥↦y₁y₂)
  (snd-intro₂ 𝑡𝑥′↦y′₁y′₂) con
  with (Appmap.↦-con 𝑡 𝑡𝑥↦y₁y₂ 𝑡𝑥′↦y′₁y′₂ con)
... | con-pair _ cony′₁y′₂ = cony′₁y′₂
