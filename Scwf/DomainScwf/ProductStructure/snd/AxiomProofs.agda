{-# OPTIONS --safe #-}

open import Base.Core
open import Base.Variables
open import Scwf.DomainScwf.Appmap.Definition
open import Scwf.DomainScwf.ProductStructure.NbhSys.Instance

module Scwf.DomainScwf.ProductStructure.snd.AxiomProofs
  (𝑡 : tAppmap Γ [ 𝐴 × 𝐵 ]) where

open import NbhSys.Definition
open import NbhSys.Lemmata
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Lemmata
open import Scwf.DomainScwf.Appmap.Valuation.Relation
open import Scwf.DomainScwf.ProductStructure.NbhSys.Definition
open import Scwf.DomainScwf.ProductStructure.NbhSys.Relation
open import Scwf.DomainScwf.ProductStructure.snd.Relation

snd↦-mono : ∀ {𝑥 𝑦 𝑧} → ⊑ᵥ Γ 𝑥 𝑦 → snd↦ 𝑡 𝑥 𝑧 →
            snd↦ 𝑡 𝑦 𝑧
snd↦-mono {𝑦 = 𝑦} _ (snd-intro₁ _ z z⊑⊥)
  = snd-intro₁ 𝑦 z z⊑⊥
snd↦-mono {𝑦 = 𝑦} 𝑥⊑𝑦 (snd-intro₂ _ z₁ z₂ 𝑡𝑥↦z₁z₂)
  = snd-intro₂ 𝑦 z₁ z₂ 𝑡𝑦↦z₁z₂
    where 𝑡𝑦↦z₁z₂ = Appmap.↦-mono 𝑡 𝑥⊑𝑦 𝑡𝑥↦z₁z₂

snd↦-bottom : ∀ {𝑥} → snd↦ 𝑡 𝑥 ⟪ NbhSys.⊥ 𝐵 ⟫
snd↦-bottom {𝑥 = 𝑥} = snd-intro₁ 𝑥 (NbhSys.⊥ 𝐵) (NbhSys.⊑-refl 𝐵)

snd↦-↓closed : ∀ {𝑥 𝑦 𝑧} → ⊑ᵥ [ 𝐵 ] 𝑦 𝑧 → snd↦ 𝑡 𝑥 𝑧 →
               snd↦ 𝑡 𝑥 𝑦
snd↦-↓closed {𝑥 = 𝑥} {⟪ y , ⟪⟫ ⟫}
  (⊑ᵥ-cons _ _ _ y⊑z ⊑ᵥ-nil) (snd-intro₁ _ z z⊑⊥)
  = snd-intro₁ 𝑥 y (NbhSys.⊑-trans 𝐵 y⊑z z⊑⊥)
snd↦-↓closed {𝑥 = 𝑥} {⟪ y , ⟪⟫ ⟫}
  (⊑ᵥ-cons _ _ _ y⊑z₂ ⊑ᵥ-nil)
  (snd-intro₂ _ z₁ z₂ 𝑡𝑥↦z₁z₂)
  = snd-intro₂ 𝑥 z₁ y 𝑡𝑥↦z₁y
  where z₁y⊑z₁z₂' = ⊑ₓ-intro₂ z₁ z₁ y z₂
                    (NbhSys.⊑-refl 𝐴) y⊑z₂
        z₁y⊑z₁z₂ = ⊑ᵥ-cons [ 𝐴 × 𝐵 ] ⟪ < z₁ , y > ⟫
                   ⟪ < z₁ , z₂ > ⟫ z₁y⊑z₁z₂' ⊑ᵥ-nil
        𝑡𝑥↦z₁y = Appmap.↦-↓closed 𝑡 z₁y⊑z₁z₂ 𝑡𝑥↦z₁z₂

snd↦-↑directed : ∀ {𝑥 𝑦 𝑧} → snd↦ 𝑡 𝑥 𝑦 → snd↦ 𝑡 𝑥 𝑧 →
                 (con : ValCon [ 𝐵 ] 𝑦 𝑧) →
                 snd↦ 𝑡 𝑥 (𝑦 ⊔ᵥ 𝑧 [ con ])
snd↦-↑directed {𝑥 = 𝑥} (snd-intro₁ _ y y⊑⊥)
  (snd-intro₁ _ z z⊑⊥) (con-tup _ _ conyz _ _ _)
  = snd-intro₁ 𝑥 ([ 𝐵 ] y ⊔ z [ conyz ]) (NbhSys.⊑-⊔ 𝐵 y⊑⊥ z⊑⊥ conyz)
snd↦-↑directed {𝑥 = 𝑥}
  (snd-intro₂ _ y₁ y₂ 𝑡𝑥↦y₁y₂) (snd-intro₁ _ z z⊑⊥)
  (con-tup _ _ cony₂z _ _ _)
  = snd-intro₂ 𝑥 y₁ ([ 𝐵 ] y₂ ⊔ z [ cony₂z ]) 𝑡𝑥↦y₁y₂⊔z
  where z⊑y₂ = NbhSys.⊑-trans 𝐵 z⊑⊥ (NbhSys.⊑-⊥ 𝐵)
        y₂⊔z⊑y₂ = NbhSys.⊑-⊔ 𝐵 (NbhSys.⊑-refl 𝐵) z⊑y₂ cony₂z
        y₁y₂⊔z⊑y₁y₂' = ⊑ₓ-intro₂ y₁ y₁ ([ 𝐵 ] y₂ ⊔ z [ cony₂z ]) y₂
                       (NbhSys.⊑-refl 𝐴) y₂⊔z⊑y₂
        y₁y₂⊔z⊑y₁y₂ = ⊑ᵥ-cons [ 𝐴 × 𝐵 ]
                      ⟪ < y₁ , [ 𝐵 ] y₂ ⊔ z [ cony₂z ] > ⟫
                      ⟪ < y₁ , y₂ > ⟫ y₁y₂⊔z⊑y₁y₂' ⊑ᵥ-nil
        𝑡𝑥↦y₁y₂⊔z = Appmap.↦-↓closed 𝑡 y₁y₂⊔z⊑y₁y₂ 𝑡𝑥↦y₁y₂
snd↦-↑directed {𝑥 = 𝑥} (snd-intro₁ _ y y⊑⊥)
  (snd-intro₂ _ z₁ z₂ 𝑡𝑥↦z₁z₂) (con-tup _ _ conyz₂ _ _ _)
  = snd-intro₂ 𝑥 z₁ ([ 𝐵 ] y ⊔ z₂ [ conyz₂ ]) 𝑡𝑥↦z₁y⊔z₂
  where y⊑z₂ = NbhSys.⊑-trans 𝐵 y⊑⊥ (NbhSys.⊑-⊥ 𝐵)
        y⊔z₂⊑z₂ = NbhSys.⊑-⊔ 𝐵 y⊑z₂ (NbhSys.⊑-refl 𝐵) conyz₂
        z₁y⊔z₂⊑z₂z₂' = ⊑ₓ-intro₂ z₁ z₁ ([ 𝐵 ] y ⊔ z₂ [ conyz₂ ]) z₂
                       (NbhSys.⊑-refl 𝐴) y⊔z₂⊑z₂
        z₁y⊔z₂⊑z₂z₂ = ⊑ᵥ-cons [ 𝐴 × 𝐵 ]
                      ⟪ < z₁ , [ 𝐵 ] y ⊔ z₂ [ conyz₂ ] > ⟫
                      ⟪ < z₁ , z₂ > ⟫ z₁y⊔z₂⊑z₂z₂' ⊑ᵥ-nil
        𝑡𝑥↦z₁y⊔z₂ = Appmap.↦-↓closed 𝑡 z₁y⊔z₂⊑z₂z₂ 𝑡𝑥↦z₁z₂
snd↦-↑directed {𝑥 = 𝑥}
  (snd-intro₂ _ y₁ y₂ 𝑡𝑥↦y₁y₂)
  (snd-intro₂ _ z₁ z₂ 𝑡𝑥↦z₁z₂)
  (con-tup _ _ cony₂z₂ _ _ _)
  with (Appmap.↦-con 𝑡 𝑡𝑥↦y₁y₂ 𝑡𝑥↦z₁z₂ valConRefl)
... | con-tup _ _ (con-pair cony₁z₁ _) _ _ _
  = snd-intro₂ 𝑥 ([ 𝐴 ] y₁ ⊔ z₁ [ cony₁z₁ ]) ([ 𝐵 ] y₂ ⊔ z₂ [ cony₂z₂ ]) 𝑡𝑥↦⊔
  where 𝑡𝑥↦⊔ = Appmap.↦-↑directed 𝑡 𝑡𝑥↦y₁y₂ 𝑡𝑥↦z₁z₂
               (con-tup _ _ (con-pair cony₁z₁ cony₂z₂) _ _ con-nil)

snd↦-con : ∀ {𝑥 𝑦 𝑥′ 𝑦′} → snd↦ 𝑡 𝑥 𝑦 → snd↦ 𝑡 𝑥′ 𝑦′ → ValCon Γ 𝑥 𝑥′ →
           ValCon [ 𝐵 ] 𝑦 𝑦′
snd↦-con (snd-intro₁ _ y y⊑⊥) (snd-intro₁ _ y′ y′⊑⊥) _
  = toValCon (NbhSys.Con-⊔ 𝐵 y⊑⊥ y′⊑⊥)
snd↦-con (snd-intro₁ _ y y⊑⊥) (snd-intro₂ _ y′₁ y′₂ _) _
  = toValCon (NbhSys.Con-⊔ 𝐵 y⊑y′₁ (NbhSys.⊑-refl 𝐵))
  where y⊑y′₁ = NbhSys.⊑-trans 𝐵 y⊑⊥ (NbhSys.⊑-⊥ 𝐵)
snd↦-con (snd-intro₂ _ y₁ y₂ _) (snd-intro₁ _ y′ y′⊑⊥) _
  = toValCon (NbhSys.Con-⊔ 𝐵 (NbhSys.⊑-refl 𝐵) y′₁⊑y)
  where y′₁⊑y = NbhSys.⊑-trans 𝐵 y′⊑⊥ (NbhSys.⊑-⊥ 𝐵)
snd↦-con (snd-intro₂ _ y₁ y₂ 𝑡𝑥↦y₁y₂) (snd-intro₂ _ y′₁ y′₂ 𝑡𝑥′↦y′₁y′₂) con
  with (Appmap.↦-con 𝑡 𝑡𝑥↦y₁y₂ 𝑡𝑥′↦y′₁y′₂ con)
... | con-tup _ _ (con-pair _ cony′₁y′₂) _ _ _ = toValCon cony′₁y′₂
