{-# OPTIONS --safe #-}

open import Base.Core
open import Base.Variables
open import Scwf.DomainScwf.Appmap.Definition
open import Scwf.DomainScwf.ProductStructure.NbhSys.Instance

module Scwf.DomainScwf.ProductStructure.fst.AxiomProofs
  (𝑡 : Term Γ (𝐴 × 𝐵)) where

open import NbhSys.Definition
open import NbhSys.Lemmata
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Lemmata
open import Scwf.DomainScwf.Appmap.Valuation.Relation
open import Scwf.DomainScwf.ProductStructure.NbhSys.Definition
open import Scwf.DomainScwf.ProductStructure.NbhSys.Relation
open import Scwf.DomainScwf.ProductStructure.fst.Relation

fst↦-mono : ∀ {𝑥 𝑦 z} → ⊑ᵥ Γ 𝑥 𝑦 → fst↦ 𝑡 𝑥 z →
            fst↦ 𝑡 𝑦 z
fst↦-mono _ (fst-intro₁ z⊑⊥) =
  fst-intro₁ z⊑⊥
fst↦-mono 𝑥⊑𝑦 (fst-intro₂ 𝑡𝑥↦z₁z₂)
  = fst-intro₂ 𝑡𝑦↦z₁z₂
    where 𝑡𝑦↦z₁z₂ = Appmap.↦-mono 𝑡 𝑥⊑𝑦 𝑡𝑥↦z₁z₂

fst↦-bottom : ∀ {𝑥} → fst↦ 𝑡 𝑥 (NbhSys.⊥ 𝐴)
fst↦-bottom = fst-intro₁ (NbhSys.⊑-refl 𝐴)

fst↦-↓closed : ∀ {𝑥 y z} → [ 𝐴 ] y ⊑ z → fst↦ 𝑡 𝑥 z →
               fst↦ 𝑡 𝑥 y
fst↦-↓closed y⊑z (fst-intro₁ z⊑⊥)
  = fst-intro₁ (NbhSys.⊑-trans 𝐴 y⊑z z⊑⊥)
fst↦-↓closed y⊑z₁ (fst-intro₂ 𝑡𝑥↦z₁z₂)
  = fst-intro₂ 𝑡𝑥↦yz₂
  where yy₂⊑zy₂ = ⊑ₓ-intro₂ y⊑z₁ (NbhSys.⊑-refl 𝐵)
        𝑡𝑥↦yz₂ = Appmap.↦-↓closed 𝑡 yy₂⊑zy₂ 𝑡𝑥↦z₁z₂

fst↦-↑directed : ∀ {𝑥 y z} → fst↦ 𝑡 𝑥 y → fst↦ 𝑡 𝑥 z →
                 ∀ conyz → fst↦ 𝑡 𝑥 ([ 𝐴 ] y ⊔ z [ conyz ])
fst↦-↑directed (fst-intro₁ y⊑⊥) (fst-intro₁ z⊑⊥) conyz
  = fst-intro₁ y⊔z⊑⊥
  where y⊔z⊑⊥ = NbhSys.⊑-⊔ 𝐴 y⊑⊥ z⊑⊥ conyz
fst↦-↑directed (fst-intro₂ 𝑡𝑥↦y₁y₂) (fst-intro₁ z⊑⊥) cony₁z
  = fst-intro₂ 𝑡𝑥→y₁⊔zy₂
  where z⊑y₁ = NbhSys.⊑-trans 𝐴 z⊑⊥ (NbhSys.⊑-⊥ 𝐴)
        y₁⊔z⊑y = NbhSys.⊑-⊔ 𝐴 (NbhSys.⊑-refl 𝐴) z⊑y₁ cony₁z
        y₁⊔zy₂⊑y₁y₂ = ⊑ₓ-intro₂ y₁⊔z⊑y (NbhSys.⊑-refl 𝐵)
        𝑡𝑥→y₁⊔zy₂ = Appmap.↦-↓closed 𝑡 y₁⊔zy₂⊑y₁y₂ 𝑡𝑥↦y₁y₂
fst↦-↑directed {𝑥 = 𝑥} (fst-intro₁ y⊑⊥) (fst-intro₂ 𝑡𝑥↦z₁z₂) conyz₁
  = fst-intro₂ 𝑡𝑥→y⊔z₁z₂
  where y⊑z₁ = NbhSys.⊑-trans 𝐴 y⊑⊥ (NbhSys.⊑-⊥ 𝐴)
        y⊔z₁⊑z₂ = NbhSys.⊑-⊔ 𝐴 y⊑z₁ (NbhSys.⊑-refl 𝐴) conyz₁
        y⊔z₁z₂⊑z₁z₂ = ⊑ₓ-intro₂ y⊔z₁⊑z₂ (NbhSys.⊑-refl 𝐵)
        𝑡𝑥→y⊔z₁z₂ = Appmap.↦-↓closed 𝑡 y⊔z₁z₂⊑z₁z₂ 𝑡𝑥↦z₁z₂
fst↦-↑directed {𝑥 = 𝑥} (fst-intro₂ 𝑡𝑥↦y₁y₂) (fst-intro₂ 𝑡𝑥↦z₁z₂) _
  with (Appmap.↦-con 𝑡 𝑡𝑥↦y₁y₂ 𝑡𝑥↦z₁z₂ valConRefl)
... | con-pair cony₁z₁ cony₂z₂
  = fst-intro₂ 𝑡𝑥↦⊔
  where 𝑡𝑥↦⊔ = Appmap.↦-↑directed 𝑡 𝑡𝑥↦y₁y₂ 𝑡𝑥↦z₁z₂ (con-pair _ cony₂z₂)

fst↦-con : ∀ {𝑥 y 𝑥′ y′} → fst↦ 𝑡 𝑥 y → fst↦ 𝑡 𝑥′ y′ →
           ValCon Γ 𝑥 𝑥′ → NbhSys.Con 𝐴 y y′
fst↦-con (fst-intro₁ y⊑⊥) (fst-intro₁ y′⊑⊥) _
  = NbhSys.Con-⊔ 𝐴 y⊑⊥ y′⊑⊥
fst↦-con (fst-intro₁ y⊑⊥) (fst-intro₂ _) _
  = NbhSys.Con-⊔ 𝐴 y⊑y′₁ (NbhSys.⊑-refl 𝐴)
  where y⊑y′₁ = NbhSys.⊑-trans 𝐴 y⊑⊥ (NbhSys.⊑-⊥ 𝐴)
fst↦-con (fst-intro₂ _) (fst-intro₁ y′⊑⊥) _
  = NbhSys.Con-⊔ 𝐴 (NbhSys.⊑-refl 𝐴) y′₁⊑y
  where y′₁⊑y = NbhSys.⊑-trans 𝐴 y′⊑⊥ (NbhSys.⊑-⊥ 𝐴)
fst↦-con (fst-intro₂ 𝑡𝑥↦y₁y₂)
  (fst-intro₂ 𝑡𝑥′↦y′₁y′₂) con
  with (Appmap.↦-con 𝑡 𝑡𝑥↦y₁y₂ 𝑡𝑥′↦y′₁y′₂ con)
... | con-pair cony₁y₂ _ = cony₁y₂
