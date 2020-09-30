{-# OPTIONS --safe #-}

open import Base.Core
open import Base.Variables
open import Scwf.DomainScwf.Appmap.Definition
open import Scwf.DomainScwf.ProductStructure.NbhSys.Instance

module Scwf.DomainScwf.ProductStructure.fst.AxiomProofs
  (𝑡 : tAppmap Γ [ 𝐴 × 𝐵 ]) where

open import NbhSys.Definition
open import NbhSys.Lemmata
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Lemmata
open import Scwf.DomainScwf.Appmap.Valuation.Relation
open import Scwf.DomainScwf.ProductStructure.NbhSys.Definition
open import Scwf.DomainScwf.ProductStructure.NbhSys.Relation
open import Scwf.DomainScwf.ProductStructure.fst.Relation

fst↦-mono : ∀ {𝑥 𝑦 𝑧} → ⊑ᵥ Γ 𝑥 𝑦 → fst↦ 𝑡 𝑥 𝑧 →
            fst↦ 𝑡 𝑦 𝑧
fst↦-mono {𝑦 = 𝑦} _ (fst-intro₁ z⊑⊥) =
  fst-intro₁ z⊑⊥
fst↦-mono {𝑦 = 𝑦} 𝑥⊑𝑦 (fst-intro₂ 𝑡𝑥↦z₁z₂)
  = fst-intro₂ 𝑡𝑦↦z₁z₂
    where 𝑡𝑦↦z₁z₂ = Appmap.↦-mono 𝑡 𝑥⊑𝑦 𝑡𝑥↦z₁z₂

fst↦-bottom : ∀ {𝑥} → fst↦ 𝑡 𝑥 ⟪ NbhSys.⊥ 𝐴 ⟫
fst↦-bottom {𝑥 = 𝑥} = fst-intro₁ (NbhSys.⊑-refl 𝐴)

fst↦-↓closed : ∀ {𝑥 𝑦 𝑧} → ⊑ᵥ [ 𝐴 ] 𝑦 𝑧 → fst↦ 𝑡 𝑥 𝑧 →
               fst↦ 𝑡 𝑥 𝑦
fst↦-↓closed {𝑥 = 𝑥} {⟪ y ,, ⟪⟫ ⟫}
  (⊑ᵥ-cons _ y⊑z ⊑ᵥ-nil) (fst-intro₁ z⊑⊥)
  = fst-intro₁ (NbhSys.⊑-trans 𝐴 y⊑z z⊑⊥)
fst↦-↓closed {𝑥 = 𝑥} {⟪ y ,, ⟪⟫ ⟫}
  (⊑ᵥ-cons _ y⊑z₁ ⊑ᵥ-nil) (fst-intro₂ 𝑡𝑥↦z₁z₂)
  = fst-intro₂ 𝑡𝑥↦yz₂
  where yz₂⊑z₁z₂' = ⊑ₓ-intro₂ y⊑z₁ (NbhSys.⊑-refl 𝐵)
        yz₂⊑z₁z₂ = ⊑ᵥ-cons [ 𝐴 × 𝐵 ] yz₂⊑z₁z₂' ⊑ᵥ-nil
        𝑡𝑥↦yz₂ = Appmap.↦-↓closed 𝑡 yz₂⊑z₁z₂ 𝑡𝑥↦z₁z₂

fst↦-↑directed : ∀ {𝑥 𝑦 𝑧} → fst↦ 𝑡 𝑥 𝑦 → fst↦ 𝑡 𝑥 𝑧 →
                 (con : ValCon [ 𝐴 ] 𝑦 𝑧) → fst↦ 𝑡 𝑥 (𝑦 ⊔ᵥ 𝑧 [ con ])
fst↦-↑directed (fst-intro₁ y⊑⊥) (fst-intro₁ z⊑⊥)
  (con-tup conyz _)
  = fst-intro₁ y⊔z⊑⊥
  where y⊔z⊑⊥ = NbhSys.⊑-⊔ 𝐴 y⊑⊥ z⊑⊥ conyz
fst↦-↑directed (fst-intro₂ 𝑡𝑥↦y₁y₂)
  (fst-intro₁ z⊑⊥) (con-tup cony₁z _)
  = fst-intro₂ 𝑡𝑥→y₁⊔zy₂
  where z⊑y₁ = NbhSys.⊑-trans 𝐴 z⊑⊥ (NbhSys.⊑-⊥ 𝐴)
        y₁⊔z⊑y = NbhSys.⊑-⊔ 𝐴 (NbhSys.⊑-refl 𝐴) z⊑y₁ cony₁z
        y₁⊔zy₂⊑y₁y₂' = ⊑ₓ-intro₂ y₁⊔z⊑y (NbhSys.⊑-refl 𝐵)
        y₁⊔zy₂⊑y₁y₂ = ⊑ᵥ-cons [ 𝐴 × 𝐵 ] y₁⊔zy₂⊑y₁y₂' ⊑ᵥ-nil
        𝑡𝑥→y₁⊔zy₂ = Appmap.↦-↓closed 𝑡 y₁⊔zy₂⊑y₁y₂ 𝑡𝑥↦y₁y₂
fst↦-↑directed {𝑥 = 𝑥} (fst-intro₁ y⊑⊥)
  (fst-intro₂ 𝑡𝑥↦z₁z₂) (con-tup conyz₁ _)
  = fst-intro₂ 𝑡𝑥→y⊔z₁z₂
  where y⊑z₁ = NbhSys.⊑-trans 𝐴 y⊑⊥ (NbhSys.⊑-⊥ 𝐴)
        y⊔z₁⊑z₂ = NbhSys.⊑-⊔ 𝐴 y⊑z₁ (NbhSys.⊑-refl 𝐴) conyz₁
        y⊔z₁z₂⊑z₁z₂' = ⊑ₓ-intro₂ y⊔z₁⊑z₂ (NbhSys.⊑-refl 𝐵)
        y⊔z₁z₂⊑z₁z₂ = ⊑ᵥ-cons [ 𝐴 × 𝐵 ] y⊔z₁z₂⊑z₁z₂' ⊑ᵥ-nil
        𝑡𝑥→y⊔z₁z₂ = Appmap.↦-↓closed 𝑡 y⊔z₁z₂⊑z₁z₂ 𝑡𝑥↦z₁z₂
fst↦-↑directed {𝑥 = 𝑥} (fst-intro₂ 𝑡𝑥↦y₁y₂)
  (fst-intro₂ 𝑡𝑥↦z₁z₂) (con-tup _ _)
  with (Appmap.↦-con 𝑡 𝑡𝑥↦y₁y₂ 𝑡𝑥↦z₁z₂ valConRefl)
... | con-tup (con-pair cony₁z₁ cony₂z₂) _
  = fst-intro₂ 𝑡𝑥↦⊔
  where 𝑡𝑥↦⊔ = Appmap.↦-↑directed 𝑡 𝑡𝑥↦y₁y₂ 𝑡𝑥↦z₁z₂
               (con-tup (con-pair _ cony₂z₂) con-nil)

fst↦-con : ∀ {𝑥 𝑦 𝑥′ 𝑦′} → fst↦ 𝑡 𝑥 𝑦 → fst↦ 𝑡 𝑥′ 𝑦′ →
           ValCon Γ 𝑥 𝑥′ → ValCon [ 𝐴 ] 𝑦 𝑦′
fst↦-con (fst-intro₁ y⊑⊥) (fst-intro₁ y′⊑⊥) _
  = toValCon (NbhSys.Con-⊔ 𝐴 y⊑⊥ y′⊑⊥)
fst↦-con (fst-intro₁ y⊑⊥) (fst-intro₂ _) _
  = toValCon (NbhSys.Con-⊔ 𝐴 y⊑y′₁ (NbhSys.⊑-refl 𝐴))
  where y⊑y′₁ = NbhSys.⊑-trans 𝐴 y⊑⊥ (NbhSys.⊑-⊥ 𝐴)
fst↦-con (fst-intro₂ _) (fst-intro₁ y′⊑⊥) _
  = toValCon (NbhSys.Con-⊔ 𝐴 (NbhSys.⊑-refl 𝐴) y′₁⊑y)
  where y′₁⊑y = NbhSys.⊑-trans 𝐴 y′⊑⊥ (NbhSys.⊑-⊥ 𝐴)
fst↦-con (fst-intro₂ 𝑡𝑥↦y₁y₂)
  (fst-intro₂ 𝑡𝑥′↦y′₁y′₂) con
  with (Appmap.↦-con 𝑡 𝑡𝑥↦y₁y₂ 𝑡𝑥′↦y′₁y′₂ con)
... | con-tup (con-pair cony₁y₂ _) _ = toValCon cony₁y₂
