{-# OPTIONS --safe #-}

module Scwf.DomainScwf.Comprehension.q.AxiomProofs where

open import Base.Core
open import Base.Variables
open import NbhSys.Definition
open import NbhSys.Lemmata
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Instance
open import Scwf.DomainScwf.Appmap.Valuation.Relation
open import Scwf.DomainScwf.Comprehension.q.Relation

q↦-mono : ∀ {𝑥 𝑦} → {𝑧 : Valuation [ 𝐴 ]} →
          ⊑ᵥ (𝐴 :: Γ) 𝑥 𝑦 → 𝑥 q↦ 𝑧 →
          𝑦 q↦ 𝑧
q↦-mono {𝐴} (⊑ᵥ-cons _ x⊑y _) (q↦-intro z⊑x)
  = q↦-intro (NbhSys.⊑-trans 𝐴 z⊑x x⊑y)

q↦-bottom : {𝑥 : Valuation (𝐴 :: Γ)} → 𝑥 q↦ ⊥ᵥ
q↦-bottom {𝐴 = 𝐴} = q↦-intro (NbhSys.⊑-⊥ 𝐴)

q↦-↓closed : {𝑥 : Valuation (𝐴 :: Γ)} → ∀ {𝑦 𝑧} →
             ⊑ᵥ [ 𝐴 ] 𝑦 𝑧 → 𝑥 q↦ 𝑧 → 𝑥 q↦ 𝑦
q↦-↓closed {𝐴 = 𝐴} (⊑ᵥ-cons _ y⊑z _) (q↦-intro z⊑x)
  = q↦-intro (NbhSys.⊑-trans 𝐴 y⊑z z⊑x)

q↦-↑directed : {𝑥 : Valuation (𝐴 :: Γ)} → ∀ {𝑦 𝑧} →
               𝑥 q↦ 𝑦 → 𝑥 q↦ 𝑧 → ∀ con𝑦𝑧 →
               𝑥 q↦ (𝑦 ⊔ᵥ 𝑧 [ con𝑦𝑧 ])
q↦-↑directed {𝐴 = 𝐴} {𝑥 = ⟪ x ,, 𝑥 ⟫} {⟪ y ,, ⟪⟫ ⟫} {⟪ z ,, ⟪⟫ ⟫}
  (q↦-intro y⊑x) (q↦-intro z⊑x) (con-tup conyz con-nil)
  = q↦-intro y⊔z⊑x
  where y⊔z⊑x = NbhSys.⊑-⊔ 𝐴 y⊑x z⊑x conyz

q↦-con : {𝑥 : Valuation (𝐴 :: Γ)} → ∀ {𝑦 𝑥′ 𝑦′} →
         𝑥 q↦ 𝑦 → 𝑥′ q↦ 𝑦′ →
         ValCon _ 𝑥 𝑥′ → ValCon _ 𝑦 𝑦′
q↦-con {𝐴 = 𝐴} {𝑦 = ⟪ y ,, ⟪⟫ ⟫} {𝑦′ = ⟪ y′ ,, ⟪⟫ ⟫}
  (q↦-intro y⊑x) (q↦-intro y′⊑x′) (con-tup conxx′ con𝑥𝑥′)
  = NbhSys.Con-⊔ (ValNbhSys _) {z = ⟪ [ 𝐴 ] _ ⊔ _ [ conxx′ ] ⟫}
    y⊑x⊔x′ᵥ y′⊑x⊔x′ᵥ
  where y⊑x⊔x′ = ⊑-⊔-lemma₄ 𝐴 y⊑x conxx′
        y⊑x⊔x′ᵥ = ⊑ᵥ-cons [ 𝐴 ] y⊑x⊔x′ ⊑ᵥ-nil
        y′⊑x⊔x′ = ⊑-⊔-lemma₅ 𝐴 y′⊑x′ conxx′
        y′⊑x⊔x′ᵥ = ⊑ᵥ-cons [ 𝐴 ] y′⊑x⊔x′ ⊑ᵥ-nil
