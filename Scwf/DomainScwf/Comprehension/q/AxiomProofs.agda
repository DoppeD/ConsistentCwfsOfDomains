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

q↦-mono : ∀ {𝑥 𝑦 z} →
          ⊑ᵥ (𝐴 :: Γ) 𝑥 𝑦 → 𝑥 q↦ z →
          𝑦 q↦ z
q↦-mono {𝐴} (⊑ᵥ-cons _ x⊑y _) (q↦-intro z⊑x)
  = q↦-intro (NbhSys.⊑-trans 𝐴 z⊑x x⊑y)

q↦-bottom : {𝑥 : Valuation (𝐴 :: Γ)} → 𝑥 q↦ (NbhSys.⊥ 𝐴)
q↦-bottom {𝐴 = 𝐴} = q↦-intro (NbhSys.⊑-⊥ 𝐴)

q↦-↓closed : {𝑥 : Valuation (𝐴 :: Γ)} → ∀ {y z} →
             [ 𝐴 ] y ⊑ z → 𝑥 q↦ z → 𝑥 q↦ y
q↦-↓closed {𝐴 = 𝐴} y⊑z (q↦-intro z⊑x)
  = q↦-intro (NbhSys.⊑-trans 𝐴 y⊑z z⊑x)

q↦-↑directed : {𝑥 : Valuation (𝐴 :: Γ)} → ∀ {y z} →
               𝑥 q↦ y → 𝑥 q↦ z → ∀ conyz →
               𝑥 q↦ ([ 𝐴 ] y ⊔ z [ conyz ])
q↦-↑directed {𝐴 = 𝐴} {𝑥 = ⟪ x ,, 𝑥 ⟫} {y} {z}
  (q↦-intro y⊑x) (q↦-intro z⊑x) conyz
  = q↦-intro y⊔z⊑x
  where y⊔z⊑x = NbhSys.⊑-⊔ 𝐴 y⊑x z⊑x conyz

q↦-con : {𝑥 : Valuation (𝐴 :: Γ)} → ∀ {y 𝑥′ y′} →
         𝑥 q↦ y → 𝑥′ q↦ y′ →
         ValCon _ 𝑥 𝑥′ → NbhSys.Con 𝐴 y y′
q↦-con {𝐴 = 𝐴} {y = y} {y′ = y′}
  (q↦-intro y⊑x) (q↦-intro y′⊑x′) (con-tup conxx′ con𝑥𝑥′)
  = NbhSys.Con-⊔ 𝐴 y⊑x⊔x′ y′⊑x⊔x′
  where y⊑x⊔x′ = ⊑-⊔-lemma₄ 𝐴 y⊑x conxx′
        y′⊑x⊔x′ = ⊑-⊔-lemma₅ 𝐴 y′⊑x′ conxx′
