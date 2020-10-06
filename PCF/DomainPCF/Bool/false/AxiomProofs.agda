module PCF.DomainPCF.Bool.false.AxiomProofs where

open import Base.Variables
open import NbhSys.Definition
open import PCF.DomainPCF.Bool.NbhSys.AxiomProofs
open import PCF.DomainPCF.Bool.NbhSys.Definition
open import PCF.DomainPCF.Bool.NbhSys.Relation
open import PCF.DomainPCF.Bool.false.Relation
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Instance

false↦-mono : ∀ {𝑥 𝑦 z} → [ ValNbhSys Γ ] 𝑥 ⊑ 𝑦 → 𝑥 false↦ z →
            𝑦 false↦ z
false↦-mono _ (false↦-intro z⊑f) = false↦-intro z⊑f

false↦-bottom : {𝑥 : Valuation Γ} → 𝑥 false↦ ⊥b
false↦-bottom = false↦-intro ⊑b-intro₁

false↦-↓closed : {𝑥 : Valuation Γ} → ∀ {y z} → y ⊑b z →
               𝑥 false↦ z → 𝑥 false↦ y
false↦-↓closed y⊑z (false↦-intro z⊑f)
  = false↦-intro (⊑b-trans y⊑z z⊑f)

false↦-↑directed : {𝑥 : Valuation Γ} → ∀ {y z} → 𝑥 false↦ y →
                 𝑥 false↦ z → ∀ conyz →
                 𝑥 false↦ (y ⊔b z [ conyz ])
false↦-↑directed (false↦-intro y⊑f) (false↦-intro z⊑f) conyz
  = false↦-intro (⊑b-⊔ y⊑f z⊑f conyz)

false↦-con : {𝑥 : Valuation Γ} → ∀ {y 𝑥′ y′} →
           𝑥 false↦ y → 𝑥′ false↦ y′ →
           ValCon _ 𝑥 𝑥′ → Conb y y′
false↦-con (false↦-intro y⊑f) (false↦-intro y′⊑f) _
  = Conb-⊔ y⊑f y′⊑f
