module PCF.DomainPCF.Bool.true.AxiomProofs where

open import Base.Variables hiding (n)
open import NbhSys.Definition
open import PCF.DomainPCF.Bool.NbhSys.AxiomProofs
open import PCF.DomainPCF.Bool.NbhSys.Definition
open import PCF.DomainPCF.Bool.NbhSys.Relation
open import PCF.DomainPCF.Bool.true.Relation
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Instance

true↦-mono : ∀ {𝑥 𝑦 z} → [ ValNbhSys Γ ] 𝑥 ⊑ 𝑦 → 𝑥 true↦ z →
            𝑦 true↦ z
true↦-mono _ (true↦-intro z⊑t) = true↦-intro z⊑t

true↦-bottom : {𝑥 : Valuation Γ} → 𝑥 true↦ ⊥b
true↦-bottom = true↦-intro ⊑b-intro₁

true↦-↓closed : {𝑥 : Valuation Γ} → ∀ {y z} → y ⊑b z →
               𝑥 true↦ z → 𝑥 true↦ y
true↦-↓closed y⊑z (true↦-intro z⊑t)
  = true↦-intro (⊑b-trans y⊑z z⊑t)

true↦-↑directed : {𝑥 : Valuation Γ} → ∀ {y z} → 𝑥 true↦ y →
                 𝑥 true↦ z → ∀ conyz →
                 𝑥 true↦ (y ⊔b z [ conyz ])
true↦-↑directed (true↦-intro y⊑t) (true↦-intro z⊑t) conyz
  = true↦-intro (⊑b-⊔ y⊑t z⊑t conyz)

true↦-con : {𝑥 : Valuation Γ} → ∀ {y 𝑥′ y′} →
           𝑥 true↦ y → 𝑥′ true↦ y′ →
           ValCon _ 𝑥 𝑥′ → Conb y y′
true↦-con (true↦-intro y⊑t) (true↦-intro y′⊑t) _
  = Conb-⊔ y⊑t y′⊑t
