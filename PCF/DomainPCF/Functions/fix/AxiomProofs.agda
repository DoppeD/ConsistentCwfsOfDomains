open import Base.Core

module PCF.DomainPCF.Functions.fix.AxiomProofs
  {𝐴 : Ty} where

open import Base.Variables hiding (𝐴)
open import NbhSys.Definition
open import PCF.DomainPCF.Functions.fix.Relation 𝐴
open import PCF.DomainPCF.Nat.NbhSys.Instance
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Instance
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Definition
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Instance
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Relation

fix↦-mono : ∀ {𝑥 𝑦 z} → [ ValNbhSys Γ ] 𝑥 ⊑ 𝑦 →
            𝑥 fix↦ z → 𝑦 fix↦ z
fix↦-mono x fix↦-intro₁ = fix↦-intro₁
fix↦-mono x (fix↦-intro₂ p) = fix↦-intro₂ p

fix↦-bottom : {𝑥 : Valuation Γ} → 𝑥 fix↦ ⊥ₑ
fix↦-bottom = fix↦-intro₁

fix↦-↓closed : {𝑥 : Valuation Γ} → ∀ {y z} →
               [ (𝐴 ⇒ 𝐴) ⇒ 𝐴 ] y ⊑ z →
               𝑥 fix↦ z → 𝑥 fix↦ y
fix↦-↓closed ⊑ₑ-intro₁ _ = fix↦-intro₁
fix↦-↓closed (⊑ₑ-intro₂ _ _ p₁) (fix↦-intro₂ p₂)
  = {!!}
