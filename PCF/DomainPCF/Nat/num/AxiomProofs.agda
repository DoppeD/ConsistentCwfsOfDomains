open import Agda.Builtin.Nat renaming (Nat to AgdaNat)

module PCF.DomainPCF.Nat.num.AxiomProofs (n : AgdaNat) where

open import Base.Variables hiding (n)
open import NbhSys.Definition
open import PCF.DomainPCF.Nat.NbhSys.AxiomProofs
open import PCF.DomainPCF.Nat.NbhSys.Definition
open import PCF.DomainPCF.Nat.NbhSys.Relation
open import PCF.DomainPCF.Nat.num.Relation n
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Instance

num↦-mono : ∀ {𝑥 𝑦 z} → [ ValNbhSys Γ ] 𝑥 ⊑ 𝑦 → 𝑥 num↦ z →
            𝑦 num↦ z
num↦-mono _ (num↦-intro z⊑n) = num↦-intro z⊑n

num↦-bottom : {𝑥 : Valuation Γ} → 𝑥 num↦ ⊥ₙ
num↦-bottom = num↦-intro ⊑ₙ-intro₁

num↦-↓closed : {𝑥 : Valuation Γ} → ∀ {y z} → y ⊑ₙ z →
               𝑥 num↦ z → 𝑥 num↦ y
num↦-↓closed y⊑z (num↦-intro z⊑n)
  = num↦-intro (⊑ₙ-trans y⊑z z⊑n)

num↦-↑directed : {𝑥 : Valuation Γ} → ∀ {y z} → 𝑥 num↦ y →
                 𝑥 num↦ z → ∀ conyz →
                 𝑥 num↦ (y ⊔ₙ z [ conyz ])
num↦-↑directed (num↦-intro y⊑n) (num↦-intro z⊑n) conyz
  = num↦-intro (⊑ₙ-⊔ y⊑n z⊑n conyz)

num↦-con : {𝑥 : Valuation Γ} → ∀ {y 𝑥′ y′} →
           𝑥 num↦ y → 𝑥′ num↦ y′ →
           ValCon _ 𝑥 𝑥′ → Conₙ y y′
num↦-con (num↦-intro y⊑n) (num↦-intro y′⊑n) _
  = Conₙ-⊔ y⊑n y′⊑n
