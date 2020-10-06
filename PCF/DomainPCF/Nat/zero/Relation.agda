module PCF.DomainPCF.Nat.zero.Relation where

open import Base.Core
open import Base.FinFun
open import Base.Variables
open import NbhSys.Definition
open import PCF.DomainPCF.Nat.NbhSys.Definition
open import PCF.DomainPCF.Nat.NbhSys.Instance
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Definition

data _zero↦_ : Valuation Γ → ArrNbh Nat Nat → Set where
  zero↦-intro₁ : {𝑥 : Valuation Γ} → 𝑥 zero↦ ⊥ₑ
  zero↦-intro₂ : {𝑥 : Valuation Γ} → ∀ {𝑓 con𝑓} →
                 (∀ {x y} → (x , y) ∈ 𝑓 → [ Nat ] y ⊑ 0ₙ) →
                 𝑥 zero↦ (𝐹 𝑓 con𝑓)
