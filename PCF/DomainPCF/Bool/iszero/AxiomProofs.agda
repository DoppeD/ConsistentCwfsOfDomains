{-# OPTIONS --safe #-}

module PCF.DomainPCF.Bool.iszero.AxiomProofs where

open import Base.Core
open import Base.FinFun
open import Base.Variables
open import NbhSys.Definition
open import PCF.DomainPCF.Nat.NbhSys.Definition
open import PCF.DomainPCF.Nat.NbhSys.Instance
open import PCF.DomainPCF.Bool.iszero.Relation
open import PCF.DomainPCF.Bool.NbhSys.Definition
open import PCF.DomainPCF.Bool.NbhSys.Instance
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Instance
open import Scwf.DomainScwf.ArrowStructure.NbhSys.ConFinFun Nat Bool
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Definition Nat Bool
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Instance
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Post Nat Bool
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Pre Nat Bool
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Relation Nat Bool

--iszero↦-mono' : ∀ {𝑥 𝑦 z} → [ ValNbhSys Γ ] 𝑥 ⊑ 𝑦 →


iszero↦-mono : ∀ {𝑥 𝑦 z} → [ ValNbhSys Γ ] 𝑥 ⊑ 𝑦 →
               𝑥 iszero↦ z → 𝑦 iszero↦ z
iszero↦-mono x iszero↦-intro₁ = iszero↦-intro₁
iszero↦-mono x (iszero↦-intro₂ p) = iszero↦-intro₂ p

iszero↦-bottom : {𝑥 : Valuation Γ} → 𝑥 iszero↦ ⊥ₑ
iszero↦-bottom = iszero↦-intro₁

iszero↦-↓closed' : ∀ {𝑓 𝑓′ con𝑓′} →
                   (∀ {x y} → (x , y) ∈ 𝑓 → ⊑ₑ-proof 𝑓′ con𝑓′ x y) →
                   (∀ {x y} → (x , y) ∈ 𝑓′ → iszeroprop x y) →
                   ∀ {x y} → (x , y) ∈ 𝑓 → iszeroprop x y
iszero↦-↓closed' p₁ p₂ xy∈𝑓 with (p₁ xy∈𝑓)
iszero↦-↓closed' p₁ p₂ xy∈𝑓
  | record { sub = sub
           ; preablesub = preablesub
           ; postablesub = postablesub
           }
  = {!!}

iszero↦-↓closed : {𝑥 : Valuation Γ} → ∀ {y z} → y ⊑ₑ z →
                  𝑥 iszero↦ z → 𝑥 iszero↦ y
iszero↦-↓closed ⊑ₑ-intro₁ iszero↦-intro₁ = iszero↦-intro₁
iszero↦-↓closed ⊑ₑ-intro₁ (iszero↦-intro₂ _) = iszero↦-intro₁
iszero↦-↓closed (⊑ₑ-intro₂ con𝑓 _ p₁) (iszero↦-intro₂ p₂)
  = iszero↦-intro₂ (iszero↦-↓closed' p₁ p₂)

iszero↦-↑directed : {𝑥 : Valuation Γ} → ∀ {y z} →
                    𝑥 iszero↦ y → 𝑥 iszero↦ z →
                    ∀ conyz → 𝑥 iszero↦ (y ⊔ₑ z [ conyz ])
iszero↦-↑directed = {!!}

iszero↦-con : {𝑥 : Valuation Γ} → ∀ {y 𝑥′ y′} →
              𝑥 iszero↦ y → 𝑥′ iszero↦ y′ →
              ValCon _ 𝑥 𝑥′ → ArrCon y y′
iszero↦-con = {!!}
