{-# OPTIONS --safe #-}

module PCF.DomainPCF.Functions.pred.Relation where

open import Base.Core
open import Base.FinFun
open import Base.Variables
open import NbhSys.Definition
open import PCF.DomainPCF.Nat.NbhSys.Definition
open import PCF.DomainPCF.Nat.NbhSys.Instance
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Definition

data predprop (x y : NatNbh) : Set where
  pprop₁ : [ Nat ] x ⊑ 0ₙ → [ Nat ] y ⊑ ⊥ₙ → predprop x y
  pprop₂ : [ Nat ] (sₙ y) ⊑ x → predprop x y

data _pred↦_ : Valuation Γ → ArrNbh Nat Nat → Set where
  pred↦-intro₁ : {𝑥 : Valuation Γ} → 𝑥 pred↦ ⊥ₑ
  pred↦-intro₂ : {𝑥 : Valuation Γ} → ∀ {𝑓 con𝑓} →
                 (∀ {x y} → (x , y) ∈ 𝑓 → predprop x y) →
                 𝑥 pred↦ (𝐹 𝑓 con𝑓)
