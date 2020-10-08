{-# OPTIONS --safe #-}

module PCF.DomainPCF.Bool.iszero.Relation where

open import Base.Core
open import Base.FinFun
open import Base.Variables
open import NbhSys.Definition
open import PCF.DomainPCF.Nat.NbhSys.Definition
open import PCF.DomainPCF.Nat.NbhSys.Instance
open import PCF.DomainPCF.Bool.NbhSys.Definition
open import PCF.DomainPCF.Bool.NbhSys.Instance
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Definition

data iszeroprop (x : NatNbh) (y : BoolNbh) : Set where
  izprop₁ : [ Bool ] y ⊑ ⊥b → iszeroprop x y
  izprop₂ : [ Nat ] 0ₙ ⊑ x → [ Bool ] t ⊑ y →
            iszeroprop x y
  izprop₃ : [ Nat ] sₙ ⊥ₙ ⊑ x → [ Bool ] f ⊑ y →
            iszeroprop x y

data _iszero↦_ : Valuation Γ → ArrNbh Nat Bool → Set where
  iszero↦-intro₁ : {𝑥 : Valuation Γ} → 𝑥 iszero↦ ⊥ₑ
  iszero↦-intro₂ : {𝑥 : Valuation Γ} → ∀ {𝑓 con𝑓} →
                   (∀ {x y} → (x , y) ∈ 𝑓 → iszeroprop x y) →
                   𝑥 iszero↦ (𝐹 𝑓 con𝑓)
