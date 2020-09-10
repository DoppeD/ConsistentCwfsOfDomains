{-# OPTIONS --safe #-}

module Scwf.DomainScwf.Appmap.Valuation.Relation where

open import Base.Core
open import Base.Variables
open import NbhSys.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Definition

open import Agda.Builtin.Nat

data ⊑ᵥ : (Γ : Ctx n) → (𝑥 𝑦 : Valuation Γ) →
          Set where
  ⊑ᵥ-nil : ⊑ᵥ [] ⟪⟫ ⟪⟫
  ⊑ᵥ-cons : (Γ : Ctx (suc n)) → ∀ 𝑥 𝑦 →
            [ head Γ ] (ctHead 𝑥) ⊑ (ctHead 𝑦) →
            ⊑ᵥ (tail Γ) (ctTail 𝑥) (ctTail 𝑦) →
            ⊑ᵥ Γ 𝑥 𝑦
