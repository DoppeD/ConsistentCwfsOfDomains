{-# OPTIONS --safe #-}

module Scwf.DomainScwf.ProductStructure.Unit.NSub where

open import Appmap.Equivalence
open import Base.Core
open import Base.Variables
open import Scwf.DomainScwf.Appmap.Composition.Instance
open import Scwf.DomainScwf.Appmap.Composition.Relation
open import Scwf.DomainScwf.Appmap.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.ProductStructure.Unit.Mapping.Instance
open import Scwf.DomainScwf.ProductStructure.Unit.Mapping.Relation
open import Scwf.DomainScwf.ProductStructure.Unit.NbhSys.Instance

private
  variable
    γ : tAppmap Δ Γ

ℕ₁-subLemma₁ : ∀ {𝑥 𝑦} → [ 0₁ ∘ γ ] 𝑥 ↦ 𝑦 →
               [ 0₁ ] 𝑥 ↦ 𝑦
ℕ₁-subLemma₁ _ = 0₁↦∀

ℕ₁-subLemma₂ : ∀ {𝑥 𝑦} → [ 0₁ ] 𝑥 ↦ 𝑦 →
               [ 0₁ ∘ γ ] 𝑥 ↦ 𝑦
ℕ₁-subLemma₂ {γ = γ} _
  = ∘↦-intro γ𝑥↦⊥ 0₁↦∀
  where γ𝑥↦⊥ = Appmap.↦-bottom γ

ℕ₁-sub : (0₁ ∘ γ) ≈ 0₁
ℕ₁-sub = ≈-intro (≼-intro ℕ₁-subLemma₁)
         (≼-intro ℕ₁-subLemma₂)
