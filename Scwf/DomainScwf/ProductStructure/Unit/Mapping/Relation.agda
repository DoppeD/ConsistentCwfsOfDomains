{-# OPTIONS --safe #-}

module Scwf.DomainScwf.ProductStructure.Unit.Mapping.Relation where

open import Base.Core
open import Base.Variables
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.ProductStructure.Unit.NbhSys.Definition
open import Scwf.DomainScwf.ProductStructure.Unit.NbhSys.Instance

data _0₁↦_ {Γ : Ctx n} : Valuation Γ → Valuation [ ℕ₁ ] →
                         Set where
  0₁↦∀ : ∀ {𝑥 𝑦} → 𝑥 0₁↦ 𝑦

0₁↦-con : ∀ {𝑥 𝑦 𝑥′ 𝑦′} → 𝑥 0₁↦ 𝑦 → 𝑥′  0₁↦ 𝑦′ →
          ValCon Γ 𝑥 𝑥′ → ValCon _ 𝑦 𝑦′
0₁↦-con {𝑦 = ⟪ _ ,, ⟪⟫ ⟫} {𝑦′ = ⟪ _ ,, ⟪⟫ ⟫} _ _ _
  = con-tup allCon con-nil
