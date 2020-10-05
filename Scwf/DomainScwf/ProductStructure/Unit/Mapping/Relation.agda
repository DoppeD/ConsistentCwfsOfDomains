{-# OPTIONS --safe #-}

module Scwf.DomainScwf.ProductStructure.Unit.Mapping.Relation where

open import Base.Core
open import Base.Variables
open import NbhSys.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.ProductStructure.Unit.NbhSys.Definition
open import Scwf.DomainScwf.ProductStructure.Unit.NbhSys.Instance

data _0₁↦_ {Γ : Ctx n} : Valuation Γ → NbhSys.Nbh ℕ₁ →
                         Set where
  0₁↦∀ : ∀ {𝑥 𝑦} → 𝑥 0₁↦ 𝑦

0₁↦-con : ∀ {𝑥 y 𝑥′ y′} → 𝑥 0₁↦ y → 𝑥′ 0₁↦ y′ →
          ValCon Γ 𝑥 𝑥′ → NbhSys.Con ℕ₁ y y′
0₁↦-con _ _ _ = allCon
