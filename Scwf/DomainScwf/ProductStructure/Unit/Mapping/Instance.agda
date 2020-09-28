{-# OPTIONS --safe #-}

module Scwf.DomainScwf.ProductStructure.Unit.Mapping.Instance where

open import Base.Core
open import Base.Variables
open import Scwf.DomainScwf.Appmap.Definition
open import Scwf.DomainScwf.ProductStructure.Unit.Mapping.Relation
open import Scwf.DomainScwf.ProductStructure.Unit.NbhSys.Instance

0₁ : tAppmap Γ [ ℕ₁ ]
Appmap._↦_ 0₁         = _0₁↦_
Appmap.↦-mono 0₁      = λ _ _ → 0₁↦∀
Appmap.↦-bottom 0₁    = 0₁↦∀
Appmap.↦-↓closed 0₁   = λ _ _ → 0₁↦∀
Appmap.↦-↑directed 0₁ = λ _ _ _ → 0₁↦∀
Appmap.↦-con 0₁       = 0₁↦-con
