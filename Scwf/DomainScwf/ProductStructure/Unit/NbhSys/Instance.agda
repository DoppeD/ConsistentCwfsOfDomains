{-# OPTIONS --safe #-}

module Scwf.DomainScwf.ProductStructure.Unit.NbhSys.Instance where

open import NbhSys.Definition
open import Scwf.DomainScwf.ProductStructure.Unit.NbhSys.AxiomProofs
open import Scwf.DomainScwf.ProductStructure.Unit.NbhSys.Definition

ℕ₁ : NbhSys
NbhSys.Nbh ℕ₁     = UnitNbh
NbhSys._⊑_ ℕ₁     = _⊑₁_
NbhSys.Con ℕ₁     = UnitCon
NbhSys._⊔_[_] ℕ₁  = _⊔₁_[_]
NbhSys.⊥ ℕ₁       = ⊥₁
NbhSys.Con-⊔ ℕ₁   = Con-⊔₁
NbhSys.⊑-refl ℕ₁  = ⊑₁-refl
NbhSys.⊑-trans ℕ₁ = ⊑₁-trans
NbhSys.⊑-⊥ ℕ₁     = ⊑₁-⊥
NbhSys.⊑-⊔ ℕ₁     = ⊑₁-⊔
NbhSys.⊑-⊔-fst ℕ₁ = ⊑₁-⊔-fst
NbhSys.⊑-⊔-snd ℕ₁ = ⊑₁-⊔-snd
