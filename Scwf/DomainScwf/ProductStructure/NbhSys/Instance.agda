{-# OPTIONS --safe #-}

module Scwf.DomainScwf.ProductStructure.NbhSys.Instance where

open import Base.Core
open import Base.Variables
open import NbhSys.Definition
open import Scwf.DomainScwf.ProductStructure.NbhSys.AxiomProofs
open import Scwf.DomainScwf.ProductStructure.NbhSys.Definition
open import Scwf.DomainScwf.ProductStructure.NbhSys.Relation

_×_ : NbhSys → NbhSys → NbhSys
NbhSys.Nbh (d₁ × d₂)     = ProdNbh d₁ d₂
NbhSys._⊑_ (d₁ × d₂)     = _⊑ₓ_ d₁ d₂
NbhSys.Con (d₁ × d₂)     = ProdCon d₁ d₂
NbhSys._⊔_[_] (d₁ × d₂)  = _⊔ₓ_[_] d₁ d₂
NbhSys.⊥ (d₁ × d₂)       = ⊥ₓ
NbhSys.Con-⊔ (d₁ × d₂)   = Con-⊔ₓ d₁ d₂
NbhSys.⊑-refl (d₁ × d₂)  = ⊑ₓ-refl d₁ d₂
NbhSys.⊑-trans (d₁ × d₂) = ⊑ₓ-trans d₁ d₂
NbhSys.⊑-⊥ (d₁ × d₂)     = ⊑ₓ-⊥ d₁ d₂
NbhSys.⊑-⊔ (d₁ × d₂)     = ⊑ₓ-⊔ d₁ d₂
NbhSys.⊑-⊔-fst (d₁ × d₂) = ⊑ₓ-⊔-fst d₁ d₂
NbhSys.⊑-⊔-snd (d₁ × d₂) = ⊑ₓ-⊔-snd d₁ d₂
