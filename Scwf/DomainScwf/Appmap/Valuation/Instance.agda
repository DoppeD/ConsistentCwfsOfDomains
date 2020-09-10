{-# OPTIONS --safe #-}

module Scwf.DomainScwf.Appmap.Valuation.Instance where

open import Base.Core
open import Base.Variables
open import NbhSys.Definition
open import Scwf.DomainScwf.Appmap.Valuation.AxiomProofs
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Relation

ValNbhSys : (Γ : Ctx n) → NbhSys
NbhSys.Nbh (ValNbhSys Γ)     = Valuation Γ
NbhSys._⊑_ (ValNbhSys Γ)     = ⊑ᵥ Γ
NbhSys.Con (ValNbhSys Γ)     = ValCon Γ
NbhSys._⊔_[_] (ValNbhSys Γ)  = _⊔ᵥ_[_]
NbhSys.⊥ (ValNbhSys Γ)       = ⊥ᵥ
NbhSys.Con-⊔ (ValNbhSys Γ)   = Con-⊔ᵥ
NbhSys.⊑-refl (ValNbhSys Γ)  = ⊑ᵥ-refl
NbhSys.⊑-trans (ValNbhSys Γ) = ⊑ᵥ-trans
NbhSys.⊑-⊥ (ValNbhSys Γ)     = ⊑ᵥ-⊥
NbhSys.⊑-⊔ (ValNbhSys Γ)     = ⊑ᵥ-⊔
NbhSys.⊑-⊔-fst (ValNbhSys Γ) = ⊑ᵥ-⊔-fst
NbhSys.⊑-⊔-snd (ValNbhSys Γ) = ⊑ᵥ-⊔-snd
