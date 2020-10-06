module PCF.DomainPCF.Bool.false.Relation where

open import Base.Variables
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import PCF.DomainPCF.Bool.NbhSys.Definition
open import PCF.DomainPCF.Bool.NbhSys.Relation

data _false↦_ : Valuation Γ → BoolNbh → Set where
  false↦-intro : {𝑥 : Valuation Γ} → ∀ {y} →
                y ⊑b f → 𝑥 false↦ y
