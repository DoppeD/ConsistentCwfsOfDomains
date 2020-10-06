module PCF.DomainPCF.Bool.true.Relation where

open import Base.Variables
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import PCF.DomainPCF.Bool.NbhSys.Definition
open import PCF.DomainPCF.Bool.NbhSys.Relation

data _true↦_ : Valuation Γ → BoolNbh → Set where
  true↦-intro : {𝑥 : Valuation Γ} → ∀ {y} →
                y ⊑b t → 𝑥 true↦ y
