module PCF.DomainPCF.Bool.NbhSys.Relation where

open import PCF.DomainPCF.Bool.NbhSys.Definition

data _⊑b_ : BoolNbh → BoolNbh → Set where
  ⊑b-intro₁ : ∀ {x} → ⊥b ⊑b x
  ⊑b-intro₂ : ∀ {x} → x ⊑b x
