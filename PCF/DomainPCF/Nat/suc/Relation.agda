module PCF.DomainPCF.Nat.suc.Relation where

open import PCF.DomainPCF.Nat.NbhSys.Definition
open import PCF.DomainPCF.Nat.NbhSys.Relation

data _suc↦_ : NatNbh → NatNbh → Set where
  suc↦-intro : ∀ {x y} → y ⊑ₙ (sₙ x) → x suc↦ y
