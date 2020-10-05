module PCF.DomainPCF.Nat.zero.Relation where

open import PCF.DomainPCF.Nat.NbhSys.Definition
open import PCF.DomainPCF.Nat.NbhSys.Relation

data _zero↦_ : NatNbh → NatNbh → Set where
  zero-intro : ∀ {x y} → y ⊑ₙ 0ₙ → x zero↦ y
