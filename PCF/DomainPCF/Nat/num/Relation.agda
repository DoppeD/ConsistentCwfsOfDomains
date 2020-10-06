open import Agda.Builtin.Nat renaming (Nat to AgdaNat)

module PCF.DomainPCF.Nat.num.Relation (n : AgdaNat) where

open import Base.Variables hiding (n)
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import PCF.DomainPCF.Nat.NbhSys.Definition
open import PCF.DomainPCF.Nat.NbhSys.Relation

natToNbh : AgdaNat → NatNbh
natToNbh 0 = 0ₙ
natToNbh (suc m) = sₙ (natToNbh m)

data _num↦_ : Valuation Γ → NatNbh → Set where
  num↦-intro : {𝑥 : Valuation Γ} → ∀ {y} →
               y ⊑ₙ natToNbh n → 𝑥 num↦ y
