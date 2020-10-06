{-# OPTIONS --safe #-}

module PCF.DomainPCF.Nat.NbhSys.Instance where

open import PCF.DomainPCF.Nat.NbhSys.AxiomProofs
open import PCF.DomainPCF.Nat.NbhSys.Definition
open import PCF.DomainPCF.Nat.NbhSys.Relation
open import NbhSys.Definition

Nat : NbhSys
NbhSys.Nbh Nat     = NatNbh
NbhSys._⊑_ Nat     = _⊑ₙ_
NbhSys.Con Nat     = Conₙ
NbhSys._⊔_[_] Nat  = _⊔ₙ_[_]
NbhSys.⊥ Nat       = ⊥ₙ
NbhSys.Con-⊔ Nat   = Conₙ-⊔
NbhSys.⊑-refl Nat  = ⊑ₙ-refl
NbhSys.⊑-trans Nat = ⊑ₙ-trans
NbhSys.⊑-⊥ Nat     = ⊑ₙ-intro₁
NbhSys.⊑-⊔ Nat     = ⊑ₙ-⊔
NbhSys.⊑-⊔-fst Nat = ⊑ₙ-⊔-fst
NbhSys.⊑-⊔-snd Nat = ⊑ₙ-⊔-snd
