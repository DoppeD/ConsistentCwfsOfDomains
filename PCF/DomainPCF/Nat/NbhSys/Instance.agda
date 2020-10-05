module PCF.DomainPCF.Nat.NbhSys.Instance where

open import PCF.DomainPCF.Nat.NbhSys.AxiomProofs
open import PCF.DomainPCF.Nat.NbhSys.Definition
open import PCF.DomainPCF.Nat.NbhSys.Relation
open import NbhSys.Definition

NatNbhSys : NbhSys
NbhSys.Nbh NatNbhSys     = NatNbh
NbhSys._⊑_ NatNbhSys     = _⊑ₙ_
NbhSys.Con NatNbhSys     = Conₙ
NbhSys._⊔_[_] NatNbhSys  = _⊔ₙ_[_]
NbhSys.⊥ NatNbhSys       = ⊥ₙ
NbhSys.Con-⊔ NatNbhSys   = Conₙ-⊔
NbhSys.⊑-refl NatNbhSys  = ⊑ₙ-refl
NbhSys.⊑-trans NatNbhSys = ⊑ₙ-trans
NbhSys.⊑-⊥ NatNbhSys     = ⊑ₙ-intro₁
NbhSys.⊑-⊔ NatNbhSys     = ⊑ₙ-⊔
NbhSys.⊑-⊔-fst NatNbhSys = ⊑ₙ-⊔-fst
NbhSys.⊑-⊔-snd NatNbhSys = ⊑ₙ-⊔-snd
