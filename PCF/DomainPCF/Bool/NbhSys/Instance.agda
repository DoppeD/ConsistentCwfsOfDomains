module PCF.DomainPCF.Bool.NbhSys.Instance where

open import PCF.DomainPCF.Bool.NbhSys.AxiomProofs
open import PCF.DomainPCF.Bool.NbhSys.Definition
open import PCF.DomainPCF.Bool.NbhSys.Relation
open import NbhSys.Definition

Bool : NbhSys
NbhSys.Nbh Bool     = BoolNbh
NbhSys._⊑_ Bool     = _⊑b_
NbhSys.Con Bool     = Conb
NbhSys._⊔_[_] Bool  = _⊔b_[_]
NbhSys.⊥ Bool       = ⊥b
NbhSys.Con-⊔ Bool   = Conb-⊔
NbhSys.⊑-refl Bool  = ⊑b-refl
NbhSys.⊑-trans Bool = ⊑b-trans
NbhSys.⊑-⊥ Bool     = ⊑b-intro₁
NbhSys.⊑-⊔ Bool     = ⊑b-⊔
NbhSys.⊑-⊔-fst Bool = ⊑b-⊔-fst
NbhSys.⊑-⊔-snd Bool = ⊑b-⊔-snd
