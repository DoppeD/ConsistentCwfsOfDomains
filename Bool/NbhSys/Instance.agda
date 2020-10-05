module Bool.NbhSys.Instance where

open import Bool.NbhSys.AxiomProofs
open import Bool.NbhSys.Definition
open import Bool.NbhSys.Relation
open import NbhSys.Definition

BoolNbhSys : NbhSys
NbhSys.Nbh BoolNbhSys     = BoolNbh
NbhSys._⊑_ BoolNbhSys     = _⊑b_
NbhSys.Con BoolNbhSys     = Conb
NbhSys._⊔_[_] BoolNbhSys  = _⊔b_[_]
NbhSys.⊥ BoolNbhSys       = ⊥b
NbhSys.Con-⊔ BoolNbhSys   = Conb-⊔
NbhSys.⊑-refl BoolNbhSys  = ⊑b-refl
NbhSys.⊑-trans BoolNbhSys = ⊑b-trans
NbhSys.⊑-⊥ BoolNbhSys     = ⊑b-intro₁
NbhSys.⊑-⊔ BoolNbhSys     = ⊑b-⊔
NbhSys.⊑-⊔-fst BoolNbhSys = ⊑b-⊔-fst
NbhSys.⊑-⊔-snd BoolNbhSys = ⊑b-⊔-snd
