module Cwf.UniType.Instance where

open import Cwf.UniType.AxiomProofs
open import Cwf.UniType.Definition
open import Cwf.UniType.Relation
open import NbhSys.Definition

UniType : NbhSys
NbhSys.Nbh UniType = Nbh
NbhSys._⊑_ UniType = _⊑ᵤ_
NbhSys.Con UniType = Con
NbhSys._⊔_[_] UniType = _⊔ᵤ_[_]
NbhSys.⊥ UniType = ⊥
NbhSys.Con-⊔ UniType = {!!}
NbhSys.⊑-refl UniType = ⊑ᵤ-refl
NbhSys.⊑-trans UniType = {!!}
NbhSys.⊑-⊥ UniType = ⊑ᵤ-⊥
NbhSys.⊑-⊔ UniType = ⊑ᵤ-⊔
NbhSys.⊑-⊔-fst UniType = ⊑ᵤ-⊔-fst
NbhSys.⊑-⊔-snd UniType = ⊑ᵤ-⊔-snd
