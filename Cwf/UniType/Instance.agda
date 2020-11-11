module Cwf.UniType.Instance where

open import Cwf.UniType.Consistency
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
NbhSys.⊑-refl UniType = {!!}
NbhSys.⊑-trans UniType = {!!}
NbhSys.⊑-⊥ UniType = {!!}
NbhSys.⊑-⊔ UniType = {!!}
NbhSys.⊑-⊔-fst UniType = {!!}
NbhSys.⊑-⊔-snd UniType = {!!}
