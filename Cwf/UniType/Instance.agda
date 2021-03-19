module Cwf.UniType.Instance where

open import Base.Core
open import Cwf.UniType.AxiomProofs
open import Cwf.UniType.ConLub
open import Cwf.UniType.Consistency
open import Cwf.UniType.Definition
open import Cwf.UniType.Relation
open import NbhSys.Definition

UniType : NbhSys
NbhSys.Nbh UniType = Nbh
NbhSys._⊑_ UniType = _⊑_
NbhSys.Con UniType = λ u v → con (u ⊔ v)
NbhSys._⊔_[_] UniType = λ u v _ → u ⊔ v
NbhSys.⊥ UniType = ⊥
NbhSys.Con-⊔ UniType = Con-⊔
NbhSys.⊑-refl UniType = {!!}
NbhSys.⊑-trans UniType = {!!}
NbhSys.⊑-⊥ UniType = {!!}
NbhSys.⊑-⊔ UniType = ⊑-⊔
NbhSys.⊑-⊔-fst UniType = ⊑-⊔-fst
NbhSys.⊑-⊔-snd UniType = ⊑-⊔-snd
