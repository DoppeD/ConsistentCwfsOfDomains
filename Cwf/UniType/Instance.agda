module Cwf.UniType.Instance where

open import Base.Core
open import Cwf.UniType.AxiomProofs
open import Cwf.UniType.ConLub
open import Cwf.UniType.Consistency
open import Cwf.UniType.Definition
open import Cwf.UniType.Relation
open import Cwf.UniType.Transitivity
open import NbhSys.Definition

data ConNbh : Set where
  conNbh : (u : Nbh) → con u → ConNbh

unwrapNbh : ConNbh → Nbh
unwrapNbh (conNbh u _) = u

UniType : NbhSys
NbhSys.Nbh UniType = ConNbh
NbhSys._⊑_ UniType u v = unwrapNbh u ⊑ unwrapNbh v
NbhSys.Con UniType u v = con (unwrapNbh u ⊔ unwrapNbh v)
NbhSys._⊔_[_] UniType u v conuv = conNbh (unwrapNbh u ⊔ unwrapNbh v) conuv
NbhSys.⊥ UniType = conNbh ⊥ *
NbhSys.Con-⊔ UniType = Con-⊔
NbhSys.⊑-refl UniType {conNbh _ conu} = ⊑-refl conu
NbhSys.⊑-trans UniType = ⊑-trans
NbhSys.⊑-⊥ UniType {conNbh _ conu} = ⊑-⊥ conu
NbhSys.⊑-⊔ UniType = ⊑-⊔
NbhSys.⊑-⊔-fst UniType = ⊑-⊔-fst
NbhSys.⊑-⊔-snd UniType = ⊑-⊔-snd
