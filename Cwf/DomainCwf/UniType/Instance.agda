module Cwf.DomainCwf.UniType.Instance where

open import Base.Core
open import Base.FinFun
open import Cwf.DomainCwf.UniType.AxiomProofs
--open import Cwf.DomainCwf.UniType.ConLub
open import Cwf.DomainCwf.UniType.Consistency
open import Cwf.DomainCwf.UniType.Definition
open import Cwf.DomainCwf.UniType.Relation
--open import Cwf.DomainCwf.UniType.Transitivity
open import NbhSys.Definition

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

-- We now define our neighborhood system as those Nbh that are consistent.
data ConNbh : Set where
  conNbh : ∀ u → con u → ConNbh

UniType : NbhSys
NbhSys.Nbh UniType = ConNbh
NbhSys._⊑_ UniType (conNbh u _) (conNbh v _) = u ⊑ v
NbhSys.Con UniType (conNbh u _) (conNbh v _) = con (u ⊔ v)
NbhSys._⊔_[_] UniType (conNbh u _) (conNbh v _) conuv = conNbh (u ⊔ v) conuv
NbhSys.⊥ UniType = conNbh ⊥ *
NbhSys.Con-⊔ UniType = {!!}
NbhSys.⊑-refl UniType {conNbh _ conu} = ⊑-refl conu
NbhSys.⊑-trans UniType {conNbh u _} {conNbh v _} {conNbh w _} u⊑v v⊑w
  = {!!}
NbhSys.⊑-⊥ UniType {conNbh _ conu} = ⊑-⊥ conu
NbhSys.⊑-⊔ UniType {conNbh u _} {conNbh v _} {conNbh w _} = ⊑-⊔
NbhSys.⊑-⊔-fst UniType {conNbh u _} {conNbh v _} = ⊑-⊔-fst
NbhSys.⊑-⊔-snd UniType {conNbh u _} {conNbh v _} = ⊑-⊔-snd
