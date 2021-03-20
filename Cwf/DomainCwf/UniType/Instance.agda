{-# OPTIONS --safe --sized-types #-}

module Cwf.DomainCwf.UniType.Instance where

open import Base.Core
open import Cwf.DomainCwf.UniType.AxiomProofs
open import Cwf.DomainCwf.UniType.ConLub
open import Cwf.DomainCwf.UniType.Consistency
open import Cwf.DomainCwf.UniType.Definition
open import Cwf.DomainCwf.UniType.Relation
open import Cwf.DomainCwf.UniType.Transitivity
open import NbhSys.Definition

data ConNbh : Set where
  conNbh : (u : Nbh) → con u → ConNbh

UniType : NbhSys
NbhSys.Nbh UniType = ConNbh
NbhSys._⊑_ UniType (conNbh u _) (conNbh v _) = u ⊑ v
NbhSys.Con UniType (conNbh u _) (conNbh v _) = con (u ⊔ v)
NbhSys._⊔_[_] UniType (conNbh u _) (conNbh v _) conuv = conNbh (u ⊔ v) conuv
NbhSys.⊥ UniType = conNbh ⊥ *
NbhSys.Con-⊔ UniType {conNbh _ _} {conNbh _ _} {conNbh _ _} = Con-⊔
NbhSys.⊑-refl UniType {conNbh _ conu} = ⊑-refl conu
NbhSys.⊑-trans UniType {conNbh _ _} {conNbh _ _} {conNbh _ _} = ⊑-trans
NbhSys.⊑-⊥ UniType {conNbh _ conu} = ⊑-⊥ conu
NbhSys.⊑-⊔ UniType {conNbh _ _} {conNbh _ _} {conNbh _ _} = ⊑-⊔
NbhSys.⊑-⊔-fst UniType {conNbh _ _} {conNbh _ _} = ⊑-⊔-fst
NbhSys.⊑-⊔-snd UniType {conNbh _ _} {conNbh _ _} = ⊑-⊔-snd
