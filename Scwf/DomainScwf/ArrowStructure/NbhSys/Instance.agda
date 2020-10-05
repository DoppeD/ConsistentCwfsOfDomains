{-# OPTIONS --safe #-}

module Scwf.DomainScwf.ArrowStructure.NbhSys.Instance where

open import Base.Core
open import Base.FinFun
open import NbhSys.Definition
open import Scwf.DomainScwf.ArrowStructure.NbhSys.AxiomProofs
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Consistency
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Definition
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Relation
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Transitivity

_⇒_ : (𝐴 𝐵 : Ty) → NbhSys
NbhSys.Nbh (𝐴 ⇒ 𝐵)     = ArrNbh 𝐴 𝐵
NbhSys._⊑_ (𝐴 ⇒ 𝐵)     = _⊑ₑ_ 𝐴 𝐵
NbhSys.Con (𝐴 ⇒ 𝐵)     = ArrCon 𝐴 𝐵
NbhSys._⊔_[_] (𝐴 ⇒ 𝐵)  = _⊔ₑ_[_] 𝐴 𝐵
NbhSys.⊥ (𝐴 ⇒ 𝐵)       = ⊥ₑ
NbhSys.Con-⊔ (𝐴 ⇒ 𝐵)   = Con-⊔ₑ 𝐴 𝐵
NbhSys.⊑-refl (𝐴 ⇒ 𝐵)  = ⊑ₑ-refl 𝐴 𝐵
NbhSys.⊑-trans (𝐴 ⇒ 𝐵) = ⊑ₑ-trans 𝐴 𝐵
NbhSys.⊑-⊥ (𝐴 ⇒ 𝐵)     = ⊑ₑ-⊥ₑ 𝐴 𝐵
NbhSys.⊑-⊔ (𝐴 ⇒ 𝐵)     = ⊑ₑ-⊔ₑ 𝐴 𝐵
NbhSys.⊑-⊔-fst (𝐴 ⇒ 𝐵) = ⊑ₑ-⊔ₑ-fst 𝐴 𝐵
NbhSys.⊑-⊔-snd (𝐴 ⇒ 𝐵) = ⊑ₑ-⊔ₑ-snd 𝐴 𝐵
