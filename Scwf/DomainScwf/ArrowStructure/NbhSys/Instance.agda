{-# OPTIONS --safe #-}

module Scwf.DomainScwf.ArrowStructure.NbhSys.Instance where

open import Base.Core
open import Base.FinFun
open import NbhSys.Definition
open import Scwf.DomainScwf.ArrowStructure.NbhSys.AxiomProofs
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Definition
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Relation
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Transitivity

ArrNbhSys : (𝐴 𝐵 : Ty) → NbhSys
NbhSys.Nbh (ArrNbhSys 𝐴 𝐵)     = ArrNbh 𝐴 𝐵
NbhSys._⊑_ (ArrNbhSys 𝐴 𝐵)     = _⊑ₑ_ 𝐴 𝐵
NbhSys._⊔_ (ArrNbhSys 𝐴 𝐵)     = _⊔ₑ_ 𝐴 𝐵
NbhSys.⊥ (ArrNbhSys 𝐴 𝐵)       = ⊥ₑ
NbhSys.⊑-refl (ArrNbhSys 𝐴 𝐵)  = ⊑ₑ-refl 𝐴 𝐵
NbhSys.⊑-trans (ArrNbhSys 𝐴 𝐵) = ⊑ₑ-trans 𝐴 𝐵
NbhSys.⊑-⊥ (ArrNbhSys 𝐴 𝐵)     = ⊑ₑ-⊥ₑ 𝐴 𝐵
NbhSys.⊑-⊔ (ArrNbhSys 𝐴 𝐵)     = ⊑ₑ-⊔ₑ 𝐴 𝐵
NbhSys.⊑-⊔-fst (ArrNbhSys 𝐴 𝐵) = ⊑ₑ-⊔ₑ-fst 𝐴 𝐵
NbhSys.⊑-⊔-snd (ArrNbhSys 𝐴 𝐵) = ⊑ₑ-⊔ₑ-snd 𝐴 𝐵
