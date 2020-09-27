{-# OPTIONS --safe #-}

open import Base.Core

module Scwf.DomainScwf.ArrowStructure.NbhSys.ConFinFun
  (𝐴 𝐵 : Ty) where

open import Base.FinFun
open import NbhSys.Definition
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Post 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Pre 𝐴 𝐵

-- A finite function 𝑓 is consistent if...
data ConFinFun (𝑓 : FinFun (NbhSys.Nbh 𝐴) (NbhSys.Nbh 𝐵)) : Set where
  cff : (∀ {𝑓′} → 𝑓′ ⊆ 𝑓 → Preable 𝑓′ → Postable 𝑓′) →
        ConFinFun 𝑓

subsetIsCon : ∀ {𝑓 𝑓′} → ConFinFun 𝑓′ → 𝑓 ⊆ 𝑓′ → ConFinFun 𝑓
subsetIsCon (cff p) 𝑓⊆𝑓′
  = cff (λ 𝑓″⊆𝑓 preable𝑓″ → p (⊆-trans 𝑓″⊆𝑓 𝑓⊆𝑓′) preable𝑓″)
