{-# OPTIONS --safe #-}

module Scwf.DomainScwf.ProductStructure.Pair.Instance where

open import Base.Core
open import Base.Variables
open import Scwf.DomainScwf.Appmap.Definition
open import Scwf.DomainScwf.ProductStructure.NbhSys.Instance
open import Scwf.DomainScwf.ProductStructure.Pair.AxiomProofs
open import Scwf.DomainScwf.ProductStructure.Pair.Relation

<_,_> : Term Γ 𝐴 → Term Γ 𝐵 → Term Γ (𝐴 × 𝐵)
Appmap._↦_ < 𝑡 , 𝑢 >         = <>↦ 𝑡 𝑢
Appmap.↦-mono < 𝑡 , 𝑢 >      = <>↦-mono 𝑡 𝑢
Appmap.↦-bottom < 𝑡 , 𝑢 >    = <>↦-bottom 𝑡 𝑢
Appmap.↦-↓closed < 𝑡 , 𝑢 >   = <>↦-↓closed 𝑡 𝑢
Appmap.↦-↑directed < 𝑡 , 𝑢 > = <>↦-↑directed 𝑡 𝑢
Appmap.↦-con < 𝑡 , 𝑢 >       = <>↦-con 𝑡 𝑢
