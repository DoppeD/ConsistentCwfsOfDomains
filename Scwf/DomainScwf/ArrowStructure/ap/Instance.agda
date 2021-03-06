{-# OPTIONS --safe #-}

module Scwf.DomainScwf.ArrowStructure.ap.Instance where

open import Base.Core
open import Base.Variables
open import Scwf.DomainScwf.Appmap.Definition
open import Scwf.DomainScwf.ArrowStructure.ap.AxiomProofs
open import Scwf.DomainScwf.ArrowStructure.ap.Consistency
open import Scwf.DomainScwf.ArrowStructure.ap.Relation
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Instance

ap : Term Γ (𝐴 ⇒ 𝐵) → Term Γ 𝐴 → Term Γ 𝐵
Appmap._↦_ (ap {𝐴 = 𝐴} {𝐵} 𝑡 𝑢) = [_,_]_ap↦_ 𝐴 𝐵 𝑡 𝑢
Appmap.↦-mono (ap 𝑡 𝑢)          = ap↦-mono 𝑡 𝑢
Appmap.↦-bottom (ap 𝑡 𝑢)        = ap↦-bottom 𝑡 𝑢
Appmap.↦-↓closed (ap 𝑡 𝑢)       = ap↦-↓closed 𝑡 𝑢
Appmap.↦-↑directed (ap 𝑡 𝑢)     = ap↦-↑directed 𝑡 𝑢
Appmap.↦-con (ap 𝑡 𝑢)           = ap↦-con 𝑡 𝑢
