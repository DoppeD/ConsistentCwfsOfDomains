{-# OPTIONS --safe #-}

module Scwf.DomainScwf.ArrowStructure.lam.Instance where

open import Base.Core
open import Base.Variables
open import Scwf.DomainScwf.Appmap.Definition
open import Scwf.DomainScwf.ArrowStructure.lam.AxiomProofs
open import Scwf.DomainScwf.ArrowStructure.lam.Consistency
open import Scwf.DomainScwf.ArrowStructure.lam.Relation
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Instance

lam : Term (𝐴 :: Γ) 𝐵 → Term Γ (𝐴 ⇒ 𝐵)
Appmap._↦_ (lam {𝐴} {𝐵 = 𝐵} 𝑡) = [_]_lam↦_ 𝐴 𝐵 𝑡
Appmap.↦-mono (lam  𝑡)         = lam↦-mono 𝑡
Appmap.↦-bottom (lam 𝑡)        = lam↦-bottom 𝑡
Appmap.↦-↓closed (lam 𝑡)       = lam↦-↓closed 𝑡
Appmap.↦-↑directed (lam 𝑡)     = lam↦-↑directed 𝑡
Appmap.↦-con (lam 𝑡)           = lam↦-con 𝑡
