{-# OPTIONS --safe #-}

module Scwf.DomainScwf.ProductStructure.fst.Instance where

open import Base.Core
open import Base.Variables
open import Scwf.DomainScwf.Appmap.Definition
open import Scwf.DomainScwf.ProductStructure.fst.AxiomProofs
open import Scwf.DomainScwf.ProductStructure.fst.Relation
open import Scwf.DomainScwf.ProductStructure.NbhSys.Instance

fst : tAppmap Γ [ 𝐴 × 𝐵 ] → tAppmap Γ [ 𝐴 ]
Appmap._↦_ (fst 𝑡)         = fst↦ 𝑡
Appmap.↦-mono (fst 𝑡)      = fst↦-mono 𝑡
Appmap.↦-bottom (fst 𝑡)    = fst↦-bottom 𝑡
Appmap.↦-↓closed (fst 𝑡)   = fst↦-↓closed 𝑡
Appmap.↦-↑directed (fst 𝑡) = fst↦-↑directed 𝑡
