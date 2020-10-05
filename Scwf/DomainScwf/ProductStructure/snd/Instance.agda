{-# OPTIONS --safe #-}

module Scwf.DomainScwf.ProductStructure.snd.Instance where

open import Base.Core
open import Base.Variables
open import Scwf.DomainScwf.Appmap.Definition
open import Scwf.DomainScwf.ProductStructure.NbhSys.Instance
open import Scwf.DomainScwf.ProductStructure.snd.AxiomProofs
open import Scwf.DomainScwf.ProductStructure.snd.Relation

snd : Term Γ (𝐴 × 𝐵) → Term Γ 𝐵
Appmap._↦_ (snd 𝑡)         = snd↦ 𝑡
Appmap.↦-mono (snd 𝑡)      = snd↦-mono 𝑡
Appmap.↦-bottom (snd 𝑡)    = snd↦-bottom 𝑡
Appmap.↦-↓closed (snd 𝑡)   = snd↦-↓closed 𝑡
Appmap.↦-↑directed (snd 𝑡) = snd↦-↑directed 𝑡
Appmap.↦-con (snd 𝑡)       = snd↦-con 𝑡
