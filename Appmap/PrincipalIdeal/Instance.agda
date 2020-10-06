{-# OPTIONS --safe #-}

open import Base.Core
open import NbhSys.Definition

module Appmap.PrincipalIdeal.Instance
  (𝐴 𝐵 : Ty) (gen : NbhSys.Nbh 𝐵) where

open import Appmap.PrincipalIdeal.AxiomProofs 𝐴 𝐵 gen
open import Appmap.PrincipalIdeal.Relation 𝐴 𝐵 gen
open import Scwf.DomainScwf.Appmap.Definition

principalIdeal : Appmap 𝐴 𝐵
Appmap._↦_ principalIdeal         = _ideal↦_
Appmap.↦-mono principalIdeal      = ideal↦-mono
Appmap.↦-bottom principalIdeal    = ideal↦-bottom
Appmap.↦-↓closed principalIdeal   = ideal↦-↓closed
Appmap.↦-↑directed principalIdeal = ideal↦-↑directed
Appmap.↦-con principalIdeal       = ideal↦-con
