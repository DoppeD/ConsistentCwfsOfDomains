{-# OPTIONS --safe #-}

module PCF.DomainPCF.Functions.fix.Instance where

open import Appmap.Definition
open import Base.Variables
open import PCF.DomainPCF.Functions.fix.AxiomProofs
open import PCF.DomainPCF.Functions.fix.Relation
open import Scwf.DomainScwf.Appmap.Definition
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Instance

fix : Term Γ ((𝐴 ⇒ 𝐴) ⇒ 𝐴)
Appmap._↦_ (fix {𝐴 = 𝐴})         = _fix↦_ 𝐴
Appmap.↦-mono (fix {𝐴 = 𝐴})      = fix↦-mono
Appmap.↦-bottom (fix {𝐴 = 𝐴})    = fix↦-bottom
Appmap.↦-↓closed (fix {𝐴 = 𝐴})   = fix↦-↓closed
Appmap.↦-↑directed (fix {𝐴 = 𝐴}) = fix↦-↑directed
Appmap.↦-con (fix {𝐴 = 𝐴})       = fix↦-con
