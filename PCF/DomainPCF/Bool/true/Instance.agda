module PCF.DomainPCF.Bool.true.Instance where

open import Base.Variables
open import PCF.DomainPCF.Bool.NbhSys.Instance
open import PCF.DomainPCF.Bool.true.AxiomProofs
open import PCF.DomainPCF.Bool.true.Relation
open import Scwf.DomainScwf.Appmap.Definition

true : Term Γ Bool
Appmap._↦_ true         = _true↦_
Appmap.↦-mono true      = true↦-mono
Appmap.↦-bottom true    = true↦-bottom
Appmap.↦-↓closed true   = true↦-↓closed
Appmap.↦-↑directed true = true↦-↑directed
Appmap.↦-con true       = true↦-con
