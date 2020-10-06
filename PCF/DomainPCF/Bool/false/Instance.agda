module PCF.DomainPCF.Bool.false.Instance where

open import Base.Variables
open import PCF.DomainPCF.Bool.NbhSys.Instance
open import PCF.DomainPCF.Bool.false.AxiomProofs
open import PCF.DomainPCF.Bool.false.Relation
open import Scwf.DomainScwf.Appmap.Definition

false : Term Γ Bool
Appmap._↦_ false         = _false↦_
Appmap.↦-mono false      = false↦-mono
Appmap.↦-bottom false    = false↦-bottom
Appmap.↦-↓closed false   = false↦-↓closed
Appmap.↦-↑directed false = false↦-↑directed
Appmap.↦-con false       = false↦-con
