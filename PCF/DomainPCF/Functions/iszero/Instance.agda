{-# OPTIONS --safe #-}

module PCF.DomainPCF.Functions.iszero.Instance where

open import Appmap.Definition
open import Base.Variables
open import PCF.DomainPCF.Functions.iszero.AxiomProofs
open import PCF.DomainPCF.Functions.iszero.Relation
open import PCF.DomainPCF.Bool.NbhSys.Instance
open import PCF.DomainPCF.Nat.NbhSys.Instance
open import Scwf.DomainScwf.Appmap.Definition
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Instance

iszero : Term Γ (Nat ⇒ Bool)
Appmap._↦_ iszero         = _iszero↦_
Appmap.↦-mono iszero      = iszero↦-mono
Appmap.↦-bottom iszero    = iszero↦-bottom
Appmap.↦-↓closed iszero   = iszero↦-↓closed
Appmap.↦-↑directed iszero = iszero↦-↑directed
Appmap.↦-con iszero       = iszero↦-con
