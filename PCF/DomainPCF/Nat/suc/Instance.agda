{-# OPTIONS --safe #-}

module PCF.DomainPCF.Nat.suc.Instance where

open import Appmap.Definition
open import Base.Variables
open import PCF.DomainPCF.Nat.NbhSys.Instance
open import PCF.DomainPCF.Nat.suc.AxiomProofs
open import PCF.DomainPCF.Nat.suc.Relation
open import Scwf.DomainScwf.Appmap.Definition
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Instance

suc : Term Γ (Nat ⇒ Nat)
Appmap._↦_ suc         = _suc↦_
Appmap.↦-mono suc      = suc↦-mono
Appmap.↦-bottom suc    = suc↦-bottom
Appmap.↦-↓closed suc   = suc↦-↓closed
Appmap.↦-↑directed suc = suc↦-↑directed
Appmap.↦-con suc       = suc↦-con
