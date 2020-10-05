module PCF.DomainPCF.Nat.suc.Instance where

open import Appmap.Definition
open import PCF.DomainPCF.Nat.NbhSys.Instance
open import PCF.DomainPCF.Nat.suc.AxiomProofs
open import PCF.DomainPCF.Nat.suc.Relation

suc : Appmap NatNbhSys NatNbhSys
Appmap._↦_ suc         = _suc↦_
Appmap.↦-mono suc      = suc↦-mono
Appmap.↦-bottom suc    = suc↦-bottom
Appmap.↦-↓closed suc   = suc↦-↓closed
Appmap.↦-↑directed suc = suc↦-↑directed
Appmap.↦-con suc       = suc↦-con
