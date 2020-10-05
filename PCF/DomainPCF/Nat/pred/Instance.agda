module PCF.DomainPCF.Nat.pred.Instance where

open import Appmap.Definition
open import PCF.DomainPCF.Nat.NbhSys.Instance
open import PCF.DomainPCF.Nat.NbhSys.Relation
open import PCF.DomainPCF.Nat.pred.AxiomProofs
open import PCF.DomainPCF.Nat.pred.Relation

pred : Appmap NatNbhSys NatNbhSys
Appmap._↦_ pred         = _pred↦_
Appmap.↦-mono pred      = pred↦-mono
Appmap.↦-bottom pred    = pred↦-bottom
Appmap.↦-↓closed pred   = pred↦-↓closed
Appmap.↦-↑directed pred = pred↦-↑directed
Appmap.↦-con pred       = pred↦-con
