module PCF.DomainPCF.Nat.zero.Instance where

open import Appmap.Definition
open import Base.Variables
open import PCF.DomainPCF.Nat.NbhSys.Instance
open import PCF.DomainPCF.Nat.zero.AxiomProofs
open import PCF.DomainPCF.Nat.zero.Relation
open import Scwf.DomainScwf.Appmap.Definition
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Instance

zero : Term Γ (Nat ⇒ Nat)
Appmap._↦_ zero = _zero↦_
Appmap.↦-mono zero = zero↦-mono
Appmap.↦-bottom zero = zero↦-bottom
Appmap.↦-↓closed zero = zero↦-↓closed
Appmap.↦-↑directed zero = zero↦-↑directed
Appmap.↦-con zero = zero↦-con
