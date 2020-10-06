module PCF.DomainPCF.Nat.num.Instance where

open import Base.Variables
open import PCF.DomainPCF.Nat.NbhSys.Instance
open import PCF.DomainPCF.Nat.num.AxiomProofs
open import PCF.DomainPCF.Nat.num.Relation
open import Scwf.DomainScwf.Appmap.Definition

open import Agda.Builtin.Nat renaming (Nat to AgdaNat)

num : AgdaNat → Term Γ Nat
Appmap._↦_ (num n)         = _num↦_ n
Appmap.↦-mono (num n)      = num↦-mono n
Appmap.↦-bottom (num n)    = num↦-bottom n
Appmap.↦-↓closed (num n)   = num↦-↓closed n
Appmap.↦-↑directed (num n) = num↦-↑directed n
Appmap.↦-con (num n)       = num↦-con n
