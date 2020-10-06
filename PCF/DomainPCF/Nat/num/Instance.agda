module PCF.DomainPCF.Nat.num.Instance where

open import Appmap.PrincipalIdeal.Instance
open import Base.Variables
open import PCF.DomainPCF.Nat.NbhSys.Definition
open import PCF.DomainPCF.Nat.NbhSys.Instance
open import Scwf.DomainScwf.Appmap.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Instance

open import Agda.Builtin.Nat renaming (Nat to AgdaNat)

-- Translates a natural number to the corresponding neighborhood.
natToNbh : AgdaNat → NatNbh
natToNbh 0 = 0ₙ
natToNbh (suc n) = sₙ (natToNbh n)

num : AgdaNat → Term Γ Nat
num n = principalIdeal (ValNbhSys _) Nat (natToNbh n)
