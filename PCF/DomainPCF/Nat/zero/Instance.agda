{-# OPTIONS --safe #-}

module PCF.DomainPCF.Nat.zero.Instance where

open import Appmap.PrincipalIdeal.Instance
open import Base.Variables
open import PCF.DomainPCF.Nat.NbhSys.Definition
open import PCF.DomainPCF.Nat.NbhSys.Instance
open import Scwf.DomainScwf.Appmap.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Instance

zero : Term Γ Nat
zero = principalIdeal (ValNbhSys _) Nat 0ₙ
