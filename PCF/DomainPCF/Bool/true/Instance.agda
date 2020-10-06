{-# OPTIONS --safe #-}

module PCF.DomainPCF.Bool.true.Instance where

open import Appmap.PrincipalIdeal.Instance
open import Base.Variables
open import PCF.DomainPCF.Bool.NbhSys.Definition
open import PCF.DomainPCF.Bool.NbhSys.Instance
open import Scwf.DomainScwf.Appmap.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Instance

true : Term Γ Bool
true = principalIdeal (ValNbhSys _) Bool t
