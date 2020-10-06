{-# OPTIONS --safe #-}

module PCF.DomainPCF.Bool.false.Instance where

open import Appmap.PrincipalIdeal.Instance
open import Base.Variables
open import PCF.DomainPCF.Bool.NbhSys.Definition
open import PCF.DomainPCF.Bool.NbhSys.Instance
open import Scwf.DomainScwf.Appmap.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Instance

false : Term Γ Bool
false = principalIdeal (ValNbhSys _) Bool f
