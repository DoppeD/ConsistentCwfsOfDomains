{-# OPTIONS --safe #-}

module PCF.DomainPCF.PCFInstance where

open import PCF.DomainPCF.Bool.false.Instance
open import PCF.DomainPCF.Functions.iszero.Instance
open import PCF.DomainPCF.Bool.NbhSys.Instance
open import PCF.DomainPCF.Bool.true.Instance
open import PCF.DomainPCF.Nat.NbhSys.Instance
open import PCF.DomainPCF.Nat.zero.Instance
open import PCF.DomainPCF.Functions.fix.Instance
open import PCF.DomainPCF.Functions.fixeq
open import PCF.DomainPCF.Functions.pred.Instance
open import PCF.DomainPCF.Functions.predeq
open import PCF.DomainPCF.Functions.suc.Instance
open import PCF.PCF
open import Scwf.DomainScwf.ProdArrInstance

domPCF : PCF
PCF.productArrow-scwf domPCF = domProductArrowScwf
PCF.Nat domPCF = Nat
PCF.Bool domPCF = Bool
PCF.zero domPCF = zero
PCF.true domPCF = true
PCF.false domPCF = false
PCF.suc domPCF = suc
PCF.pred domPCF = pred
PCF.iszero domPCF = iszero
PCF.fix domPCF = fix
PCF.predeq domPCF = predeq
PCF.iszeroeq₁ domPCF = {!!}
PCF.iszeroeq₂ domPCF = {!!}
PCF.fixeq domPCF {𝐴 = 𝐴} = fixeq 𝐴
