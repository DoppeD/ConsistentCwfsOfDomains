{-# OPTIONS --safe #-}

module PCF.DomainPCF.PCFInstance where

open import PCF.DomainPCF.Bool.false.Instance
open import PCF.DomainPCF.Functions.iszero.Instance
open import PCF.DomainPCF.Functions.iszeroeq1
open import PCF.DomainPCF.Functions.iszeroeq2
open import PCF.DomainPCF.Bool.NbhSys.Instance
open import PCF.DomainPCF.Bool.true.Instance
open import PCF.DomainPCF.Nat.NbhSys.Instance
open import PCF.DomainPCF.Nat.num.Instance
open import PCF.DomainPCF.Functions.fix.Instance
open import PCF.DomainPCF.Functions.pred.Instance
open import PCF.DomainPCF.Functions.predeq
open import PCF.DomainPCF.Functions.suc.Instance
open import PCF.DomainPCF.Functions.suceq
open import PCF.DomainPCF.Functions.zero.Instance
open import PCF.DomainPCF.Functions.zeroeq
open import PCF.PCF
open import Scwf.DomainScwf.ProdArrInstance

domPCF : PCF
PCF.productArrow-scwf domPCF = domProductArrowScwf
PCF.Nat domPCF = Nat
PCF.Bool domPCF = Bool
PCF.num domPCF = num
PCF.true domPCF = true
PCF.false domPCF = false
PCF.suc domPCF = suc
PCF.pred domPCF = pred
PCF.zero domPCF = zero
PCF.iszero domPCF = iszero
PCF.fix domPCF = fix
PCF.suceq domPCF = suceq
PCF.predeq domPCF = predeq
PCF.zeroeq domPCF = zeroeq
PCF.iszeroeq₁ domPCF = iszeroeq₁
PCF.iszeroeq₂ domPCF = iszeroeq₂
PCF.fixeq domPCF = {!!}
