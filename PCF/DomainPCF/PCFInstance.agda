{-# OPTIONS --safe #-}

module PCF.DomainPCF.PCFInstance where

open import PCF.DomainPCF.Bool.false.Instance
open import PCF.DomainPCF.Bool.iszero.Instance
open import PCF.DomainPCF.Bool.iszeroeq1
open import PCF.DomainPCF.Bool.iszeroeq2
open import PCF.DomainPCF.Bool.NbhSys.Instance
open import PCF.DomainPCF.Bool.true.Instance
open import PCF.DomainPCF.Nat.NbhSys.Instance
open import PCF.DomainPCF.Nat.num.Instance
open import PCF.DomainPCF.Nat.pred.Instance
open import PCF.DomainPCF.Nat.suc.Instance
open import PCF.DomainPCF.Nat.suceq
open import PCF.DomainPCF.Nat.zero.Instance
open import PCF.DomainPCF.Nat.zeroeq
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
PCF.fix domPCF = {!!}
PCF.suceq domPCF = suceq
PCF.predeq domPCF = {!!}
PCF.zeroeq domPCF = zeroeq
PCF.iszeroeq₁ domPCF = iszeroeq₁
PCF.iszeroeq₂ domPCF = iszeroeq₂
PCF.fixeq domPCF = {!!}
