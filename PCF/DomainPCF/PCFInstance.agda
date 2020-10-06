module PCF.DomainPCF.PCFInstance where

open import PCF.DomainPCF.Bool.false.Instance
open import PCF.DomainPCF.Bool.NbhSys.Instance
open import PCF.DomainPCF.Bool.true.Instance
open import PCF.DomainPCF.Nat.NbhSys.Instance
open import PCF.DomainPCF.Nat.num.Instance
open import PCF.PCF
open import Scwf.DomainScwf.ProdArrInstance

domPCF : PCF
PCF.productArrow-scwf domPCF = domProductArrowScwf
PCF.Nat domPCF = Nat
PCF.Bool domPCF = Bool
PCF.num domPCF = num
PCF.true domPCF = true
PCF.false domPCF = false
PCF.suc domPCF = {!!}
PCF.pred domPCF = {!!}
PCF.zero domPCF = {!!}
PCF.iszero domPCF = {!!}
PCF.fix domPCF = {!!}
PCF.suceq domPCF = {!!}
PCF.predeq domPCF = {!!}
PCF.zeroeq domPCF = {!!}
PCF.iszeroeq₁ domPCF = {!!}
PCF.iszeroeq₂ domPCF = {!!}
PCF.fixeq domPCF = {!!}
