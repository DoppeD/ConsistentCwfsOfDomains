{-# OPTIONS --safe #-}

module Scwf.DomainScwf.ProdArrInstance where

open import Scwf.DomainScwf.ArrowStructure.ap.Instance
open import Scwf.DomainScwf.ArrowStructure.apCong
open import Scwf.DomainScwf.ArrowStructure.apSub
open import Scwf.DomainScwf.ArrowStructure.beta
open import Scwf.DomainScwf.ArrowStructure.lam.Instance
open import Scwf.DomainScwf.ArrowStructure.lamCong
open import Scwf.DomainScwf.ArrowStructure.lamSub
open import Scwf.DomainScwf.ArrowStructure.NbhSys.DefProof
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Instance
open import Scwf.DomainScwf.ProdInstance
open import Scwf.ProductArrow

domProductArrowScwf : ProductArrow-scwf
ProductArrow-scwf.prod-scwf domProductArrowScwf
  = domProdScwf
ProductArrow-scwf._⇒_ domProductArrowScwf
  = ArrNbhSys
ProductArrow-scwf.lam domProductArrowScwf
  = lam
ProductArrow-scwf.ap domProductArrowScwf
  = ap
ProductArrow-scwf.lamSub domProductArrowScwf {𝐴 = 𝐴} {𝐵}
  = lamSub 𝐴 𝐵
ProductArrow-scwf.apSub domProductArrowScwf {𝐴 = 𝐴} {𝐵}
  = apSub 𝐴 𝐵
ProductArrow-scwf.β domProductArrowScwf {𝐴 = 𝐴} {𝐵}
  = β-equal 𝐴 𝐵
ProductArrow-scwf.lamCong domProductArrowScwf {𝐴 = 𝐴} {𝐵}
  = lamCong 𝐴 𝐵
ProductArrow-scwf.apCong domProductArrowScwf {𝐴 = 𝐴} {𝐵}
  = apCong 𝐴 𝐵
