{-# OPTIONS --safe #-}

module Scwf.DomainScwf.ProdInstance where

open import Scwf.DomainScwf.PlainInstance
open import Scwf.DomainScwf.ProductStructure.AxiomProofs
open import Scwf.DomainScwf.ProductStructure.fst.Instance
open import Scwf.DomainScwf.ProductStructure.NbhSys.Instance
open import Scwf.DomainScwf.ProductStructure.Pair.Instance
open import Scwf.DomainScwf.ProductStructure.snd.Instance
open import Scwf.DomainScwf.ProductStructure.Unit.Mapping.Instance
open import Scwf.DomainScwf.ProductStructure.Unit.NbhSys.Instance
open import Scwf.DomainScwf.ProductStructure.Unit.NSub
open import Scwf.Product

domProdScwf : Prod-scwf
Prod-scwf.scwf domProdScwf                 = domScwf
Prod-scwf._×_ domProdScwf                  = _×_
Prod-scwf.fst domProdScwf                  = fst
Prod-scwf.snd domProdScwf                  = snd
Prod-scwf.<_,_> domProdScwf                = <_,_>
Prod-scwf.fstAxiom domProdScwf {𝐴 = 𝐴} {𝐵} = fstAxiom 𝐴 𝐵
Prod-scwf.sndAxiom domProdScwf {𝐴 = 𝐴} {𝐵} = sndAxiom  𝐴 𝐵
Prod-scwf.pairSub domProdScwf {𝐴 = 𝐴} {𝐵}  = pairSub 𝐴 𝐵
Prod-scwf.fstCong domProdScwf {𝐴 = 𝐴} {𝐵}  = fstCong 𝐴 𝐵
Prod-scwf.sndCong domProdScwf {𝐴 = 𝐴} {𝐵}  = sndCong 𝐴 𝐵
Prod-scwf.pairCong domProdScwf {𝐴 = 𝐴} {𝐵} = pairCong 𝐴 𝐵
Prod-scwf.ℕ₁ domProdScwf                   = ℕ₁
Prod-scwf.0₁ domProdScwf                   = 0₁
Prod-scwf.ℕ₁-sub domProdScwf               = ℕ₁-sub
