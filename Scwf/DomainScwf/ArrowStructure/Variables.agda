{-# OPTIONS --safe #-}

open import Base.Core

module Scwf.DomainScwf.ArrowStructure.Variables (𝐴 𝐵 : Ty) where

open import Base.FinFun

variable
  𝑓 𝑓′ 𝑓″ 𝑓‴ : NbhFinFun 𝐴 𝐵
