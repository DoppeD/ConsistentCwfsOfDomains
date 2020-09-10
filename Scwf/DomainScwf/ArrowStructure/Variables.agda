{-# OPTIONS --safe #-}

open import Base.Core

module Scwf.DomainScwf.ArrowStructure.Variables (𝐴 𝐵 : Ty) where

open import Base.FinFun

open import Agda.Builtin.Nat

variable
  𝑓 𝑓′ 𝑓″ 𝑓‴ : NbhFinFun 𝐴 𝐵
