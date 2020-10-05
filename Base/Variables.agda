{-# OPTIONS --safe #-}

module Base.Variables where

open import Base.Core

open import Agda.Builtin.Nat

variable
  m n o r : Nat
  Γ : Ctx m
  Δ : Ctx n
  Θ : Ctx o
  Λ : Ctx r
  𝐴 𝐵 𝐶 : Ty
  A B : Set
