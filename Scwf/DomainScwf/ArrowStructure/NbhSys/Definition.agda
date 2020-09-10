{-# OPTIONS --safe #-}

open import Base.Core

module Scwf.DomainScwf.ArrowStructure.NbhSys.Definition
  (𝐴 𝐵 : Ty) where

open import Base.FinFun

data ArrNbh : Set where
  ⊥ₑ : ArrNbh
  𝐹 : NbhFinFun 𝐴 𝐵 → ArrNbh

_⊔ₑ_ : ArrNbh → ArrNbh → ArrNbh
⊥ₑ ⊔ₑ ⊥ₑ = ⊥ₑ
⊥ₑ ⊔ₑ (𝐹 𝑓) = 𝐹 𝑓
(𝐹 𝑓) ⊔ₑ ⊥ₑ = 𝐹 𝑓
(𝐹 𝑓) ⊔ₑ (𝐹 𝑓′) = 𝐹 (𝑓 ∪ 𝑓′)
