{-# OPTIONS --safe #-}

open import Base.Core

module Scwf.DomainScwf.ArrowStructure.NbhSys.Definition
  (𝐴 𝐵 : Ty) where

open import Base.FinFun
open import Scwf.DomainScwf.ArrowStructure.NbhSys.ConFinFun 𝐴 𝐵

data ArrNbh : Set where
  ⊥ₑ : ArrNbh
  𝐹 : (𝑓 : NbhFinFun 𝐴 𝐵) → ConFinFun 𝑓 → ArrNbh

data ArrCon : ArrNbh → ArrNbh → Set where
  conₑ-⊥₁ : ∀ {x} → ArrCon x ⊥ₑ
  conₑ-⊥₂ : ∀ {x} → ArrCon ⊥ₑ x
  con-∪ : ∀ {𝑓 𝑓′} → (con𝑓 : ConFinFun 𝑓) → (con𝑓′ : ConFinFun 𝑓′) →
          ConFinFun (𝑓 ∪ 𝑓′) → ArrCon (𝐹 𝑓 con𝑓) (𝐹 𝑓′ con𝑓′)

_⊔ₑ_[_] : (x : ArrNbh) → (y : ArrNbh) → ArrCon x y → ArrNbh
⊥ₑ ⊔ₑ ⊥ₑ [ _ ] = ⊥ₑ
⊥ₑ ⊔ₑ (𝐹 𝑓′ con𝑓′) [ _ ] = 𝐹 𝑓′ con𝑓′
(𝐹 𝑓 con𝑓) ⊔ₑ ⊥ₑ [ _ ] = 𝐹 𝑓 con𝑓
𝐹 𝑓 _ ⊔ₑ 𝐹 𝑓′ _ [ con-∪ _ _ con∪ ] = 𝐹 (𝑓 ∪ 𝑓′) con∪
