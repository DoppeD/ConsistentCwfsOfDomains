{-# OPTIONS --safe --sized-types #-}

module Ucwf.DomainUcwf.UniType.Definition where

open import Base.Core
open import Base.FinFun

open import Agda.Builtin.Size

data UniNbh : ∀ {Size} → Set where
  ⊥ᵤ : ∀ {i} → UniNbh {i}
  -- Note that λᵤ increases the size!
  λᵤ : ∀ {i} → FinFun (UniNbh {i}) (UniNbh {i}) → UniNbh {↑ i}

FinFunₛ : ∀ {Size} → Set
FinFunₛ {i} = FinFun (UniNbh {i}) (UniNbh {i})

×ₛ : ∀ {Size} → Set
×ₛ {i} = (UniNbh {i}) ⊠ (UniNbh {i})

data UniCon : UniNbh → UniNbh → Set where
  con-all : ∀ {x y} → UniCon x y

_⊔ᵤ_[_] : ∀ {i} → (x y : UniNbh {i}) →
          UniCon x y → UniNbh {i}
⊥ᵤ ⊔ᵤ ⊥ᵤ [ _ ] = ⊥ᵤ
⊥ᵤ ⊔ᵤ (λᵤ 𝑓) [ _ ] = λᵤ 𝑓
(λᵤ 𝑓) ⊔ᵤ ⊥ᵤ [ _ ] = λᵤ 𝑓
(λᵤ 𝑓) ⊔ᵤ (λᵤ 𝑓′) [ _ ] = λᵤ (𝑓 ∪ 𝑓′)
