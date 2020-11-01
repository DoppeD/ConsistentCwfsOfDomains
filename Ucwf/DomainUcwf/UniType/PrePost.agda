{-# OPTIONS --safe --sized-types #-}

module Ucwf.DomainUcwf.UniType.PrePost where

open import Base.Core
open import Base.FinFun
open import Ucwf.DomainUcwf.UniType.Definition

pre : ∀ {i} → FinFunₛ {i} → UniNbh {i}
pre ∅ = ⊥ᵤ
pre ((x , y) ∷ 𝑓) = x ⊔ᵤ pre 𝑓 [ con-all ]

post : ∀ {i} → FinFunₛ {i} → UniNbh {i}
post ∅ = ⊥ᵤ
post ((x , y) ∷ 𝑓) = y ⊔ᵤ post 𝑓 [ con-all ]
