{-# OPTIONS --safe --sized-types #-}

module Ucwf.DomainUcwf.UniType.PrePost where

open import Ucwf.DomainUcwf.UniType.Definition

pre : ∀ {i} → FinFunₛ {i} → UniNbh {i}
pre ∅ = ⊥ᵤ
pre (< x , y >ₛ ∷ 𝑓) = x ⊔ᵤ pre 𝑓

post : ∀ {i} → FinFunₛ {i} → UniNbh {i}
post ∅ = ⊥ᵤ
post (< x , y >ₛ ∷ 𝑓) = y ⊔ᵤ post 𝑓
