{-# OPTIONS --safe --sized-types #-}

module Ucwf.DomainUcwf.UniType.Definition where

open import Agda.Builtin.Size

-- We give pairs, finite functions, neighborhoods of the
-- universal type, and related concepts sizes.
-- This lets Agda see that the recursion used in the
-- transitivity proof is well-founded.
data ×ₛ : {i : Size} → Set
data FinFunₛ : {i : Size} → Set
data UniNbh : {i : Size} → Set

data ×ₛ where
  <_,_>ₛ : ∀ {i} → (x y : UniNbh {i}) → ×ₛ {i}

data FinFunₛ where
  ∅ : ∀ {i} → FinFunₛ {i}
  _∷_ : ∀ {i} → ×ₛ {i} → FinFunₛ {i} → FinFunₛ {i}

data UniNbh where
  ⊥ᵤ : ∀ {i} → UniNbh {i}
  -- Note that λᵤ increases the size!
  λᵤ : ∀ {i} → FinFunₛ {i} → UniNbh {↑ i}

_∪ₛ_ : ∀ {i} → FinFunₛ {i} → FinFunₛ {i} → FinFunₛ {i}
∅ ∪ₛ 𝑓′ = 𝑓′
(x ∷ 𝑓) ∪ₛ 𝑓′ = x ∷ (𝑓 ∪ₛ 𝑓′)

_⊔ᵤ_ : ∀ {i} → UniNbh {i} → UniNbh {i} → UniNbh {i}
⊥ᵤ ⊔ᵤ ⊥ᵤ = ⊥ᵤ
⊥ᵤ ⊔ᵤ (λᵤ 𝑓) = λᵤ 𝑓
(λᵤ 𝑓) ⊔ᵤ ⊥ᵤ = λᵤ 𝑓
(λᵤ 𝑓) ⊔ᵤ (λᵤ 𝑓′) = λᵤ (𝑓 ∪ₛ 𝑓′)
