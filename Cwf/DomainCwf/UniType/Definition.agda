{-# OPTIONS --safe --sized-types #-}

module Cwf.DomainCwf.UniType.Definition where

open import Base.Core

open import Agda.Builtin.Size

data Nbh : {Size} → Set
data FinFun : {Size} → Set

data Nbh where
  ⊥ : ∀ {i} → Nbh {i}
  0ᵤ : ∀ {i} → Nbh {i}
  s : ∀ {i} → Nbh {i} → Nbh {i}
  ℕ : ∀ {i} → Nbh {i}
  F : ∀ {i} → FinFun {i} -> Nbh {↑ i}
  Π : ∀ {i} → Nbh {i} → FinFun {i} → Nbh {↑ i}
  𝒰 : ∀ {i} → Nbh {i}
  incons : ∀ {i} → Nbh {i}

data FinFun where
  ∅ : ∀ {i} → FinFun {i}
  _∷_ : ∀ {i} → (Nbh {i}) ⊠ (Nbh {i}) → FinFun {i} → FinFun {i}

_∪_ : ∀ {i} → FinFun {i} → FinFun {i} → FinFun {i}
(x ∷ 𝑓) ∪ 𝑓′ = x ∷ (𝑓 ∪ 𝑓′)
∅ ∪ 𝑓′ = 𝑓′

_⊔_ : ∀ {i} → Nbh {i} -> Nbh {i} -> Nbh {i}
⊥ ⊔ u = u
0ᵤ ⊔ ⊥ = 0ᵤ
0ᵤ ⊔ 0ᵤ = 0ᵤ
0ᵤ ⊔ (s _) = incons
0ᵤ ⊔ ℕ = incons
0ᵤ ⊔ (F _) = incons
0ᵤ ⊔ (Π _ _) = incons
0ᵤ ⊔ 𝒰 = incons
0ᵤ ⊔ incons = incons
(s u) ⊔ ⊥ = s u
(s _) ⊔ 0ᵤ = incons
(s u) ⊔ (s v) = s (u ⊔ v)
(s _) ⊔ ℕ = incons
(s _) ⊔ (F _) = incons
(s _) ⊔ (Π _ _) = incons
(s _) ⊔ 𝒰 = incons
(s _) ⊔ incons = incons
ℕ ⊔ ⊥ = ℕ
ℕ ⊔ 0ᵤ = incons
ℕ ⊔ (s _) = incons
ℕ ⊔ ℕ = ℕ
ℕ ⊔ (F _) = incons
ℕ ⊔ (Π _ _) = incons
ℕ ⊔ 𝒰 = incons
ℕ ⊔ incons = incons
(F f) ⊔ ⊥ = F f
(F _) ⊔ 0ᵤ = incons
(F _) ⊔ (s _) = incons
(F _) ⊔ ℕ = incons
(F f) ⊔ (F g) = F (f ∪ g)
(F _) ⊔ (Π _ _) = incons
(F _) ⊔ 𝒰 = incons
(F _) ⊔ incons = incons
(Π u f) ⊔ ⊥ = Π u f
(Π _ _) ⊔ 0ᵤ = incons
(Π _ _) ⊔ (s _) = incons
(Π _ _) ⊔ ℕ = incons
(Π _ _) ⊔ (F _) = incons
(Π u f) ⊔ (Π v g) = Π (u ⊔ v) (f ∪ g)
(Π _ _) ⊔ 𝒰 = incons
(Π _ _) ⊔ incons = incons
𝒰 ⊔ ⊥ = 𝒰
𝒰 ⊔ 0ᵤ = incons
𝒰 ⊔ (s _) = incons
𝒰 ⊔ ℕ = incons
𝒰 ⊔ (F _) = incons
𝒰 ⊔ (Π _ _) = incons
𝒰 ⊔ 𝒰 = 𝒰
𝒰 ⊔ incons = incons
incons ⊔ _ = incons

pre : ∀ {i} → FinFun {i} → Nbh {i}
pre ∅ = ⊥
pre ((u , v) ∷ f) = u ⊔ pre f

post : ∀ {i} → FinFun {i} → Nbh {i}
post ∅ = ⊥
post ((u , v) ∷ f) = v ⊔ post f
