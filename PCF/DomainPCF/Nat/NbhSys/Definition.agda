{-# OPTIONS --safe #-}

module PCF.DomainPCF.Nat.NbhSys.Definition where

data NatNbh : Set where
  ⊥ₙ : NatNbh
  0ₙ : NatNbh
  sₙ : NatNbh → NatNbh

data Conₙ : NatNbh → NatNbh → Set where
  conₙ-bot₁ : ∀ {x} → Conₙ ⊥ₙ x
  conₙ-bot₂ : ∀ {x} → Conₙ x ⊥ₙ
  conₙ-0ₙ : Conₙ 0ₙ 0ₙ
  conₙ-sₙ : ∀ {x y} → Conₙ x y → Conₙ (sₙ x) (sₙ y)

_⊔ₙ_[_] : ∀ x y → Conₙ x y → NatNbh
.⊥ₙ ⊔ₙ y [ conₙ-bot₁ ] = y
x ⊔ₙ .⊥ₙ [ conₙ-bot₂ ] = x
0ₙ ⊔ₙ 0ₙ [ conₙ-0ₙ ] = 0ₙ
(sₙ x) ⊔ₙ (sₙ y) [ conₙ-sₙ conxy ]
  = sₙ (x ⊔ₙ y [ conxy ])
