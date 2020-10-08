{-# OPTIONS --safe #-}

module PCF.DomainPCF.Nat.NbhSys.Lemmata where

open import NbhSys.Definition
open import PCF.DomainPCF.Nat.NbhSys.Definition
open import PCF.DomainPCF.Nat.NbhSys.Instance
open import PCF.DomainPCF.Nat.NbhSys.Relation

natLemma₁ : ∀ {x y} → [ Nat ] x ⊑ y → [ Nat ] sₙ x ⊑ sₙ y
natLemma₁ ⊑ₙ-intro₁ = ⊑ₙ-intro₃ ⊑ₙ-intro₁
natLemma₁ ⊑ₙ-intro₂ = ⊑ₙ-intro₃ ⊑ₙ-intro₂
natLemma₁ (⊑ₙ-intro₃ x⊑y) = ⊑ₙ-intro₃ (natLemma₁ x⊑y)

natLemma₂ : ∀ {x y conxy} →
            [ Nat ] ((sₙ x) ⊔ₙ (sₙ y) [ conₙ-sₙ conxy ])
              ⊑ (sₙ (x ⊔ₙ y [ conxy ]))
natLemma₂ {conxy = conₙ-bot₁} = NbhSys.⊑-refl Nat
natLemma₂ {conxy = conₙ-bot₂} = NbhSys.⊑-refl Nat
natLemma₂ {conxy = conₙ-0ₙ} = NbhSys.⊑-refl Nat
natLemma₂ {conxy = conₙ-sₙ conxy}
  = natLemma₁ (natLemma₂ {conxy = conxy})

natLemma₃ : ∀ {x} → [ Nat ] 0ₙ ⊑ x → [ Nat ] x ⊑ 0ₙ
natLemma₃ ⊑ₙ-intro₂ = ⊑ₙ-intro₂

natLemma₄ : ∀ {x y} → [ Nat ] sₙ x ⊑ sₙ y → [ Nat ] x ⊑ y
natLemma₄ (⊑ₙ-intro₃ x⊑y) = x⊑y
