module PCF.DomainPCF.Nat.NbhSys.AxiomProofs where

open import PCF.DomainPCF.Nat.NbhSys.Definition
open import PCF.DomainPCF.Nat.NbhSys.Relation

Conₙ-⊔ : ∀ {x y z} → x ⊑ₙ z → y ⊑ₙ z →
         Conₙ x y
Conₙ-⊔ ⊑ₙ-intro₁ _
  = conₙ-bot₁
Conₙ-⊔ ⊑ₙ-intro₂ ⊑ₙ-intro₁
  = conₙ-bot₂
Conₙ-⊔ ⊑ₙ-intro₂ ⊑ₙ-intro₂
  = conₙ-0ₙ
Conₙ-⊔ (⊑ₙ-intro₃ _) ⊑ₙ-intro₁
  = conₙ-bot₂
Conₙ-⊔ (⊑ₙ-intro₃ x⊑z) (⊑ₙ-intro₃ y⊑z)
  = conₙ-sₙ (Conₙ-⊔ x⊑z y⊑z)

⊑ₙ-refl : ∀ {x} → x ⊑ₙ x
⊑ₙ-refl {⊥ₙ} = ⊑ₙ-intro₁
⊑ₙ-refl {0ₙ} = ⊑ₙ-intro₂
⊑ₙ-refl {sₙ x} = ⊑ₙ-intro₃ ⊑ₙ-refl

⊑ₙ-trans : ∀ {x y z} → x ⊑ₙ y → y ⊑ₙ z →
           x ⊑ₙ z
⊑ₙ-trans ⊑ₙ-intro₁ _
  = ⊑ₙ-intro₁
⊑ₙ-trans ⊑ₙ-intro₂ ⊑ₙ-intro₂
  = ⊑ₙ-intro₂
⊑ₙ-trans (⊑ₙ-intro₃ x⊑y) (⊑ₙ-intro₃ y⊑z)
  = ⊑ₙ-intro₃ (⊑ₙ-trans x⊑y y⊑z)

⊑ₙ-⊔ : ∀ {x y z} → y ⊑ₙ x → z ⊑ₙ x →
       ∀ conyz → (y ⊔ₙ z [ conyz ]) ⊑ₙ x
⊑ₙ-⊔ _ z⊑x conₙ-bot₁ = z⊑x
⊑ₙ-⊔ y⊑x _ conₙ-bot₂ = y⊑x
⊑ₙ-⊔ 0⊑x _ conₙ-0ₙ = 0⊑x
⊑ₙ-⊔ (⊑ₙ-intro₃ y⊑x) (⊑ₙ-intro₃ z⊑x) (conₙ-sₙ conyz)
  = ⊑ₙ-intro₃ (⊑ₙ-⊔ y⊑x z⊑x conyz)

⊑ₙ-⊔-fst : ∀ {x y} → ∀ conxy →
           x ⊑ₙ (x ⊔ₙ y [ conxy ])
⊑ₙ-⊔-fst conₙ-bot₁ = ⊑ₙ-intro₁
⊑ₙ-⊔-fst conₙ-bot₂ = ⊑ₙ-refl
⊑ₙ-⊔-fst conₙ-0ₙ = ⊑ₙ-intro₂
⊑ₙ-⊔-fst (conₙ-sₙ conxy)
  = ⊑ₙ-intro₃ (⊑ₙ-⊔-fst conxy)

⊑ₙ-⊔-snd : ∀ {x y} → ∀ conxy →
           y ⊑ₙ (x ⊔ₙ y [ conxy ])
⊑ₙ-⊔-snd conₙ-bot₁ = ⊑ₙ-refl
⊑ₙ-⊔-snd conₙ-bot₂ = ⊑ₙ-intro₁
⊑ₙ-⊔-snd conₙ-0ₙ = ⊑ₙ-intro₂
⊑ₙ-⊔-snd (conₙ-sₙ conxy)
  = ⊑ₙ-intro₃ (⊑ₙ-⊔-snd conxy)
