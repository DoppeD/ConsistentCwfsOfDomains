{-# OPTIONS --safe #-}

module PCF.DomainPCF.Bool.NbhSys.AxiomProofs where

open import PCF.DomainPCF.Bool.NbhSys.Definition
open import PCF.DomainPCF.Bool.NbhSys.Relation

Conb-⊔ : ∀ {x y z} → x ⊑b z → y ⊑b z →
         Conb x y
Conb-⊔ ⊑b-intro₁ _ = conb-bot₁
Conb-⊔ ⊑b-intro₂ ⊑b-intro₁ = conb-bot₂
Conb-⊔ ⊑b-intro₂ ⊑b-intro₂ = conb-refl

⊑b-refl : ∀ {x} → x ⊑b x
⊑b-refl = ⊑b-intro₂

⊑b-trans : ∀ {x y z} → x ⊑b y → y ⊑b z →
           x ⊑b z
⊑b-trans ⊑b-intro₁ _ = ⊑b-intro₁
⊑b-trans ⊑b-intro₂ ⊑b-intro₁ = ⊑b-intro₁
⊑b-trans ⊑b-intro₂ ⊑b-intro₂ = ⊑b-intro₂

⊑b-⊔ : ∀ {x y z} → y ⊑b x → z ⊑b x →
       ∀ conyz → (y ⊔b z [ conyz ]) ⊑b x
⊑b-⊔ _ z⊑x conb-bot₁ = z⊑x
⊑b-⊔ y⊑x _ conb-bot₂ = y⊑x
⊑b-⊔ y⊑x _ conb-refl = y⊑x

⊑b-⊔-fst : ∀ {x y} → ∀ conxy →
           x ⊑b (x ⊔b y [ conxy ])
⊑b-⊔-fst conb-bot₁ = ⊑b-intro₁
⊑b-⊔-fst conb-bot₂ = ⊑b-intro₂
⊑b-⊔-fst conb-refl = ⊑b-intro₂

⊑b-⊔-snd : ∀ {x y} → ∀ conxy →
           y ⊑b (x ⊔b y [ conxy ])
⊑b-⊔-snd conb-bot₁ = ⊑b-intro₂
⊑b-⊔-snd conb-bot₂ = ⊑b-intro₁
⊑b-⊔-snd conb-refl = ⊑b-intro₂
