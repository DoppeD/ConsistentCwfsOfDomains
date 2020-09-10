{-# OPTIONS --safe #-}

module Scwf.DomainScwf.ProductStructure.Unit.NbhSys.AxiomProofs where

open import Scwf.DomainScwf.ProductStructure.Unit.NbhSys.Definition

private
  variable
    x y z : UnitNbh

Con-⊔₁ : x ⊑₁ z → y ⊑₁ z → UnitCon x y
Con-⊔₁ _ _ = allCon

⊑₁-refl : x ⊑₁ x
⊑₁-refl {⊥₁} = ⊥₁-bot
⊑₁-refl {0₁} = 0₁-refl

⊑₁-trans : x ⊑₁ y → y ⊑₁ z → x ⊑₁ z
⊑₁-trans ⊥₁-bot _ = ⊥₁-bot
⊑₁-trans 0₁-refl 0₁-refl = 0₁-refl

⊑₁-⊥ : ⊥₁ ⊑₁ x
⊑₁-⊥ = ⊥₁-bot

⊑₁-⊔ : y ⊑₁ x → z ⊑₁ x → (con : UnitCon y z) → (y ⊔₁ z [ con ]) ⊑₁ x
⊑₁-⊔ ⊥₁-bot ⊥₁-bot _ = ⊥₁-bot
⊑₁-⊔ ⊥₁-bot 0₁-refl _ = 0₁-refl
⊑₁-⊔ 0₁-refl _ _ = 0₁-refl

⊑₁-⊔-fst : (con : UnitCon x y) → x ⊑₁ (x ⊔₁ y [ con ])
⊑₁-⊔-fst {⊥₁} _ = ⊥₁-bot
⊑₁-⊔-fst {0₁} _ = 0₁-refl

⊑₁-⊔-snd : (con : UnitCon x y) → y ⊑₁ (x ⊔₁ y [ con ])
⊑₁-⊔-snd {y = ⊥₁} _ = ⊥₁-bot
⊑₁-⊔-snd {x = ⊥₁} {y = 0₁} _ = 0₁-refl
⊑₁-⊔-snd {x = 0₁} {y = 0₁} _ = 0₁-refl
