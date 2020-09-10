{-# OPTIONS --safe #-}

module Scwf.DomainScwf.ProductStructure.Unit.NbhSys.Definition where

data UnitNbh : Set where
  ⊥₁ : UnitNbh
  0₁ : UnitNbh

data _⊑₁_ : UnitNbh → UnitNbh → Set where
  ⊥₁-bot : ∀ {x} → ⊥₁ ⊑₁ x
  0₁-refl : 0₁ ⊑₁ 0₁

data UnitCon : UnitNbh → UnitNbh → Set where
  allCon : ∀ {x y} → UnitCon x y

_⊔₁_[_] : (x : UnitNbh) → (y : UnitNbh) → UnitCon x y → UnitNbh
⊥₁ ⊔₁ y [ _ ] = y
0₁ ⊔₁ y [ _ ] = 0₁
