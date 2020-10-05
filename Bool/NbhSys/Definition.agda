module Bool.NbhSys.Definition where

data BoolNbh : Set where
  ⊥b : BoolNbh
  t : BoolNbh
  f : BoolNbh → BoolNbh

data Conb : BoolNbh → BoolNbh → Set where
  conb-bot₁ : ∀ {x} → Conb ⊥b x
  conb-bot₂ : ∀ {x} → Conb x ⊥b
  conb-refl : ∀ {x} → Conb x x

_⊔b_[_] : ∀ x y → Conb x y → BoolNbh
_ ⊔b y [ conb-bot₁ ] = y
x ⊔b _ [ conb-bot₂ ] = x
x ⊔b y [ conb-refl ] = x
