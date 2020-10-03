module PCF.Nat.NbhSys where

open import Appmap.Definition
open import NbhSys.Definition

data NatNbh : Set where
  ⊥ₙ : NatNbh
  0ₙ : NatNbh
  sₙ : NatNbh → NatNbh

data _⊑ₙ_ : NatNbh → NatNbh → Set where
  ⊑ₙ-intro₁ : ∀ {x} → ⊥ₙ ⊑ₙ x
  ⊑ₙ-intro₂ : 0ₙ ⊑ₙ 0ₙ
  ⊑ₙ-intro₃ : ∀ {x y} → x ⊑ₙ y → sₙ x ⊑ₙ sₙ y

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

NatNbhSys : NbhSys
NbhSys.Nbh NatNbhSys = NatNbh
NbhSys._⊑_ NatNbhSys = _⊑ₙ_
NbhSys.Con NatNbhSys = Conₙ
NbhSys._⊔_[_] NatNbhSys = _⊔ₙ_[_]
NbhSys.⊥ NatNbhSys = ⊥ₙ
NbhSys.Con-⊔ NatNbhSys = Conₙ-⊔
NbhSys.⊑-refl NatNbhSys = ⊑ₙ-refl
NbhSys.⊑-trans NatNbhSys = ⊑ₙ-trans
NbhSys.⊑-⊥ NatNbhSys = ⊑ₙ-intro₁
NbhSys.⊑-⊔ NatNbhSys = ⊑ₙ-⊔
NbhSys.⊑-⊔-fst NatNbhSys = ⊑ₙ-⊔-fst
NbhSys.⊑-⊔-snd NatNbhSys = ⊑ₙ-⊔-snd

data _suc↦_ : NatNbh → NatNbh → Set where
  suc↦-intro₁ : ∀ {x y} → y ⊑ₙ (sₙ x) → x suc↦ y

suc↦-mono : ∀ {x y z} → x ⊑ₙ y → x suc↦ z →
            y suc↦ z
suc↦-mono ⊑ₙ-intro₁ (suc↦-intro₁ z⊑sx)
  = suc↦-intro₁ (⊑ₙ-trans z⊑sx (⊑ₙ-intro₃ ⊑ₙ-intro₁))
suc↦-mono ⊑ₙ-intro₂ (suc↦-intro₁ z⊑sx)
  = suc↦-intro₁ z⊑sx
suc↦-mono (⊑ₙ-intro₃ x⊑y) (suc↦-intro₁ z⊑sx)
  = suc↦-intro₁ (⊑ₙ-trans z⊑sx (⊑ₙ-intro₃ (⊑ₙ-intro₃ x⊑y)))

suc↦-↓closed : ∀ {x y z} → y ⊑ₙ z → x suc↦ z →
               x suc↦ y
suc↦-↓closed ⊑ₙ-intro₁ (suc↦-intro₁ z⊑sx)
  = suc↦-intro₁ ⊑ₙ-intro₁
suc↦-↓closed (⊑ₙ-intro₃ y⊑z) (suc↦-intro₁ (⊑ₙ-intro₃ z⊑ssx))
  = suc↦-intro₁ (⊑ₙ-intro₃ (⊑ₙ-trans y⊑z z⊑ssx))

suc↦-↑directed : ∀ {x y z} → x suc↦ y → x suc↦ z →
                 ∀ conyz → x suc↦ (y ⊔ₙ z [ conyz ])
suc↦-↑directed _ (suc↦-intro₁ z⊑sx) conₙ-bot₁
  = suc↦-intro₁ z⊑sx
suc↦-↑directed (suc↦-intro₁ y⊑sx) (suc↦-intro₁ _) conₙ-bot₂
  = suc↦-intro₁ y⊑sx
suc↦-↑directed (suc↦-intro₁ ()) (suc↦-intro₁ z⊑sx) conₙ-0ₙ
suc↦-↑directed (suc↦-intro₁ (⊑ₙ-intro₃ y⊑x))
  (suc↦-intro₁ (⊑ₙ-intro₃ z⊑x)) (conₙ-sₙ conyz)
  = suc↦-intro₁ (⊑ₙ-intro₃ (⊑ₙ-⊔ y⊑x z⊑x conyz))

suc↦-con : ∀ {x y x′ y′} → x suc↦ y → x′ suc↦ y′ →
           Conₙ x x′ → Conₙ y y′
suc↦-con {x} {⊥ₙ} {x′} {y′} _ _ _ = conₙ-bot₁
suc↦-con {x} {sₙ y} {x′} {⊥ₙ} _ _ _ = conₙ-bot₂
suc↦-con {x} {y} {x′} {0ₙ} a (suc↦-intro₁ ()) _
suc↦-con {x} {0ₙ} {x′} {y′} (suc↦-intro₁ ()) (suc↦-intro₁ x₂) _
suc↦-con {x} {sₙ y} {x′} {sₙ y′} (suc↦-intro₁ sy⊑sx) (suc↦-intro₁ sy′⊑sx′) c = {!!}

suc : Appmap NatNbhSys NatNbhSys
Appmap._↦_ suc = _suc↦_
Appmap.↦-mono suc = suc↦-mono
Appmap.↦-bottom suc = suc↦-intro₁ ⊑ₙ-intro₁
Appmap.↦-↓closed suc = suc↦-↓closed
Appmap.↦-↑directed suc = suc↦-↑directed
Appmap.↦-con suc = {!!}
