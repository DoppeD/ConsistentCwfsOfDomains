module Cwf.UniType.Relation where

open import Base.FinFun
open import Cwf.UniType.Consistency
open import Cwf.UniType.Definition

-- TODO
data _⊑ᵤ_ : ∀ {i} → Nbh {i} → Nbh {i} → Set where
  ⊑ᵤ-bot : ∀ {i} → {x : Nbh {i}} → ⊥ ⊑ᵤ x
  ⊑ᵤ-ref : ∀ {i} → {x : Nbh {i}} → x ⊑ᵤ x
  ⊑ᵤ-s : ∀ {i} → {x y : Nbh {i}} → x ⊑ᵤ y → sᵤ x ⊑ᵤ sᵤ y
  ⊑ᵤ-Π : ∀ {i} → {x y : Nbh {i}} → {𝑓 𝑔 : FinFun (Nbh {i}) (Nbh {i})} →
         {con𝑓 : ConFinFun 𝑓} → {con𝑔 : ConFinFun 𝑔} →
         x ⊑ᵤ y → (λᵤ 𝑓) ⊑ᵤ (λᵤ 𝑔) → (Π x 𝑓) ⊑ᵤ (Π y 𝑔)

_⊔ᵤ_[_] : ∀ {i} → (x y : Nbh {i}) → Con x y → Nbh {i}
⊥ ⊔ᵤ y [ _ ] = y
0ₙ ⊔ᵤ ⊥ [ _ ] = 0ₙ
(sᵤ x) ⊔ᵤ ⊥ [ _ ] = sᵤ x
ℕ ⊔ᵤ ⊥ [ _ ] = ℕ
𝒰 ⊔ᵤ ⊥ [ _ ] = 𝒰
(λᵤ 𝑓) ⊔ᵤ ⊥ [ _ ] = λᵤ 𝑓
(Π x 𝑓) ⊔ᵤ ⊥ [ _ ] = Π x 𝑓
0ₙ ⊔ᵤ 0ₙ [ _ ] = 0ₙ
ℕ ⊔ᵤ ℕ [ _ ] = ℕ
𝒰 ⊔ᵤ 𝒰 [ _ ] = 𝒰
(sᵤ x) ⊔ᵤ (sᵤ y) [ con-s conxy ]
  = sᵤ (x ⊔ᵤ y [ conxy ])
(λᵤ 𝑓) ⊔ᵤ (λᵤ 𝑔) [ _ ] = λᵤ (𝑓 ∪ 𝑔)
Π x 𝑓 ⊔ᵤ Π y 𝑔 [ con-Π conxy _ ]
  = Π (x ⊔ᵤ y [ conxy ]) (𝑓 ∪ 𝑔)
