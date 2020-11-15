module Cwf.UniType.Coherency where

open import Base.Core
open import Base.FinFun
open import Cwf.UniType.Definition
open import Cwf.UniType.Lemmata
open import Cwf.UniType.Relation

coherency'' : ∀ {i} → {x y : Nbh {i}} → ∀ {con⊥y} →
              Con x y → Con x (⊥ ⊔ᵤ y [ con⊥y ])
coherency'' {y = ⊥} conxy = conxy
coherency'' {y = 0ₙ} conxy = conxy
coherency'' {y = sᵤ y} conxy = conxy
coherency'' {y = ℕ} conxy = conxy
coherency'' {y = 𝒰} conxy = conxy
coherency'' {y = λᵤ 𝑓 x} conxy = conxy
coherency'' {y = Π y 𝑓 x} conxy = conxy

coherency' : ∀ {i} → {𝑓 𝑔 ℎ : FinFun (Nbh {i}) (Nbh {i})} →
           ConFinFun (𝑓 ∪ 𝑔) → ConFinFun (𝑓 ∪ ℎ) →
           ConFinFun (𝑔 ∪ ℎ) → ∀ {x y x′ y′} →
           (x , y) ∈ (𝑓 ∪ (𝑔 ∪ ℎ)) →
           (x′ , y′) ∈ (𝑓 ∪ (𝑔 ∪ ℎ)) →
           Con x x′ → Con y y′
coherency' {𝑓 = 𝑓} _ _ _ xy∈∪ x′y′∈∪
  with (∪-lemma₂ {𝑓 = 𝑓} xy∈∪) | ∪-lemma₂ {𝑓 = 𝑓} x′y′∈∪
coherency' {𝑓 = 𝑓} cff𝑓∪𝑔 _ _ _ _ | inl xy∈𝑓 | inl x′y′∈𝑓
  = getCff {𝑓 = 𝑓} (subsetIsCon ∪-lemma₆ cff𝑓∪𝑔) xy∈𝑓 x′y′∈𝑓
coherency' {𝑔 = 𝑔} _ _ _ _ _ | inl _ | inr x′y′∈𝑔∪ℎ
  with (∪-lemma₂ {𝑓 = 𝑔} x′y′∈𝑔∪ℎ)
coherency' (cff p) _ _ _ _ | inl xy∈𝑓 | inr _ | inl x′y′∈𝑔
  = p (∪-lemma₆ xy∈𝑓) (∪-lemma₇ x′y′∈𝑔)
coherency' _ (cff p) _ _ _ | inl xy∈𝑓 | inr _ | inr x′y′∈ℎ
  = p (∪-lemma₆ xy∈𝑓) (∪-lemma₇ x′y′∈ℎ)
coherency' {𝑔 = 𝑔}  _ _ _ _ _ | inr xy∈𝑔∪ℎ | inl x′y′∈𝑓
  with (∪-lemma₂ {𝑓 = 𝑔} xy∈𝑔∪ℎ)
coherency' (cff p) _ _ _ _ | inr _ | inl x′y′∈𝑓 | inl xy∈𝑔
  = p (∪-lemma₇ xy∈𝑔) (∪-lemma₆ x′y′∈𝑓)
coherency' _ (cff p) _ _ _ | inr _ | inl x′y′∈𝑓 | inr xy∈ℎ
  = p (∪-lemma₇ xy∈ℎ) (∪-lemma₆ x′y′∈𝑓)
coherency' {𝑔 = 𝑔} {ℎ} _ _ cff𝑔∪ℎ _ _ | inr xy∈𝑔∪ℎ | inr x′y′∈𝑔∪ℎ
  = getCff {𝑓 = 𝑔 ∪ ℎ} cff𝑔∪ℎ xy∈𝑔∪ℎ x′y′∈𝑔∪ℎ

coherency : ∀ {i} → {x y z : Nbh {i}} → Con x y →
          Con x z → (conyz : Con y z) →
          Con x (y ⊔ᵤ z [ conyz ])
coherency con-⊥₁ _ conyz = con-⊥₁
coherency con-⊥₂ conxz _ = coherency'' conxz
coherency con-refl-0 con-⊥₂ _ = con-refl-0
coherency con-refl-0 con-refl-0 _ = con-refl-0
coherency (con-s conxy) con-⊥₂ _ = con-s conxy
coherency (con-s conxy) (con-s conxz) (con-s conyz)
  = con-s (coherency conxy conxz conyz)
coherency con-refl-ℕ con-⊥₂ _ = con-refl-ℕ
coherency con-refl-ℕ con-refl-ℕ _ = con-refl-ℕ
coherency con-refl-𝒰 con-⊥₂ _ = con-refl-𝒰
coherency con-refl-𝒰 con-refl-𝒰 _ = con-refl-𝒰
coherency (con-λ cff𝑓∪𝑔) con-⊥₂ _
  = con-λ cff𝑓∪𝑔
coherency {x = λᵤ 𝑓 _}
  (con-λ cff𝑓∪𝑔) (con-λ cff𝑓∪ℎ) (con-λ cff𝑔∪ℎ)
  = con-λ (cff (coherency' {𝑓 = 𝑓} cff𝑓∪𝑔 cff𝑓∪ℎ cff𝑔∪ℎ))
coherency (con-Π conxy cff𝑓∪𝑔) _ con-⊥₂
  = con-Π conxy cff𝑓∪𝑔
coherency {x = Π _ 𝑓 _}
  (con-Π conxy cff𝑓∪𝑔) (con-Π conxz cff𝑓∪ℎ) (con-Π conyz cff𝑔∪ℎ)
  = con-Π conxyz cff𝑓∪𝑔∪ℎ
  where conxyz = coherency conxy conxz conyz
        cff𝑓∪𝑔∪ℎ = cff (coherency' {𝑓 = 𝑓} cff𝑓∪𝑔 cff𝑓∪ℎ cff𝑔∪ℎ)
