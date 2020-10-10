{-# OPTIONS --safe #-}

module PCF.DomainPCF.Functions.zero.AxiomProofs where

open import Base.Core
open import Base.FinFun
open import Base.Variables
open import NbhSys.Definition
open import PCF.DomainPCF.Functions.zero.Relation
open import PCF.DomainPCF.Nat.NbhSys.Definition
open import PCF.DomainPCF.Nat.NbhSys.Instance
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Instance
open import Scwf.DomainScwf.ArrowStructure.NbhSys.ConFinFun Nat Nat
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Definition Nat Nat
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Instance
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Post Nat Nat
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Pre Nat Nat
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Relation Nat Nat

zero↦-mono : ∀ {𝑥 𝑦 z} → [ ValNbhSys Γ ] 𝑥 ⊑ 𝑦 →
             𝑥 zero↦ z → 𝑦 zero↦ z
zero↦-mono _ zero↦-intro₁ = zero↦-intro₁
zero↦-mono _ (zero↦-intro₂ p) = zero↦-intro₂ p

zero↦-bottom : {𝑥 : Valuation Γ} → 𝑥 zero↦ ⊥ₑ
zero↦-bottom = zero↦-intro₁

zero↦-↓closed' : ∀ {𝑓 𝑓′ con𝑓′} →
                 (∀ {x y} → (x , y) ∈ 𝑓 → ⊑ₑ-proof 𝑓′ con𝑓′ x y) →
                 (∀ {x y} → (x , y) ∈ 𝑓′ → [ Nat ] y ⊑ 0ₙ) →
                 ∀ {x y} → (x , y) ∈ 𝑓 → [ Nat ] y ⊑ 0ₙ
zero↦-↓closed' p₁ p₂ xy∈𝑓 with (p₁ xy∈𝑓)
... | record { sub⊆𝑓 = sub⊆𝑓
             ; y⊑post = y⊑post
             }
  = NbhSys.⊑-trans Nat y⊑post post⊑0
  where post⊑0 = boundedPostable' λ xy∈sub → p₂ (sub⊆𝑓 xy∈sub)

zero↦-↓closed : {𝑥 : Valuation Γ} → ∀ {y z} → y ⊑ₑ z →
                𝑥 zero↦ z → 𝑥 zero↦ y
zero↦-↓closed ⊑ₑ-intro₁ zero↦-intro₁ = zero↦-intro₁
zero↦-↓closed ⊑ₑ-intro₁ (zero↦-intro₂ x₁) = zero↦-intro₁
zero↦-↓closed (⊑ₑ-intro₂ con𝑓 con𝑓′ p₁) (zero↦-intro₂ p₂)
  = zero↦-intro₂ (zero↦-↓closed' p₁ p₂)

zero↦-↑directed' : {𝑓 𝑓′ : FinFun NatNbh NatNbh} →
                   (∀ {x y} → (x , y) ∈ 𝑓 → [ Nat ] y ⊑ 0ₙ) →
                   (∀ {x y} → (x , y) ∈ 𝑓′ → [ Nat ] y ⊑ 0ₙ) →
                   ∀ {x y} → (x , y) ∈ (𝑓 ∪ 𝑓′) → [ Nat ] y ⊑ 0ₙ
zero↦-↑directed' {𝑓} p₁ p₂ xy∈∪ with (∪-lemma₂ {𝑓 = 𝑓} xy∈∪)
... | inl xy∈𝑓 = p₁ xy∈𝑓
... | inr xy∈𝑓′ = p₂ xy∈𝑓′

zero↦-↑directed : {𝑥 : Valuation Γ} → ∀ {y z} →
                  𝑥 zero↦ y → 𝑥 zero↦ z →
                  ∀ conyz → 𝑥 zero↦ (y ⊔ₑ z [ conyz ])
zero↦-↑directed zero↦-intro₁ zero↦-intro₁ conyz
  = zero↦-intro₁
zero↦-↑directed zero↦-intro₁ (zero↦-intro₂ p) conₑ-⊥₂
  = zero↦-intro₂ p
zero↦-↑directed (zero↦-intro₂ p) zero↦-intro₁ conₑ-⊥₁
  = zero↦-intro₂ p
zero↦-↑directed (zero↦-intro₂ p₁) (zero↦-intro₂ p₂) (con-∪ _ _ _)
  = zero↦-intro₂ (zero↦-↑directed' p₁ p₂)

zero↦-con' : {𝑓 𝑓′ : FinFun NatNbh NatNbh} →
             (∀ {x y} → (x , y) ∈ 𝑓 → [ Nat ] y ⊑ 0ₙ) →
             (∀ {x y} → (x , y) ∈ 𝑓′ → [ Nat ] y ⊑ 0ₙ) →
             ∀ {g} → g ⊆ (𝑓 ∪ 𝑓′) → Preable g →
             Postable g
zero↦-con' p₁ p₂ g⊆∪ _ with (zero↦-↑directed' p₁ p₂)
... | y∈∪⊑0
  = boundedPostable (λ xy∈g → y∈∪⊑0 (g⊆∪ xy∈g))

zero↦-con : {𝑥 : Valuation Γ} → ∀ {y 𝑥′ y′} →
            𝑥 zero↦ y → 𝑥′ zero↦ y′ →
            ValCon _ 𝑥 𝑥′ → ArrCon y y′
zero↦-con zero↦-intro₁ zero↦-intro₁ _
  = conₑ-⊥₁
zero↦-con zero↦-intro₁ (zero↦-intro₂ _) _
  = conₑ-⊥₂
zero↦-con (zero↦-intro₂ _) zero↦-intro₁ _
  = conₑ-⊥₁
zero↦-con (zero↦-intro₂ p₁) (zero↦-intro₂ p₂) con𝑥𝑥′
  = con-∪ _ _ (cff (zero↦-con' p₁ p₂))
