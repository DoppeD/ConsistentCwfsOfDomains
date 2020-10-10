{-# OPTIONS --safe #-}

module PCF.DomainPCF.Functions.suc.AxiomProofs where

open import Base.Core
open import Base.FinFun
open import Base.Variables
open import NbhSys.Definition
open import NbhSys.Lemmata
open import PCF.DomainPCF.Functions.suc.Relation
open import PCF.DomainPCF.Nat.NbhSys.Definition
open import PCF.DomainPCF.Nat.NbhSys.Instance
open import PCF.DomainPCF.Nat.NbhSys.Lemmata
open import PCF.DomainPCF.Nat.NbhSys.Relation
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Instance
open import Scwf.DomainScwf.ArrowStructure.NbhSys.ConFinFun Nat Nat
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Definition Nat Nat
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Instance
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Post Nat Nat
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Pre Nat Nat
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Relation Nat Nat

suc↦-mono : ∀ {𝑥 𝑦 z} → [ ValNbhSys Γ ] 𝑥 ⊑ 𝑦 →
             𝑥 suc↦ z → 𝑦 suc↦ z
suc↦-mono _ suc↦-intro₁ = suc↦-intro₁
suc↦-mono _ (suc↦-intro₂ p) = suc↦-intro₂ p

suc↦-bottom : {𝑥 : Valuation Γ} → 𝑥 suc↦ ⊥ₑ
suc↦-bottom = suc↦-intro₁

suc↦-↓closed'' : ∀ {sub preable postable} →
                 (∀ {x y} → (x , y) ∈ sub → [ Nat ] y ⊑ sₙ x) →
                 [ Nat ] post sub postable ⊑ sₙ (pre sub preable)
suc↦-↓closed'' {∅} _ = ⊑ₙ-intro₁
suc↦-↓closed'' {(x , y) ∷ sub} {pre-cons preable conxpresub}
  {post-cons postable _} p
  = NbhSys.⊑-trans Nat proof₁ proof₂
  where rec = suc↦-↓closed'' λ xy∈sub → p (⊆-lemma₃ xy∈sub)
        proof₁ = ⊑-⊔-lemma₃ Nat _ (conₙ-sₙ conxpresub) (p here) rec
        proof₂ = natLemma₂ {x = x} {y = pre sub preable}

suc↦-↓closed' : ∀ {𝑓 𝑓′ con𝑓′} →
                (∀ {x y} → (x , y) ∈ 𝑓 → ⊑ₑ-proof 𝑓′ con𝑓′ x y) →
                (∀ {x y} → (x , y) ∈ 𝑓′ → [ Nat ] y ⊑ sₙ x) →
                ∀ {x y} → (x , y) ∈ 𝑓 → [ Nat ] y ⊑ sₙ x
suc↦-↓closed' p₁ p₂ xy∈𝑓 with (p₁ xy∈𝑓)
... | record { sub⊆𝑓 = sub⊆𝑓
             ; y⊑post = y⊑post
             ; pre⊑x = pre⊑x
             }
  = NbhSys.⊑-trans Nat y⊑post post⊑sx
  where proof = suc↦-↓closed'' λ xy∈sub → p₂ (sub⊆𝑓 xy∈sub)
        post⊑sx = NbhSys.⊑-trans Nat proof (⊑ₙ-intro₃ pre⊑x)

suc↦-↓closed : {𝑥 : Valuation Γ} → ∀ {y z} → y ⊑ₑ z →
                𝑥 suc↦ z → 𝑥 suc↦ y
suc↦-↓closed ⊑ₑ-intro₁ _ = suc↦-intro₁
suc↦-↓closed (⊑ₑ-intro₂ con𝑓 _ p₁) (suc↦-intro₂ p₂)
  = suc↦-intro₂ (suc↦-↓closed' p₁ p₂)

suc↦-↑directed' : ∀ {𝑓 𝑓′} →
                  (∀ {x y} → (x , y) ∈ 𝑓 → [ Nat ] y ⊑ sₙ x) →
                  (∀ {x y} → (x , y) ∈ 𝑓′ → [ Nat ] y ⊑ sₙ x) →
                  (∀ {x y} → (x , y) ∈ (𝑓 ∪ 𝑓′) →
                  [ Nat ] y ⊑ sₙ x)
suc↦-↑directed' p₁ p₂ xy∈∪ with (∪-lemma₂ xy∈∪)
... | inl xy∈𝑓 = p₁ xy∈𝑓
... | inr xy∈𝑓′ = p₂ xy∈𝑓′

suc↦-↑directed : {𝑥 : Valuation Γ} → ∀ {y z} →
                  𝑥 suc↦ y → 𝑥 suc↦ z →
                  ∀ conyz → 𝑥 suc↦ (y ⊔ₑ z [ conyz ])
suc↦-↑directed suc↦-intro₁ suc↦-intro₁ conₑ-⊥₁ = suc↦-intro₁
suc↦-↑directed suc↦-intro₁ suc↦-intro₁ conₑ-⊥₂ = suc↦-intro₁
suc↦-↑directed suc↦-intro₁ (suc↦-intro₂ p) conₑ-⊥₂ = suc↦-intro₂ p
suc↦-↑directed (suc↦-intro₂ p) suc↦-intro₁ conₑ-⊥₁ = suc↦-intro₂ p
suc↦-↑directed (suc↦-intro₂ p₁) (suc↦-intro₂ p₂) (con-∪ _ _ _)
  = suc↦-intro₂ (suc↦-↑directed' p₁ p₂)

suc↦-con'' : ∀ {𝑔} →
             (∀ {x y} → (x , y) ∈ 𝑔 → [ Nat ] y ⊑ sₙ x) →
             ∀ preable𝑔 → ∀ {x y} → (x , y) ∈ 𝑔 →
             [ Nat ] y ⊑ sₙ (pre 𝑔 preable𝑔)
suc↦-con'' p (pre-cons preable𝑔 conxpre𝑔) {x} here
  = NbhSys.⊑-trans Nat (p here) sx⊑spre
  where sx⊑sx⊔spre = NbhSys.⊑-⊔-fst Nat (conₙ-sₙ conxpre𝑔)
        proof = natLemma₂ {conxy = conxpre𝑔}
        sx⊑spre = NbhSys.⊑-trans Nat sx⊑sx⊔spre proof
suc↦-con'' p (pre-cons preable𝑔 conxpre𝑔) (there xy∈𝑔)
  with (suc↦-con'' (λ xy∈𝑔 → p (there xy∈𝑔)) preable𝑔 xy∈𝑔)
... | ⊑ₙ-intro₁ = ⊑ₙ-intro₁
... | ⊑ₙ-intro₃ x⊑pre𝑔
  = ⊑ₙ-intro₃ (⊑-⊔-lemma₅ Nat x⊑pre𝑔 conxpre𝑔)

suc↦-con' : ∀ {𝑓 𝑓′ 𝑔} → 𝑔 ⊆ (𝑓 ∪ 𝑓′) →
            (∀ {x y} → (x , y) ∈ 𝑓 → [ Nat ] y ⊑ sₙ x) →
            (∀ {x y} → (x , y) ∈ 𝑓′ → [ Nat ] y ⊑ sₙ x) →
            ∀ {x y} → (x , y) ∈ 𝑔 → [ Nat ] y ⊑ sₙ x
suc↦-con' {𝑓} 𝑔⊆∪ p₁ p₂ xy∈𝑔 with (∪-lemma₂ {𝑓 = 𝑓} (𝑔⊆∪ xy∈𝑔))
... | inl xy∈𝑓 = p₁ xy∈𝑓
... | inr xy∈𝑓′ = p₂ xy∈𝑓′

suc↦-con : {𝑥 : Valuation Γ} → ∀ {y 𝑥′ y′} →
            𝑥 suc↦ y → 𝑥′ suc↦ y′ →
            ValCon _ 𝑥 𝑥′ → ArrCon y y′
suc↦-con suc↦-intro₁ suc↦-intro₁ _ = conₑ-⊥₁
suc↦-con suc↦-intro₁ (suc↦-intro₂ _) _ = conₑ-⊥₂
suc↦-con (suc↦-intro₂ _) suc↦-intro₁ _ = conₑ-⊥₁
suc↦-con (suc↦-intro₂ p₁) (suc↦-intro₂ p₂) _
  = con-∪ _ _ (cff λ 𝑔⊆∪ preable𝑔 →
    boundedPostable (suc↦-con'' (suc↦-con' 𝑔⊆∪ p₁ p₂) preable𝑔))
