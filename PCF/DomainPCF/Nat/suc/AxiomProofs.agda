{-# OPTIONS --safe #-}

module PCF.DomainPCF.Nat.suc.AxiomProofs where

open import Base.Core
open import Base.FinFun
open import Base.Variables
open import NbhSys.Definition
open import NbhSys.Lemmata
open import PCF.DomainPCF.Nat.NbhSys.Definition
open import PCF.DomainPCF.Nat.NbhSys.Instance
open import PCF.DomainPCF.Nat.NbhSys.Lemmata
open import PCF.DomainPCF.Nat.NbhSys.Relation
open import PCF.DomainPCF.Nat.suc.Relation
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

suc↦-↑directed : {𝑥 : Valuation Γ} → ∀ {y z} →
                  𝑥 suc↦ y → 𝑥 suc↦ z →
                  ∀ conyz → 𝑥 suc↦ (y ⊔ₑ z [ conyz ])
suc↦-↑directed = {!!}

suc↦-con : {𝑥 : Valuation Γ} → ∀ {y 𝑥′ y′} →
            𝑥 suc↦ y → 𝑥′ suc↦ y′ →
            ValCon _ 𝑥 𝑥′ → ArrCon y y′
suc↦-con = {!!}
