{-# OPTIONS --safe #-}

module PCF.DomainPCF.Functions.zeroeq where

open import Appmap.Definition
open import Appmap.Equivalence
open import Appmap.PrincipalIdeal.Relation
open import Base.Core
open import Base.FinFun
open import Base.Variables
open import NbhSys.Definition
open import PCF.DomainPCF.Functions.zero.Instance
open import PCF.DomainPCF.Functions.zero.Relation
open import PCF.DomainPCF.Nat.NbhSys.Definition
open import PCF.DomainPCF.Nat.NbhSys.Instance
open import PCF.DomainPCF.Nat.NbhSys.Relation
open import PCF.DomainPCF.Nat.num.Instance
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.ArrowStructure.ap.Instance
open import Scwf.DomainScwf.ArrowStructure.ap.Relation
open import Scwf.DomainScwf.ArrowStructure.NbhSys.ConFinFun Nat Nat
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Instance
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Post Nat Nat
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Relation Nat Nat

open import Agda.Builtin.Nat renaming (Nat to AgdaNat) hiding (zero)

zeroeqLemma₁ : {𝑥 : Valuation Γ} → ∀ {y n} →
               [ ap zero (num n) ] 𝑥 ↦ y →
               [ num 0 ] 𝑥 ↦ y
zeroeqLemma₁ (ap↦-intro₁ y⊑⊥)
  = ideal↦-intro (NbhSys.⊑-trans Nat y⊑⊥ ⊑ₙ-intro₁)
zeroeqLemma₁
  (ap↦-intro₂ _ _ (zero↦-intro₂ p₁) _ (⊑ₑ-intro₂ _ _ p₂))
  with (p₂ here)
... | record { sub⊆𝑓 = sub⊆𝑓
             ; y⊑post = y⊑post
             }
  = ideal↦-intro (NbhSys.⊑-trans Nat y⊑post post⊑0)
  where post⊑0 = boundedPostable' λ xy∈sub → p₁ (sub⊆𝑓 xy∈sub)

zeroeqLemma₂' : ∀ {x y} → (x , y) ∈ ((⊥ₙ , 0ₙ) ∷ ∅) →
                [ Nat ] y ⊑ 0ₙ
zeroeqLemma₂' here = NbhSys.⊑-refl Nat

zeroeqLemma₂ : {𝑥 : Valuation Γ} → ∀ {y n} →
               [ num 0 ] 𝑥 ↦ y →
               [ ap zero (num n) ] 𝑥 ↦ y
zeroeqLemma₂ (ideal↦-intro ⊑ₙ-intro₁) = ap↦-intro₁ ⊑ₙ-intro₁
zeroeqLemma₂ (ideal↦-intro ⊑ₙ-intro₂)
  = ap↦-intro₂ singletonIsCon singletonIsCon y⊑0 num𝑥↦⊥ ⊥0⊑⊥0
  where y⊑0 = zero↦-intro₂ zeroeqLemma₂'
        num𝑥↦⊥ = ideal↦-intro (NbhSys.⊑-⊥ Nat)
        ⊥0⊑⊥0 = NbhSys.⊑-refl (Nat ⇒ Nat)

zeroeq : ∀ {n} → ap {Γ = Γ} zero (num n) ≈ num 0
zeroeq = ≈-intro (≼-intro zeroeqLemma₁)
         (≼-intro zeroeqLemma₂)
