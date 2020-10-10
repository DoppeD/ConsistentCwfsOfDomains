{-# OPTIONS --safe #-}

module PCF.DomainPCF.Functions.suceq where

open import Appmap.Definition
open import Appmap.Equivalence
open import Appmap.PrincipalIdeal.Relation
open import Base.Core
open import Base.FinFun
open import Base.Variables
open import NbhSys.Definition
open import PCF.DomainPCF.Functions.suc.AxiomProofs
open import PCF.DomainPCF.Functions.suc.Instance
open import PCF.DomainPCF.Functions.suc.Relation
open import PCF.DomainPCF.Nat.NbhSys.Definition
open import PCF.DomainPCF.Nat.NbhSys.Instance
open import PCF.DomainPCF.Nat.NbhSys.Lemmata
open import PCF.DomainPCF.Nat.NbhSys.Relation
open import PCF.DomainPCF.Nat.num.Instance
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.ArrowStructure.ap.Instance
open import Scwf.DomainScwf.ArrowStructure.ap.Relation
open import Scwf.DomainScwf.ArrowStructure.NbhSys.ConFinFun Nat Nat
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Instance
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Relation Nat Nat

open import Agda.Builtin.Nat
  renaming (Nat to AgdaNat ; suc to AgdaSuc)
  hiding (zero)

suceqLemma₁ : {𝑥 : Valuation Γ} → ∀ {y} →
              [ ap suc (num n) ] 𝑥 ↦ y →
              [ num (AgdaSuc n) ] 𝑥 ↦ y
suceqLemma₁ (ap↦-intro₁ ⊑ₙ-intro₁)
  = ideal↦-intro ⊑ₙ-intro₁
suceqLemma₁ (ap↦-intro₂ con𝑓 _ (suc↦-intro₂ p₁)
  (ideal↦-intro p₂) (⊑ₑ-intro₂ _ _ p₃)) with (p₃ here)
... | record { sub = sub
             ; sub⊆𝑓 = sub⊆𝑓
             ; preablesub = preablesub
             ; postablesub = postablesub
             ; y⊑post = y⊑post
             ; pre⊑x = pre⊑x
             }
  = ideal↦-intro y⊑sn
  where spre⊑sn = NbhSys.⊑-trans Nat (natLemma₁ pre⊑x) (⊑ₙ-intro₃ p₂)
        post⊑spre = suc↦-↓closed'' {preable = preablesub}
                    (λ xy∈sub → p₁ (sub⊆𝑓 xy∈sub))
        post⊑sn = NbhSys.⊑-trans Nat post⊑spre spre⊑sn
        y⊑sn = NbhSys.⊑-trans Nat y⊑post post⊑sn

suceqLemma₂' : ∀ {x x′ y′} →
               (x′ , y′) ∈ ((x , sₙ x) ∷ ∅) →
               [ Nat ] y′ ⊑ sₙ x′
suceqLemma₂' here = ⊑ₙ-intro₃ (NbhSys.⊑-refl Nat)

suceqLemma₂ : {𝑥 : Valuation Γ} → ∀ {y} →
              [ num (AgdaSuc n) ] 𝑥 ↦ y →
              [ ap suc (num n) ] 𝑥 ↦ y
suceqLemma₂ (ideal↦-intro ⊑ₙ-intro₁) = ap↦-intro₁ ⊑ₙ-intro₁
suceqLemma₂ {n = n} (ideal↦-intro (⊑ₙ-intro₃ {x} x⊑n))
  = ap↦-intro₂ singletonIsCon singletonIsCon suc𝑥↦𝑓 (ideal↦-intro x⊑n)
    xsx⊑xsx
  where suc𝑥↦𝑓 = suc↦-intro₂ (suceqLemma₂')
        xsx⊑xsx = NbhSys.⊑-refl (Nat ⇒ Nat)

suceq : ∀ {n} → ap {Γ = Γ} suc (num n) ≈ num (AgdaSuc n)
suceq = ≈-intro (≼-intro suceqLemma₁)
         (≼-intro suceqLemma₂)
