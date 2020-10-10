{-# OPTIONS --safe #-}

module PCF.DomainPCF.Functions.predeq where

open import Appmap.Definition
open import Appmap.Equivalence
open import Appmap.PrincipalIdeal.Relation
open import Base.Core
open import Base.FinFun
open import Base.Variables
open import NbhSys.Definition
open import PCF.DomainPCF.Functions.pred.AxiomProofs
open import PCF.DomainPCF.Functions.pred.Instance
open import PCF.DomainPCF.Functions.pred.Relation
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

open import Agda.Builtin.Nat renaming (Nat to AgdaNat)

predeqLemma₁ : {𝑥 : Valuation Γ} → ∀ {y} →
               [ ap pred (num (suc n)) ] 𝑥 ↦ y →
               [ num n ] 𝑥 ↦ y
predeqLemma₁ (ap↦-intro₁ ⊑ₙ-intro₁)
  = ideal↦-intro ⊑ₙ-intro₁
predeqLemma₁ (ap↦-intro₂ _ _ _ _ (⊑ₑ-intro₂ _ _ p))
  with (p here)
predeqLemma₁ (ap↦-intro₂ _ _ (pred↦-intro₂ p₁) _ _)
  | record { sub = sub
           ; sub⊆𝑓 = sub⊆𝑓
           ; preablesub = preable
           ; postablesub = postable
           }
  with (pred↦-↓closed'' {sub} {preable} {postable}
       λ xy∈sub → p₁ (sub⊆𝑓 xy∈sub))
predeqLemma₁ (ap↦-intro₂ _ _ _ (ideal↦-intro x⊑sn) _)
  | record { y⊑post = y⊑post
           ; pre⊑x = pre⊑x
           }
  | pprop₁ _ post⊑⊥
  = ideal↦-intro y⊑n
  where post⊑n = NbhSys.⊑-trans Nat post⊑⊥ (NbhSys.⊑-⊥ Nat)
        y⊑n = NbhSys.⊑-trans Nat y⊑post post⊑n
predeqLemma₁ (ap↦-intro₂ _ _ _ (ideal↦-intro x⊑sn) _)
  | record { y⊑post = y⊑post
           ; pre⊑x = pre⊑x
           }
  | pprop₂ spost⊑pre
  = ideal↦-intro y⊑n
  where pre⊑sn = NbhSys.⊑-trans Nat pre⊑x x⊑sn
        spost⊑sn = NbhSys.⊑-trans Nat spost⊑pre pre⊑sn
        y⊑n = NbhSys.⊑-trans Nat y⊑post (natLemma₄ spost⊑sn)
--sₙ post ⊑ pre ⊑ s n ⇒  post ⊑ n

predeqLemma₂' : ∀ {y x′ y′} →
                (x′ , y′) ∈ ((sₙ y , y) ∷ ∅) →
                predprop x′ y′
predeqLemma₂' here
  = pprop₂ (⊑ₙ-intro₃ (NbhSys.⊑-refl Nat))

predeqLemma₂ : {𝑥 : Valuation Γ} → ∀ {y} →
               [ num n ] 𝑥 ↦ y →
               [ ap pred (num (suc n)) ] 𝑥 ↦ y
predeqLemma₂ {y = y} (ideal↦-intro y⊑n)
  = ap↦-intro₂ singletonIsCon singletonIsCon
    pred𝑥↦𝑓 numsn𝑥↦y (NbhSys.⊑-refl (Nat ⇒ Nat))
  where pred𝑥↦𝑓 = pred↦-intro₂ predeqLemma₂'
        numsn𝑥↦y = ideal↦-intro (⊑ₙ-intro₃ y⊑n)

predeq : ∀ {n} → ap {Γ = Γ} pred (num (suc n)) ≈ num n
predeq = ≈-intro (≼-intro predeqLemma₁)
         (≼-intro predeqLemma₂)
