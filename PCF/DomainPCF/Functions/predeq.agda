{-# OPTIONS --safe #-}

module PCF.DomainPCF.Functions.predeq where

open import Appmap.Definition
open import Appmap.Equivalence
open import Appmap.PrincipalIdeal.Relation
open import Base.Core
open import Base.FinFun
open import Base.Variables
open import NbhSys.Definition
open import NbhSys.Lemmata
open import PCF.DomainPCF.Functions.pred.Instance
open import PCF.DomainPCF.Functions.pred.Lemmata
open import PCF.DomainPCF.Functions.pred.Relation
open import PCF.DomainPCF.Functions.suc.Instance
open import PCF.DomainPCF.Functions.suc.Lemmata
open import PCF.DomainPCF.Functions.suc.Relation
open import PCF.DomainPCF.Nat.NbhSys.Definition
open import PCF.DomainPCF.Nat.NbhSys.Instance
open import PCF.DomainPCF.Nat.NbhSys.Lemmata
open import PCF.DomainPCF.Nat.NbhSys.Relation
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.ArrowStructure.ap.Instance
open import Scwf.DomainScwf.ArrowStructure.ap.Relation
open import Scwf.DomainScwf.ArrowStructure.NbhSys.ConFinFun Nat Nat
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Definition Nat Nat
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Instance
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Post Nat Nat
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Pre Nat Nat
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Relation Nat Nat

predeqLemma₁'' : ∀ {𝑥 : Valuation Γ} → ∀ {𝑓 con𝑓 x y conxy} →
                 [ suc ] 𝑥 ↦ 𝐹 𝑓 con𝑓 →
                 [ Nat ⇒ Nat ] 𝐹 ((x , y) ∷ ∅) conxy
                   ⊑ 𝐹 𝑓 con𝑓 →
                 [ Nat ] y ⊑ sₙ x
predeqLemma₁'' _ (⊑ₑ-intro₂ _ _ p) with (p here)
predeqLemma₁'' (suc↦-intro₂ p) _
  | record { sub = sub
           ; sub⊆𝑓 = sub⊆𝑓
           ; preablesub = preable
           ; postablesub = postable
           }
  with (sucLemma {sub} {preable} {postable}
        λ xy∈sub → p (sub⊆𝑓 xy∈sub))
predeqLemma₁'' _ _
  | record { y⊑post = y⊑post
           ; pre⊑x = pre⊑x
           }
  | post⊑spre
  = NbhSys.⊑-trans Nat y⊑post post⊑sx
  where spre⊑sx = ⊑ₙ-intro₃ pre⊑x
        post⊑sx = NbhSys.⊑-trans Nat post⊑spre spre⊑sx

predeqLemma₁' : ∀ {x} → [ Nat ] sₙ x ⊑ ⊥ₙ →
                [ Nat ] x ⊑ ⊥ₙ
predeqLemma₁' ()

predeqLemma₁ : ∀ {n} → {𝑥 : Valuation Γ} → ∀ {y} →
               [ ap pred (ap suc n) ] 𝑥 ↦ y →
               [ n ] 𝑥 ↦ y
predeqLemma₁ {n = n} (ap↦-intro₁ ⊑ₙ-intro₁)
  = Appmap.↦-bottom n
predeqLemma₁ (ap↦-intro₂ _ _ _ _ (⊑ₑ-intro₂ _ _ p))
  with (p here)
predeqLemma₁ (ap↦-intro₂ _ _ (pred↦-intro₂ p) _ _)
  | record { sub = sub
           ; sub⊆𝑓 = sub⊆𝑓
           ; preablesub = preable
           ; postablesub = postable
           }
  with (predLemma {sub} {preable} {postable}
       (λ xy∈sub → (p (sub⊆𝑓 xy∈sub))))
predeqLemma₁ {n = n} (ap↦-intro₂ _ _ (pred↦-intro₂ p) apsucn𝑥↦y′ _)
  | record { y⊑post = y⊑post }
  | pprop₁ pre⊑0 post⊑⊥
  = Appmap.↦-↓closed n y⊑⊥ (Appmap.↦-bottom n)
  where y⊑⊥ = NbhSys.⊑-trans Nat y⊑post post⊑⊥
predeqLemma₁ {n = n} (ap↦-intro₂ _ _ (pred↦-intro₂ p) (ap↦-intro₁ x⊑⊥) _)
  | record { y⊑post = y⊑post
           ; pre⊑x = pre⊑x
           }
  | pprop₂ spost⊑pre
  = Appmap.↦-↓closed n y⊑⊥ (Appmap.↦-bottom n)
  where pre⊑⊥ = NbhSys.⊑-trans Nat pre⊑x x⊑⊥
        spost⊑⊥ = NbhSys.⊑-trans Nat spost⊑pre pre⊑⊥
        sy⊑⊥ = NbhSys.⊑-trans Nat (⊑ₙ-intro₃ y⊑post) spost⊑⊥
        y⊑⊥ = predeqLemma₁' sy⊑⊥
predeqLemma₁ {n = n} (ap↦-intro₂ _ _ (pred↦-intro₂ p)
  (ap↦-intro₂ {x = y′} {𝑓 = 𝑓} _ _ suc𝑥↦𝑓 n𝑥↦y′ y′x⊑𝑓) _)
  | record { y⊑post = y⊑post
           ; pre⊑x = pre⊑x
           }
  | pprop₂ spost⊑pre
  = Appmap.↦-↓closed n y⊑y′ n𝑥↦y′
  where x⊑sy′ = predeqLemma₁'' suc𝑥↦𝑓 y′x⊑𝑓
        pre⊑sy′ = NbhSys.⊑-trans Nat pre⊑x x⊑sy′
        post⊑sy′ = NbhSys.⊑-trans Nat spost⊑pre pre⊑sy′
        sy⊑sy′ = NbhSys.⊑-trans Nat (⊑ₙ-intro₃ y⊑post)
                 post⊑sy′
        y⊑y′ = natLemma₄ sy⊑sy′

predeqLemma₂'' : ∀ {y x′ y′} →
                 (x′ , y′) ∈ ((y , sₙ y) ∷ ∅) →
                 [ Nat ] y′ ⊑ sₙ x′
predeqLemma₂'' here
  = ⊑ₙ-intro₃ (NbhSys.⊑-refl Nat)

predeqLemma₂' : ∀ {y x′ y′} →
                (x′ , y′) ∈ ((sₙ y , y) ∷ ∅) →
                predprop x′ y′
predeqLemma₂' here
  = pprop₂ (⊑ₙ-intro₃ (NbhSys.⊑-refl Nat))

predeqLemma₂ : ∀ {n} → {𝑥 : Valuation Γ} → ∀ {y} →
               [ n ] 𝑥 ↦ y →
               [ ap pred (ap suc n) ] 𝑥 ↦ y
predeqLemma₂ {y = n} n𝑥↦y
  = ap↦-intro₂ {x = sₙ n} {𝑓 = ((sₙ n , n) ∷ ∅)} singletonIsCon
    singletonIsCon pred𝑥↦sₙn apsucn𝑥↦sₙn (NbhSys.⊑-refl (Nat ⇒ Nat))
  where pred𝑥↦sₙn = pred↦-intro₂ predeqLemma₂'
        suc𝑥↦nsₙ = suc↦-intro₂ predeqLemma₂''
        apsucn𝑥↦sₙn = ap↦-intro₂ {𝑓 = ((n , sₙ n) ∷ ∅)}
                      singletonIsCon singletonIsCon suc𝑥↦nsₙ
                      n𝑥↦y (NbhSys.⊑-refl (Nat ⇒ Nat))

predeq : ∀ {n} → ap {Γ = Γ} pred (ap suc n) ≈ n
predeq = ≈-intro (≼-intro predeqLemma₁)
         (≼-intro predeqLemma₂)
