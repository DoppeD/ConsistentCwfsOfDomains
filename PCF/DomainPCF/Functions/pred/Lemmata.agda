{-# OPTIONS --safe #-}

module PCF.DomainPCF.Functions.pred.Lemmata where

open import Base.Core
open import Base.FinFun
open import NbhSys.Definition
open import NbhSys.Lemmata
open import PCF.DomainPCF.Functions.pred.Relation
open import PCF.DomainPCF.Nat.NbhSys.Definition
open import PCF.DomainPCF.Nat.NbhSys.Instance
open import PCF.DomainPCF.Nat.NbhSys.Relation
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Post Nat Nat
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Pre Nat Nat

predLemma' : ∀ {x y x′ y′} → predprop x y →
             predprop x′ y′ → ∀ conxx′ conyy′ →
             predprop (x ⊔ₙ x′ [ conxx′ ]) (y ⊔ₙ y′ [ conyy′ ])
predLemma' (pprop₁ x⊑0 y⊑⊥) (pprop₁ x′⊑0 y′⊑⊥) conxx′ conyy′
  = pprop₁ x⊔x′⊑0 y⊔y′⊑⊥
  where x⊔x′⊑0 = NbhSys.⊑-⊔ Nat x⊑0 x′⊑0 conxx′
        y⊔y′⊑⊥ = NbhSys.⊑-⊔ Nat y⊑⊥ y′⊑⊥ conyy′
predLemma' (pprop₁ ⊑ₙ-intro₁ ⊑ₙ-intro₁)
  (pprop₂ (⊑ₙ-intro₃ y′⊑y)) conₙ-bot₁ conyy′
  = pprop₂ (⊑ₙ-intro₃ (⊥⊔y′⊑y))
  where ⊥⊔y′⊑y = NbhSys.⊑-⊔ Nat (NbhSys.⊑-⊥ Nat) y′⊑y conyy′
predLemma' (pprop₂ (⊑ₙ-intro₃ y⊑x))
  (pprop₁ _ ⊑ₙ-intro₁) conₙ-bot₂ conyy′
  = pprop₂ (⊑ₙ-intro₃ y⊔⊥⊑x)
  where y⊔⊥⊑x = NbhSys.⊑-⊔ Nat y⊑x (NbhSys.⊑-⊥ Nat) conyy′
predLemma' (pprop₂ (⊑ₙ-intro₃ y⊑x))
  (pprop₂ (⊑ₙ-intro₃ y′⊑x′)) (conₙ-sₙ conxx′) conyy′
  = pprop₂ (⊑ₙ-intro₃ y⊔y′⊑x⊔x′)
  where y⊔y′⊑x⊔x′ = ⊑-⊔-lemma₃ Nat conyy′ conxx′ y⊑x y′⊑x′

predLemma : ∀ {sub preable postable} →
            (∀ {x y} → (x , y) ∈ sub → predprop x y) →
            predprop (pre sub preable) (post sub postable)
predLemma {∅} _ = pprop₁ ⊑ₙ-intro₁ ⊑ₙ-intro₁
predLemma {_ ∷ _} {pre-cons _ conxpresub}
  {post-cons _ conypostsub} p
  = predLemma' ppxy ppprepost conxpresub conypostsub
  where ppxy = p here
        ppprepost = predLemma (λ xy∈sub → p (there xy∈sub))
