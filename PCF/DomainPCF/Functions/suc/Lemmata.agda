{-# OPTIONS --safe #-}

module PCF.DomainPCF.Functions.suc.Lemmata where

open import Base.Core
open import Base.FinFun
open import NbhSys.Definition
open import NbhSys.Lemmata
open import PCF.DomainPCF.Nat.NbhSys.Definition
open import PCF.DomainPCF.Nat.NbhSys.Instance
open import PCF.DomainPCF.Nat.NbhSys.Lemmata
open import PCF.DomainPCF.Nat.NbhSys.Relation
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Post Nat Nat
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Pre Nat Nat

sucLemma : ∀ {sub preable postable} →
           (∀ {x y} → (x , y) ∈ sub → [ Nat ] y ⊑ sₙ x) →
           [ Nat ] post sub postable ⊑ sₙ (pre sub preable)
sucLemma {∅} _ = ⊑ₙ-intro₁
sucLemma {(x , y) ∷ sub} {pre-cons preable conxpresub}
  {post-cons postable _} p
  = NbhSys.⊑-trans Nat proof₁ proof₂
  where rec = sucLemma λ xy∈sub → p (⊆-lemma₃ xy∈sub)
        proof₁ = ⊑-⊔-lemma₃ Nat _ (conₙ-sₙ conxpresub) (p here) rec
        proof₂ = natLemma₂ {x = x} {y = pre sub preable}
