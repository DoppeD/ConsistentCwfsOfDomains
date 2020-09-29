{-# OPTIONS --safe #-}

open import Base.Core
open import Base.Variables using (n)
open import Scwf.DomainScwf.Appmap.Definition

module Scwf.DomainScwf.ArrowStructure.lam.Consistency
  {𝐴 𝐵 : Ty}
  {Γ : Ctx n}
  (𝑡 : tAppmap (𝐴 :: Γ) [ 𝐵 ]) where

open import Appmap.Lemmata
open import Base.FinFun
open import NbhSys.Definition
open import NbhSys.Lemmata
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Instance
open import Scwf.DomainScwf.Appmap.Valuation.Relation
open import Scwf.DomainScwf.ArrowStructure.lam.Lemmata 𝐴 𝐵 𝑡
open import Scwf.DomainScwf.ArrowStructure.lam.Relation 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.ConFinFun 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Definition 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Instance
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Post 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Pre 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Relation 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.Variables 𝐴 𝐵

record ⊑ₑ-proof₄ (𝑓 𝑓′ : NbhFinFun 𝐴 𝐵) (𝑥 : Valuation Γ) : Set where
  field
    sub : NbhFinFun 𝐴 𝐵
    preablesub : Preable sub
    postablesub : Postable sub
    sub⊆𝑓′ : sub ⊆ 𝑓′
    asd : [ 𝑡 ] ⟪ pre sub preablesub , 𝑥 ⟫ ↦ ⟪ post sub postablesub ⟫

lam↦-con' : ∀ {𝑓 𝑓′ sub 𝑥 𝑥′} →
            (∀ x y → < x , y > ∈ 𝑓 → [ 𝑡 ] ⟪ x , 𝑥 ⟫ ↦ ⟪ y ⟫) →
            (∀ x y → < x , y > ∈ 𝑓′ → [ 𝑡 ] ⟪ x , 𝑥′ ⟫ ↦ ⟪ y ⟫) →
            sub ⊆ (𝑓 ∪ 𝑓′) →
            Preable sub → Postable sub
lam↦-con' {sub = ∅} p₁ p₂ sub⊆∪ preable = post-nil
lam↦-con' {sub = < x , y > ∷ sub} p₁ p₂ sub⊆∪
  (pre-cons preablesub conxpresub)
  = boundedPostable {max = [ 𝐵 ] y ⊔ (post sub rec) [ conypostsub ]} (λ x′y′∈sub → {!!})
  where rec = lam↦-con' p₁ p₂ (⊆-lemma₂ < x , y > sub⊆∪)
              preablesub
        conypostsub = fromValCon (Appmap.↦-con 𝑡 {!!} {!!} {!!})

lam↦-con : ∀ {𝑥 𝑦 𝑥′ 𝑦′} → [ 𝑡 ] 𝑥 lam↦ 𝑦 →
           [ 𝑡 ] 𝑥′ lam↦ 𝑦′ → ValCon _ 𝑥 𝑥′ →
           ValCon _ 𝑦 𝑦′
lam↦-con lam↦-intro₁ lam↦-intro₁ _
  = toValCon conₑ-⊥₂
lam↦-con lam↦-intro₁ (lam↦-intro₂ _ _ _ _) _
  = toValCon conₑ-⊥₂
lam↦-con (lam↦-intro₂ _ _ _ _) lam↦-intro₁ _
  = toValCon conₑ-⊥₁
lam↦-con (lam↦-intro₂ _ 𝑓 con𝑓 p₁) (lam↦-intro₂ _ 𝑓′ con𝑓′ p₂)
  con𝑥𝑥′
  = toValCon con𝑓𝑓′
  where con𝑓𝑓′ = con-∪ _ _ (cff (lam↦-con' p₁ p₂))
