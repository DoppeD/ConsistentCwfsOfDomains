{-# OPTIONS --safe #-}

open import Base.Core
open import Base.Variables using (n)
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Instance
open import Scwf.DomainScwf.Appmap.Definition

module Scwf.DomainScwf.ArrowStructure.ap.Consistency
  {Γ : Ctx n}
  {𝐴 𝐵 : Ty}
  (𝑡 : tAppmap Γ [ ArrNbhSys 𝐴 𝐵 ])
  (𝑢 : tAppmap Γ [ 𝐴 ])
  where

open import Base.FinFun
open import NbhSys.Definition
open import NbhSys.Lemmata
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Instance
open import Scwf.DomainScwf.Appmap.Valuation.Relation
open import Scwf.DomainScwf.ArrowStructure.ap.Relation 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Definition 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.ConFinFun 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Post 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Pre 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Relation 𝐴 𝐵

ap↦-con : ∀ {𝑥 𝑦 𝑥′ 𝑦′} → [ 𝑡 , 𝑢 ] 𝑥 ap↦ 𝑦 →
          [ 𝑡 , 𝑢 ] 𝑥′ ap↦ 𝑦′ → ValCon _ 𝑥 𝑥′ →
          ValCon _ 𝑦 𝑦′
ap↦-con {𝑦′ = ⟪ y' , ⟪⟫ ⟫} (ap↦-intro₁ y⊑⊥) ap𝑥′↦𝑦′ _
  = NbhSys.Con-⊔ (ValNbhSys [ 𝐵 ]) 𝑦⊑𝑦′ 𝑦′⊑𝑦′
  where 𝑦′⊑𝑦′ = NbhSys.⊑-refl (ValNbhSys _)
        y⊑y′ = NbhSys.⊑-trans 𝐵 y⊑⊥ (NbhSys.⊑-⊥ 𝐵)
        𝑦⊑𝑦′ = ⊑ᵥ-cons _ y⊑y′ ⊑ᵥ-nil
ap↦-con (ap↦-intro₂ _ _ _ _ _) (ap↦-intro₁ y′⊑⊥) _
  = NbhSys.Con-⊔ (ValNbhSys [ 𝐵 ]) 𝑦⊑𝑦 𝑦′⊑𝑦
  where 𝑦⊑𝑦 = NbhSys.⊑-refl (ValNbhSys _)
        y′⊑y = NbhSys.⊑-trans 𝐵 y′⊑⊥ (NbhSys.⊑-⊥ 𝐵)
        𝑦′⊑𝑦 = ⊑ᵥ-cons _ y′⊑y ⊑ᵥ-nil
ap↦-con
  (ap↦-intro₂ {x} {y} con𝑓 conxy 𝑡𝑥↦𝑓 𝑢𝑥↦x
  (⊑ₑ-intro₂ _ _ p₁))
  (ap↦-intro₂ {x′} {y′} con𝑓′ conx′y′ 𝑡𝑥′↦𝑓′ 𝑢𝑥′↦x′
  (⊑ₑ-intro₂ _ _ p₂))
  con𝑥𝑥′
  with (fromValCon (Appmap.↦-con 𝑡 𝑡𝑥↦𝑓 𝑡𝑥′↦𝑓′ con𝑥𝑥′))
... | con-∪ _ _ (cff p) = toValCon conyy′
  where p₁proof = p₁ here
        p₂proof = p₂ here
        p₁sub = ⊑ₑ-proof.sub p₁proof
        p₂sub = ⊑ₑ-proof.sub p₂proof
        p₁sub⊆𝑓 = ⊑ₑ-proof.sub⊆𝑓 p₁proof
        p₂sub⊆𝑓 = ⊑ₑ-proof.sub⊆𝑓 p₂proof
        p₁y⊑post = ⊑ₑ-proof.y⊑post p₁proof
        p₂y⊑post = ⊑ₑ-proof.y⊑post p₂proof
        p₁pre⊑x = ⊑ₑ-proof.pre⊑x p₁proof
        p₂pre⊑x = ⊑ₑ-proof.pre⊑x p₂proof
        p₁postable = ⊑ₑ-proof.postablesub p₁proof
        p₂postable = ⊑ₑ-proof.postablesub p₂proof
        p₁preable = ⊑ₑ-proof.preablesub p₁proof
        p₂preable = ⊑ₑ-proof.preablesub p₂proof
        conxx′ = fromValCon (Appmap.↦-con 𝑢 𝑢𝑥↦x 𝑢𝑥′↦x′ con𝑥𝑥′)
        p₁pre⊑x⊔x′ = ⊑-⊔-lemma₄ 𝐴 p₁pre⊑x conxx′
        p₂pre⊑x⊔x′ = ⊑-⊔-lemma₅ 𝐴 p₂pre⊑x conxx′
        preable∪ = preUnionLemma p₁preable p₂preable
                   p₁pre⊑x⊔x′ p₂pre⊑x⊔x′
        postable∪ = p (∪-lemma₅ p₁sub⊆𝑓 p₂sub⊆𝑓) preable∪
        y⊑post∪ = NbhSys.⊑-trans 𝐵 p₁y⊑post
                  (postLemma₁ {postable𝑓 = p₁postable})
        y′⊑post∪ = NbhSys.⊑-trans 𝐵 p₂y⊑post
                   (postLemma₂ {postable𝑓′ = p₂postable}
                   {postable∪})
        conyy′ = NbhSys.Con-⊔ 𝐵 y⊑post∪ y′⊑post∪
