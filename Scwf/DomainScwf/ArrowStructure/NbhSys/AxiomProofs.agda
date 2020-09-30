{-# OPTIONS --safe #-}

open import Base.Core

module Scwf.DomainScwf.ArrowStructure.NbhSys.AxiomProofs
  (𝐴 𝐵 : Ty) where

open import Base.FinFun
open import NbhSys.Definition
open import NbhSys.Lemmata
open import Scwf.DomainScwf.ArrowStructure.NbhSys.ConFinFun 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Definition 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Post 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Pre 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Relation 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.Variables 𝐴 𝐵

⊑ₑ-refl : ∀ {x} → x ⊑ₑ x
⊑ₑ-refl {⊥ₑ} = ⊑ₑ-intro₁
⊑ₑ-refl {𝐹 𝑓 con𝑓} = ⊑ₑ-intro₂ con𝑓 con𝑓 λ x y xy∈𝑓 →
  record
    { sub = < x , y > ∷ ∅
    ; sub⊆𝑓 = ⊆-lemma₄ xy∈𝑓 ∅-isSubset
    ; preablesub = singletonIsPreable
    ; postablesub = singletonIsPostable
    ; y⊑post = ⊑-⊔-lemma₄ 𝐵 (NbhSys.⊑-refl 𝐵) (con⊥₂ 𝐵)
    ; pre⊑x = NbhSys.⊑-⊔ 𝐴 (NbhSys.⊑-refl 𝐴) (NbhSys.⊑-⊥ 𝐴) (con⊥₂ 𝐴)
    }

⊑ₑ-⊥ₑ : ∀ {x} → ⊥ₑ ⊑ₑ x
⊑ₑ-⊥ₑ = ⊑ₑ-intro₁

⊑ₑ-⊔ₑ' : ∀ {𝑓 𝑓′ 𝑓″ con𝑓 con𝑓′ con𝑓″} →
         𝐹 𝑓′ con𝑓′ ⊑ₑ 𝐹 𝑓 con𝑓 → 𝐹 𝑓″ con𝑓″ ⊑ₑ 𝐹 𝑓 con𝑓 →
         ∀ x y → < x , y > ∈ (𝑓′ ∪ 𝑓″) →
         ⊑ₑ-proof 𝑓 con𝑓 x y
⊑ₑ-⊔ₑ' {𝑓′ = 𝑓′} _ _ x y xy∈∪
  with (∪-lemma₂  {𝑓 = 𝑓′} xy∈∪)
⊑ₑ-⊔ₑ' (⊑ₑ-intro₂ _ _ p) _ x y xy∈∪ | inl xy∈𝑓′
  = p x y xy∈𝑓′
⊑ₑ-⊔ₑ' _ (⊑ₑ-intro₂ _ _ p) x y xy∈∪ | inr xy∈𝑓″
  = p x y xy∈𝑓″

⊑ₑ-⊔ₑ : ∀ {x y z} → y ⊑ₑ x → z ⊑ₑ x → (conyz : ArrCon y z) →
        (y ⊔ₑ z [ conyz ]) ⊑ₑ x
⊑ₑ-⊔ₑ {y = ⊥ₑ} {⊥ₑ} _ _ _ = ⊑ₑ-intro₁
⊑ₑ-⊔ₑ {y = 𝐹 _ _} {⊥ₑ} y⊑x _ _ = y⊑x
⊑ₑ-⊔ₑ {y = ⊥ₑ} {𝐹 _ _} _ z⊑x _ = z⊑x
⊑ₑ-⊔ₑ {x = ArrNbh.𝐹 𝑓 _} {ArrNbh.𝐹 𝑓′ _} {ArrNbh.𝐹 𝑓″ _} y⊑x z⊑x
  (ArrCon.con-∪ _ _ _)
  = ⊑ₑ-intro₂ _ _ (⊑ₑ-⊔ₑ' y⊑x z⊑x)

⊑ₑ-⊔ₑ-fst : ∀ {x y} → (conxy : ArrCon x y) → x ⊑ₑ (x ⊔ₑ y [ conxy ])
⊑ₑ-⊔ₑ-fst {⊥ₑ} _ = ⊑ₑ-intro₁
⊑ₑ-⊔ₑ-fst {𝐹 𝑓 _} {⊥ₑ} _ = ⊑ₑ-refl
⊑ₑ-⊔ₑ-fst {𝐹 𝑓 _} {𝐹 𝑓′ _} (ArrCon.con-∪ _ _ _)
  = ⊑ₑ-intro₂ _ _ λ x y xy∈𝑓 →
  record
    { sub = < x , y > ∷ ∅
    ; sub⊆𝑓 = ⊆-lemma₄ (∪-lemma₃ xy∈𝑓) ∅-isSubset
    ; preablesub = singletonIsPreable
    ; postablesub = singletonIsPostable
    ; y⊑post = ⊑-⊔-lemma₄ 𝐵 (NbhSys.⊑-refl 𝐵) (con⊥₂ 𝐵)
    ; pre⊑x = NbhSys.⊑-⊔ 𝐴 (NbhSys.⊑-refl 𝐴) (NbhSys.⊑-⊥ 𝐴)
              (con⊥₂ 𝐴)
    }

⊑ₑ-⊔ₑ-snd : ∀ {x y} → (conxy : ArrCon x y) → y ⊑ₑ (x ⊔ₑ y [ conxy ])
⊑ₑ-⊔ₑ-snd {y = ⊥ₑ} _ = ⊑ₑ-intro₁
⊑ₑ-⊔ₑ-snd {⊥ₑ} {𝐹 𝑓 _} _ = ⊑ₑ-refl
⊑ₑ-⊔ₑ-snd {𝐹 𝑓 _} {𝐹 𝑓′ _} (ArrCon.con-∪ _ _ _)
  = ⊑ₑ-intro₂ _ _ λ x y xy∈𝑓′ →
  record
    { sub = < x , y > ∷ ∅
    ; sub⊆𝑓 = ⊆-lemma₄ (∪-lemma₄ xy∈𝑓′) ∅-isSubset
    ; preablesub = singletonIsPreable
    ; postablesub = singletonIsPostable
    ; y⊑post = ⊑-⊔-lemma₄ 𝐵 (NbhSys.⊑-refl 𝐵) (con⊥₂ 𝐵)
    ; pre⊑x = NbhSys.⊑-⊔ 𝐴 (NbhSys.⊑-refl 𝐴) (NbhSys.⊑-⊥ 𝐴)
              (con⊥₂ 𝐴)
    }
