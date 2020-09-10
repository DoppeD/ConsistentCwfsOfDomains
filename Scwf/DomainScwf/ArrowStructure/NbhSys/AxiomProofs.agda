{-# OPTIONS --safe #-}

open import Base.Core

module Scwf.DomainScwf.ArrowStructure.NbhSys.AxiomProofs
  (𝐴 𝐵 : Ty) where

open import Base.FinFun
open import NbhSys.Definition
open import NbhSys.Lemmata
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Definition 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Relation 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.Variables 𝐴 𝐵

⊑ₑ-refl : ∀ {x} → x ⊑ₑ x
⊑ₑ-refl {⊥ₑ} = ⊑ₑ-intro₁
⊑ₑ-refl {𝐹 𝑓} = ⊑ₑ-intro₂ 𝑓 𝑓 (λ x y xy∈𝑓 →
  record { sub = < x , y > ∷ ∅
         ; y⊑post = ⊑-⊔-lemma₄ 𝐵 (NbhSys.⊑-refl 𝐵)
         ; pre⊑x = NbhSys.⊑-⊔ 𝐴 (NbhSys.⊑-refl 𝐴) (NbhSys.⊑-⊥ 𝐴)
         ; sub⊆𝑓 = ⊆-lemma₄ < x , y > xy∈𝑓 ∅-isSubset
         })

⊑ₑ-⊥ₑ : ∀ {x} → ⊥ₑ ⊑ₑ x
⊑ₑ-⊥ₑ = ⊑ₑ-intro₁

⊑ₑ-⊔ₑ' : ∀ {𝑓 𝑓′ 𝑓″} → 𝐹 𝑓′ ⊑ₑ 𝐹 𝑓 → 𝐹 𝑓″ ⊑ₑ 𝐹 𝑓 →
         ∀ x y → < x , y > ∈ (𝑓′ ∪ 𝑓″) →
         ⊑ₑ-proof 𝑓 x y
⊑ₑ-⊔ₑ' {𝑓′ = 𝑓′} {𝑓″} _ _ x y xy∈∪
  with (∪-lemma₂ {𝑓 = 𝑓′} < x , y > xy∈∪)
⊑ₑ-⊔ₑ' (⊑ₑ-intro₂ _ _ p) _ x y xy∈∪ | inl xy∈𝑓′
  = record { sub = 𝑓′sub
           ; y⊑post = 𝑓′y⊑ₑpost
           ; pre⊑x = 𝑓′pre⊑ₑx
           ; sub⊆𝑓 = 𝑓′sub⊆𝑓
           }
  where 𝑓′proof = p x y xy∈𝑓′
        𝑓′sub = ⊑ₑ-proof.sub 𝑓′proof
        𝑓′y⊑ₑpost = ⊑ₑ-proof.y⊑post 𝑓′proof
        𝑓′pre⊑ₑx = ⊑ₑ-proof.pre⊑x 𝑓′proof
        𝑓′sub⊆𝑓 = ⊑ₑ-proof.sub⊆𝑓 𝑓′proof
⊑ₑ-⊔ₑ' _ (⊑ₑ-intro₂ _ _ p) x y xy∈∪ | inr xy∈𝑓″
  = record { sub = 𝑓″sub
           ; y⊑post = 𝑓″y⊑ₑpost
           ; pre⊑x = 𝑓″pre⊑ₑx
           ; sub⊆𝑓 = 𝑓″sub⊆𝑓
           }
  where 𝑓″proof = p x y xy∈𝑓″
        𝑓″sub = ⊑ₑ-proof.sub 𝑓″proof
        𝑓″y⊑ₑpost = ⊑ₑ-proof.y⊑post 𝑓″proof
        𝑓″pre⊑ₑx = ⊑ₑ-proof.pre⊑x 𝑓″proof
        𝑓″sub⊆𝑓 = ⊑ₑ-proof.sub⊆𝑓 𝑓″proof


⊑ₑ-⊔ₑ : ∀ {x y z} → y ⊑ₑ x → z ⊑ₑ x → (y ⊔ₑ z) ⊑ₑ x
⊑ₑ-⊔ₑ {y = ⊥ₑ} {⊥ₑ} _ _ = ⊑ₑ-intro₁
⊑ₑ-⊔ₑ {y = 𝐹 𝑓} {⊥ₑ} y⊑x _ = y⊑x
⊑ₑ-⊔ₑ {y = ⊥ₑ} {𝐹 𝑓} _ z⊑x = z⊑x
⊑ₑ-⊔ₑ {x = 𝐹 𝑓} {𝐹 𝑓′} {𝐹 𝑓″} y⊑x z⊑x
  = ⊑ₑ-intro₂ (𝑓′ ∪ 𝑓″) 𝑓 (⊑ₑ-⊔ₑ' y⊑x z⊑x)

⊑ₑ-⊔ₑ-fst : ∀ {x y} → x ⊑ₑ (x ⊔ₑ y)
⊑ₑ-⊔ₑ-fst {⊥ₑ} = ⊑ₑ-intro₁
⊑ₑ-⊔ₑ-fst {𝐹 𝑓} {⊥ₑ} = ⊑ₑ-refl
⊑ₑ-⊔ₑ-fst {𝐹 𝑓} {𝐹 𝑓′}
  = ⊑ₑ-intro₂ 𝑓 (𝑓 ∪ 𝑓′) λ x y xy∈𝑓 →
    record { sub = < x , y > ∷ ∅
           ; y⊑post = ⊑-⊔-lemma₄ 𝐵 (NbhSys.⊑-refl 𝐵)
           ; pre⊑x = NbhSys.⊑-⊔ 𝐴 (NbhSys.⊑-refl 𝐴) (NbhSys.⊑-⊥ 𝐴)
           ; sub⊆𝑓 = ⊆-lemma₄ < x , y > (∪-lemma₃ < x , y > xy∈𝑓)
                     ∅-isSubset
           }

⊑ₑ-⊔ₑ-snd : ∀ {x y} → y ⊑ₑ (x ⊔ₑ y)
⊑ₑ-⊔ₑ-snd {y = ⊥ₑ} = ⊑ₑ-intro₁
⊑ₑ-⊔ₑ-snd {⊥ₑ} {𝐹 𝑓}  = ⊑ₑ-refl
⊑ₑ-⊔ₑ-snd {𝐹 𝑓} {𝐹 𝑓′}
  = ⊑ₑ-intro₂ 𝑓′ (𝑓 ∪ 𝑓′) λ x y xy∈𝑓′ →
    record { sub = < x , y > ∷ ∅
           ; y⊑post = ⊑-⊔-lemma₄ 𝐵 (NbhSys.⊑-refl 𝐵)
           ; pre⊑x = NbhSys.⊑-⊔ 𝐴 (NbhSys.⊑-refl 𝐴) (NbhSys.⊑-⊥ 𝐴)
           ; sub⊆𝑓 = ⊆-lemma₄ < x , y > (∪-lemma₄ < x , y > xy∈𝑓′)
                     ∅-isSubset
           }
