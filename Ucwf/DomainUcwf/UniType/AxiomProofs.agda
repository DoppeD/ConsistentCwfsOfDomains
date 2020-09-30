{-# OPTIONS --safe --sized-types #-}

module Ucwf.DomainUcwf.UniType.AxiomProofs where

open import Base.Core
open import NbhSys.Definition
open import Ucwf.DomainUcwf.UniType.Definition
open import Ucwf.DomainUcwf.UniType.Lemmata
open import Ucwf.DomainUcwf.UniType.Relation
open import Ucwf.DomainUcwf.UniType.SizedFinFun

private
  variable
    x y z : UniNbh

⊑ᵤ-refl' : ∀ 𝑓 x y → < x , y >ₛ ∈ₛ 𝑓 → ⊑ᵤ-proof 𝑓 x y
⊑ᵤ-refl' (< x′ , y′ >ₛ ∷ 𝑓′) x y (there xy∈𝑓)
  = lift⊑ᵤ-proof 𝑓′ (< x′ , y′ >ₛ ∷ 𝑓′) x y
    (λ z z∈𝑓 → there z∈𝑓) (⊑ᵤ-refl' 𝑓′ x y xy∈𝑓)
⊑ᵤ-refl' (_ ∷ 𝑓′) ⊥ᵤ ⊥ᵤ here
  = record { sub = ∅
           ; y⊑ᵤpost = ⊑ᵤ-intro₁
           ; pre⊑ᵤx = ⊑ᵤ-intro₁
           ; sub⊆𝑓′ = ∅-isSubsetₛ
           }
⊑ᵤ-refl' (_ ∷ 𝑓′) ⊥ᵤ (λᵤ 𝑓) here
  = record { sub = < ⊥ᵤ , λᵤ 𝑓 >ₛ ∷ ∅
           ; y⊑ᵤpost = ⊑ᵤ-intro₂ 𝑓 𝑓 (⊑ᵤ-refl' 𝑓)
           ; pre⊑ᵤx = ⊑ᵤ-intro₁
           ; sub⊆𝑓′ = ⊆ₛ-lemma₄ here ∅-isSubsetₛ
           }
⊑ᵤ-refl' (_ ∷ 𝑓′) (λᵤ 𝑓) ⊥ᵤ here
  = record { sub = < λᵤ 𝑓 , ⊥ᵤ >ₛ ∷ ∅
           ; y⊑ᵤpost = ⊑ᵤ-intro₁
           ; pre⊑ᵤx = ⊑ᵤ-intro₂ 𝑓 𝑓 (⊑ᵤ-refl' 𝑓)
           ; sub⊆𝑓′ = ⊆ₛ-lemma₄ here ∅-isSubsetₛ
           }
⊑ᵤ-refl' (_ ∷ 𝑓′) (λᵤ 𝑓) (λᵤ 𝑓″) here
  = record { sub = < λᵤ 𝑓 , λᵤ 𝑓″ >ₛ ∷ ∅
           ; y⊑ᵤpost = ⊑ᵤ-intro₂ 𝑓″ 𝑓″ (⊑ᵤ-refl' 𝑓″)
           ; pre⊑ᵤx = ⊑ᵤ-intro₂ 𝑓 𝑓 (⊑ᵤ-refl' 𝑓)
           ; sub⊆𝑓′ = ⊆ₛ-lemma₄ here ∅-isSubsetₛ
           }

⊑ᵤ-refl : ∀ {x} → x ⊑ᵤ x
⊑ᵤ-refl {⊥ᵤ} = ⊑ᵤ-intro₁
⊑ᵤ-refl {λᵤ 𝑓} = ⊑ᵤ-intro₂ 𝑓 𝑓 (⊑ᵤ-refl' 𝑓)

⊑ᵤ-⊔ᵤ' : ∀ {𝑓 𝑓′ 𝑓″} → λᵤ 𝑓′ ⊑ᵤ λᵤ 𝑓 → λᵤ 𝑓″ ⊑ᵤ λᵤ 𝑓 →
         ∀ x y → < x , y >ₛ ∈ₛ (𝑓′ ∪ₛ 𝑓″) →
         ⊑ᵤ-proof 𝑓 x y
⊑ᵤ-⊔ᵤ' {𝑓′ = 𝑓′} _ _ x y xy∈∪
  with (∪ₛ-lemma₂ {𝑓 = 𝑓′} < x , y >ₛ xy∈∪)
⊑ᵤ-⊔ᵤ' (⊑ᵤ-intro₂ _ _ p) _ x y xy∈∪ | inl xy∈𝑓′
  = record { sub = 𝑓′sub
           ; y⊑ᵤpost = 𝑓′y⊑ᵤpost
           ; pre⊑ᵤx = 𝑓′pre⊑ᵤx
           ; sub⊆𝑓′ = 𝑓′sub⊆𝑓
           }
  where 𝑓′proof = p x y xy∈𝑓′
        𝑓′sub = ⊑ᵤ-proof.sub 𝑓′proof
        𝑓′y⊑ᵤpost = ⊑ᵤ-proof.y⊑ᵤpost 𝑓′proof
        𝑓′pre⊑ᵤx = ⊑ᵤ-proof.pre⊑ᵤx 𝑓′proof
        𝑓′sub⊆𝑓 = ⊑ᵤ-proof.sub⊆𝑓′ 𝑓′proof
⊑ᵤ-⊔ᵤ' _ (⊑ᵤ-intro₂ _ _ p) x y xy∈∪ | inr xy∈𝑓″
  = record { sub = 𝑓″sub
           ; y⊑ᵤpost = 𝑓″y⊑ᵤpost
           ; pre⊑ᵤx = 𝑓″pre⊑ᵤx
           ; sub⊆𝑓′ = 𝑓″sub⊆𝑓
           }
  where 𝑓″proof = p x y xy∈𝑓″
        𝑓″sub = ⊑ᵤ-proof.sub 𝑓″proof
        𝑓″y⊑ᵤpost = ⊑ᵤ-proof.y⊑ᵤpost 𝑓″proof
        𝑓″pre⊑ᵤx = ⊑ᵤ-proof.pre⊑ᵤx 𝑓″proof
        𝑓″sub⊆𝑓 = ⊑ᵤ-proof.sub⊆𝑓′ 𝑓″proof

⊑ᵤ-⊔ᵤ : y ⊑ᵤ x → z ⊑ᵤ x → UniCon y z → (y ⊔ᵤ z [ con-all ]) ⊑ᵤ x
⊑ᵤ-⊔ᵤ {⊥ᵤ} {x} {⊥ᵤ} _ _ _ = ⊑ᵤ-intro₁
⊑ᵤ-⊔ᵤ {λᵤ 𝑓} {x} {⊥ᵤ} y⊑x _ _ = y⊑x
⊑ᵤ-⊔ᵤ {⊥ᵤ} {x} {λᵤ 𝑓} _ z⊑x _ = z⊑x
⊑ᵤ-⊔ᵤ {λᵤ 𝑓′} {λᵤ 𝑓} {λᵤ 𝑓″} y⊑x z⊑x _
  = ⊑ᵤ-intro₂ (𝑓′ ∪ₛ 𝑓″) 𝑓 (⊑ᵤ-⊔ᵤ' y⊑x z⊑x)

⊑ᵤ-⊔ᵤ-helper₁ : ∀ {x} → x ⊑ᵤ (x ⊔ᵤ ⊥ᵤ [ con-all ])
⊑ᵤ-⊔ᵤ-helper₁ {x} rewrite (⊔ᵤ-⊥ᵤ-rightid x)
  = ⊑ᵤ-refl

⊑ᵤ-⊔ᵤ-helper₂ : ∀ {x} →  (x ⊔ᵤ ⊥ᵤ [ con-all ]) ⊑ᵤ x
⊑ᵤ-⊔ᵤ-helper₂ {x} rewrite (⊔ᵤ-⊥ᵤ-rightid x)
  = ⊑ᵤ-refl

⊑ᵤ-⊔ᵤ-fst : ∀ {x y} → UniCon x y → x ⊑ᵤ (x ⊔ᵤ y [ con-all ])
⊑ᵤ-⊔ᵤ-fst {⊥ᵤ} _ = ⊑ᵤ-intro₁
⊑ᵤ-⊔ᵤ-fst {λᵤ 𝑓} {⊥ᵤ} _ = ⊑ᵤ-refl
⊑ᵤ-⊔ᵤ-fst {λᵤ 𝑓} {λᵤ 𝑓′} _
  = ⊑ᵤ-intro₂ 𝑓 (𝑓 ∪ₛ 𝑓′) λ x y xy∈𝑓 →
    record { sub = < x , y >ₛ ∷ ∅
           ; y⊑ᵤpost = ⊑ᵤ-⊔ᵤ-helper₁
           ; pre⊑ᵤx = ⊑ᵤ-⊔ᵤ-helper₂
           ; sub⊆𝑓′ = ⊆ₛ-lemma₄ (∪ₛ-lemma₃ < x , y >ₛ xy∈𝑓)
                      ∅-isSubsetₛ
           }

⊑ᵤ-⊔ᵤ-snd : ∀ {x y} → UniCon x y → y ⊑ᵤ (x ⊔ᵤ y [ con-all ])
⊑ᵤ-⊔ᵤ-snd {y = ⊥ᵤ} _ = ⊑ᵤ-intro₁
⊑ᵤ-⊔ᵤ-snd {⊥ᵤ} {λᵤ 𝑓} _ = ⊑ᵤ-refl
⊑ᵤ-⊔ᵤ-snd {λᵤ 𝑓} {λᵤ 𝑓′} _
  = ⊑ᵤ-intro₂ 𝑓′ (𝑓 ∪ₛ 𝑓′) λ x y xy∈𝑓′ →
    record { sub = < x , y >ₛ ∷ ∅
           ; y⊑ᵤpost = ⊑ᵤ-⊔ᵤ-helper₁
           ; pre⊑ᵤx = ⊑ᵤ-⊔ᵤ-helper₂
           ; sub⊆𝑓′ = ⊆ₛ-lemma₄ (∪ₛ-lemma₄ < x , y >ₛ xy∈𝑓′)
                      ∅-isSubsetₛ
           }
