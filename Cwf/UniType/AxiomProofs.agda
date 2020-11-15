module Cwf.UniType.AxiomProofs where

open import Base.Core
open import Base.FinFun
open import Cwf.UniType.Definition
open import Cwf.UniType.Lemmata
open import Cwf.UniType.PrePost
open import Cwf.UniType.Relation

liftλ-proof : ∀ {i} → {𝑓 𝑓′ : FinFun (Nbh {i}) (Nbh {i})} →
              ∀ {con𝑓 con𝑓′ x y} → 𝑓 ⊆ 𝑓′ →
              λ-proof 𝑓 con𝑓 x y → λ-proof {i} 𝑓′ con𝑓′ x y
liftλ-proof 𝑓⊆𝑓′
  record
      { sub = sub
      ; sub⊆𝑓 = sub⊆𝑓
      ; preablesub = preablesub
      ; postablesub = postablesub
      ; y⊑post = y⊑post
      ; pre⊑x = pre⊑x
      }
  = record
      { sub = sub
      ; sub⊆𝑓 = ⊆-trans sub⊆𝑓 𝑓⊆𝑓′
      ; preablesub = preablesub
      ; postablesub = postablesub
      ; y⊑post = y⊑post
      ; pre⊑x = pre⊑x
      }

⊑ᵤ-refl : ∀ {i} → {x : Nbh {i}} → x ⊑ᵤ x
⊑ᵤ-refl' : ∀ {i} → {𝑓 : FinFun (Nbh {i}) (Nbh {i})} →
           ∀ {con𝑓 x y} → (x , y) ∈ 𝑓 → λ-proof 𝑓 con𝑓 x y

⊑ᵤ-refl' {x = x} {y} here
  = record
      { sub = (x , y) ∷ ∅
      ; sub⊆𝑓 = ⊆-lemma₁ ⊆-refl
      ; preablesub = pre-cons pre-nil con-⊥₂
      ; postablesub = post-cons post-nil con-⊥₂
      ; y⊑post = ⊑ᵤ-refl
      ; pre⊑x = ⊑ᵤ-refl
      }
⊑ᵤ-refl' {con𝑓 = conxy𝑓} (there xy∈𝑓)
  = liftλ-proof {con𝑓 = con𝑓} ⊆-lemma₃ (⊑ᵤ-refl' xy∈𝑓)
  where con𝑓 = subsetIsCon ⊆-lemma₃ conxy𝑓

⊑ᵤ-refl {x = ⊥} = ⊑ᵤ-bot
⊑ᵤ-refl {x = 0ₙ} = ⊑ᵤ-refl-0
⊑ᵤ-refl {x = sᵤ _} = ⊑ᵤ-s ⊑ᵤ-refl
⊑ᵤ-refl {x = ℕ} = ⊑ᵤ-refl-ℕ
⊑ᵤ-refl {x = 𝒰} = ⊑ᵤ-refl-𝒰
⊑ᵤ-refl {x = λᵤ _ _} = ⊑ᵤ-λ ⊑ᵤ-refl'
⊑ᵤ-refl {x = Π _ _ _} = ⊑ᵤ-Π ⊑ᵤ-refl ⊑ᵤ-refl

⊥-leftId₁ : ∀ {x y} → x ⊑ᵤ y → (⊥ ⊔ᵤ x [ con-⊥₁ ]) ⊑ᵤ y
⊥-leftId₁ {⊥} x⊑y = x⊑y
⊥-leftId₁ {0ₙ} x⊑y = x⊑y
⊥-leftId₁ {sᵤ x} x⊑y = x⊑y
⊥-leftId₁ {ℕ} x⊑y = x⊑y
⊥-leftId₁ {𝒰} x⊑y = x⊑y
⊥-leftId₁ {λᵤ 𝑓 x} x⊑y = x⊑y
⊥-leftId₁ {Π x 𝑓 x₁} x⊑y = x⊑y

⊥-leftId₂ : ∀ {x y} → x ⊑ᵤ y → x ⊑ᵤ (⊥ ⊔ᵤ y [ con-⊥₁ ])
⊥-leftId₂ {y = ⊥} x⊑y = x⊑y
⊥-leftId₂ {y = 0ₙ} x⊑y = x⊑y
⊥-leftId₂ {y = sᵤ _} x⊑y = x⊑y
⊥-leftId₂ {y = ℕ} x⊑y = x⊑y
⊥-leftId₂ {y = 𝒰} x⊑y = x⊑y
⊥-leftId₂ {y = λᵤ _ _} x⊑y = x⊑y
⊥-leftId₂ {y = Π _ _ _} x⊑y = x⊑y

⊑ᵤ-⊥ : ∀ {x} → ⊥ ⊑ᵤ x
⊑ᵤ-⊥ = ⊑ᵤ-bot

⊑ᵤ-⊔' : ∀ {𝑓 𝑓′ con𝑓 con𝑓′ con∪} →
        ({x y : Nbh} → (x , y) ∈ 𝑓 → λ-proof 𝑓 con𝑓 x y) →
        ({x y : Nbh} → (x , y) ∈ 𝑓′ → λ-proof 𝑓′ con𝑓′ x y) →
        {x y : Nbh} → (x , y) ∈ (𝑓 ∪ 𝑓′) → λ-proof (𝑓 ∪ 𝑓′) con∪ x y
⊑ᵤ-⊔' {𝑓} p₁ p₂ xy∈∪ with (∪-lemma₂ {𝑓 = 𝑓} xy∈∪)
... | inl xy∈𝑓 = liftλ-proof ∪-lemma₆ (p₁ xy∈𝑓)
... | inr xy∈𝑓′ = liftλ-proof ∪-lemma₇ (p₂ xy∈𝑓′)

⊑ᵤ-⊔ : ∀ {x y z} → y ⊑ᵤ x → z ⊑ᵤ x → (con : Con y z) →
      (y ⊔ᵤ z [ con ]) ⊑ᵤ x
⊑ᵤ-⊔ _ z⊑x con-⊥₁ = ⊥-leftId₁ z⊑x
⊑ᵤ-⊔ y⊑x _ con-⊥₂ = y⊑x
⊑ᵤ-⊔ y⊑x z⊑x con-refl-0 = y⊑x
⊑ᵤ-⊔ (⊑ᵤ-s y⊑x) (⊑ᵤ-s z⊑x) (con-s con)
  = ⊑ᵤ-s (⊑ᵤ-⊔ y⊑x z⊑x con)
⊑ᵤ-⊔ y⊑x _ con-refl-ℕ = y⊑x
⊑ᵤ-⊔ y⊑x _ con-refl-𝒰 = y⊑x
⊑ᵤ-⊔ (⊑ᵤ-λ p₁) (⊑ᵤ-λ p₂) (con-λ _)
  = ⊑ᵤ-λ (⊑ᵤ-⊔' p₁ p₂)
⊑ᵤ-⊔ (⊑ᵤ-Π y⊑x (⊑ᵤ-λ p₁)) (⊑ᵤ-Π z⊑x (⊑ᵤ-λ p₂)) (con-Π _ _)
  = ⊑ᵤ-Π (⊑ᵤ-⊔ y⊑x z⊑x _) (⊑ᵤ-λ (⊑ᵤ-⊔' p₁ p₂))

⊑ᵤ-⊔-fst : ∀ {x y} → ∀ conxy → x ⊑ᵤ (x ⊔ᵤ y [ conxy ])
⊑ᵤ-⊔-fst con-⊥₁ = ⊑ᵤ-bot
⊑ᵤ-⊔-fst con-⊥₂ = ⊑ᵤ-refl
⊑ᵤ-⊔-fst con-refl-0 = ⊑ᵤ-refl-0
⊑ᵤ-⊔-fst (con-s conxy) = ⊑ᵤ-s (⊑ᵤ-⊔-fst conxy)
⊑ᵤ-⊔-fst con-refl-ℕ = ⊑ᵤ-refl-ℕ
⊑ᵤ-⊔-fst con-refl-𝒰 = ⊑ᵤ-refl-𝒰
⊑ᵤ-⊔-fst (con-λ x) = ⊑ᵤ-λ ⊑ᵤ-refl'
⊑ᵤ-⊔-fst (con-Π conxy con𝑓∪𝑔)
  = ⊑ᵤ-Π (⊑ᵤ-⊔-fst conxy) (⊑ᵤ-λ ⊑ᵤ-refl')

⊑ᵤ-⊔-snd : ∀ {x y} → ∀ conxy → y ⊑ᵤ (x ⊔ᵤ y [ conxy ])
⊑ᵤ-⊔-snd con-⊥₁ = ⊥-leftId₂ ⊑ᵤ-refl
⊑ᵤ-⊔-snd con-⊥₂ = ⊑ᵤ-bot
⊑ᵤ-⊔-snd con-refl-0 = ⊑ᵤ-refl-0
⊑ᵤ-⊔-snd (con-s conxy) = ⊑ᵤ-s (⊑ᵤ-⊔-snd conxy)
⊑ᵤ-⊔-snd con-refl-ℕ = ⊑ᵤ-refl-ℕ
⊑ᵤ-⊔-snd con-refl-𝒰 = ⊑ᵤ-refl-𝒰
⊑ᵤ-⊔-snd (con-λ x) = ⊑ᵤ-λ ⊑ᵤ-refl'
⊑ᵤ-⊔-snd (con-Π conxy con𝑓∪𝑔)
  = ⊑ᵤ-Π (⊑ᵤ-⊔-snd conxy) (⊑ᵤ-λ ⊑ᵤ-refl')
