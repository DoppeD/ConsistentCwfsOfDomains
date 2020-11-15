module Cwf.UniType.AxiomProofs where

open import Base.Core
open import Base.FinFun
open import Cwf.UniType.Definition
open import Cwf.UniType.PrePost
open import Cwf.UniType.Relation

liftλ-proof : ∀ {𝑓 𝑓′ con𝑓 con𝑓′ x y} → 𝑓 ⊆ 𝑓′ →
              λ-proof 𝑓 con𝑓 x y → λ-proof 𝑓′ con𝑓′ x y
liftλ-proof = {!!}

⊑ᵤ-refl' : ∀ {𝑓 con𝑓 x y} → (x , y) ∈ 𝑓 → λ-proof 𝑓 con𝑓 x y
⊑ᵤ-refl' {x = x} {y} here
  = record
      { sub = (x , y) ∷ ∅
      ; sub⊆𝑓 = ⊆-lemma₁ ⊆-refl
      ; preablesub = pre-cons pre-nil con-⊥₂
      ; postablesub = post-cons post-nil con-⊥₂
      ; y⊑post = {!!}
      ; pre⊑x = {!!}
      }
⊑ᵤ-refl' {con𝑓 = conxy𝑓} (there xy∈𝑓)
  = liftλ-proof {con𝑓 = con𝑓} ⊆-lemma₃ (⊑ᵤ-refl' xy∈𝑓)
  where con𝑓 = subsetIsCon ⊆-lemma₃ conxy𝑓

⊑ᵤ-refl : ∀ {x} → x ⊑ᵤ x
⊑ᵤ-refl {⊥} = ⊑ᵤ-bot
⊑ᵤ-refl {0ₙ} = ⊑ᵤ-refl-0
⊑ᵤ-refl {sᵤ _} = ⊑ᵤ-s ⊑ᵤ-refl
⊑ᵤ-refl {ℕ} = ⊑ᵤ-refl-ℕ
⊑ᵤ-refl {𝒰} = ⊑ᵤ-refl-𝒰
⊑ᵤ-refl {λᵤ 𝑓 x} = ⊑ᵤ-λ ⊑ᵤ-refl'
⊑ᵤ-refl {Π x 𝑓 _} = ⊑ᵤ-Π ⊑ᵤ-refl ⊑ᵤ-refl
