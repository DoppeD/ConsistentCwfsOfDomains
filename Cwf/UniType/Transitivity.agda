module Cwf.UniType.Transitivity where

open import Base.Core
open import Base.FinFun
open import Cwf.UniType.AxiomProofs
open import Cwf.UniType.Definition
open import Cwf.UniType.Lemmata
open import Cwf.UniType.PrePost
open import Cwf.UniType.Relation

open import Agda.Builtin.Size

record λ-proof₂ {i : Size} (𝑓 𝑓′ : FinFun (Nbh {i}) (Nbh {i}))
                (preable𝑓 : Preable 𝑓) (postable𝑓 : Postable 𝑓) :
                Set where
  field
    sub : FinFun (Nbh {i}) (Nbh {i})
    preablesub : Preable sub
    postablesub : Postable sub
    p𝑓⊑post : (post 𝑓 postable𝑓) ⊑ᵤ (post sub postablesub)
    pre⊑p𝑓 : (pre sub preablesub) ⊑ᵤ (pre 𝑓 preable𝑓)
    sub⊆𝑓′ : sub ⊆ 𝑓′

Ω : ∀ {i} → (𝑓 𝑓′ : FinFun (Nbh {i}) (Nbh {i})) →
    ∀ {con𝑓 con𝑓′ preable𝑓 postable𝑓} →
    λᵤ 𝑓 con𝑓 ⊑ᵤ λᵤ 𝑓′ con𝑓′ →
    λ-proof₂ 𝑓 𝑓′ preable𝑓 postable𝑓
Ω ∅ _ _
  = record
      { sub = ∅
      ; preablesub = pre-nil
      ; postablesub = post-nil
      ; p𝑓⊑post = ⊑ᵤ-bot
      ; pre⊑p𝑓 = ⊑ᵤ-bot
      ; sub⊆𝑓′ = ∅-isSubset
      }
Ω ((x , y) ∷ 𝑓) 𝑓′ {con𝑓 = con𝑓} {con𝑓′}
  {pre-cons preable𝑓 _} {post-cons postable𝑓 _} (⊑ᵤ-λ p) with (p here)
  | Ω 𝑓 𝑓′ {con𝑓 = subsetIsCon ⊆-lemma₃ con𝑓} {con𝑓′} {preable𝑓} {postable𝑓}
    (⊑ᵤ-λ (shrinkλ-proof {con𝑓′ = con𝑓} ⊆-lemma₃ (⊑ᵤ-λ p)))
... | record
        { sub = sub
        ; sub⊆𝑓 = sub⊆𝑓
        ; preablesub = preablesub
        ; postablesub = postablesub
        ; y⊑post = y⊑post
        ; pre⊑x = pre⊑x
        }
    | record
        { sub = recsub
        ; preablesub = recpreablesub
        ; postablesub = recpostablesub
        ; p𝑓⊑post = recp𝑓⊑post
        ; pre⊑p𝑓 = recpre⊑p𝑓
        ; sub⊆𝑓′ = recsub⊆𝑓
        }
  = record
      { sub = sub ∪ recsub
      ; preablesub = {!!}
      ; postablesub = {!!}
      ; p𝑓⊑post = {!!}
      ; pre⊑p𝑓 = {!!}
      ; sub⊆𝑓′ = ∪-lemma₁ sub⊆𝑓 recsub⊆𝑓
      }

baff : ∀ {x 𝑓 𝑓′ postable𝑓 postable𝑓′} → 𝑓 ⊆ 𝑓′ →
       x ⊑ᵤ post 𝑓 postable𝑓 → x ⊑ᵤ post 𝑓′ postable𝑓′
baff {𝑓 = ∅} 𝑓⊆𝑓′ ⊑ᵤ-bot = ⊑ᵤ-bot
baff {𝑓 = (x , y) ∷ 𝑓} {postable𝑓 = post-cons postable𝑓 conypost𝑓}
  𝑓⊆𝑓′ x⊑post𝑓
  = {!!}

tmp : ∀ {x y 𝑓 𝑓′ conxy postable𝑓 postable𝑓′ postable∪} →
      x ⊑ᵤ post 𝑓 postable𝑓 → y ⊑ᵤ post 𝑓′ postable𝑓′ →
      (x ⊔ᵤ y [ conxy ]) ⊑ᵤ post (𝑓 ∪ 𝑓′) postable∪
tmp {conxy = con-⊥₁} {postable𝑓′ = postable𝑓′} {postable∪} _ y⊑post𝑓′
  = ⊥-leftId₁ (baff {postable𝑓 = postable𝑓′} {postable∪} ∪-lemma₇ y⊑post𝑓′)
tmp {conxy = con-⊥₂} {postable𝑓 = postable𝑓} {postable∪ = postable∪} x⊑post𝑓 _
  = baff {postable𝑓 = postable𝑓} {postable∪} ∪-lemma₆ x⊑post𝑓
tmp {conxy = con-refl-0} {postable𝑓′ = postable𝑓′} {postable∪} _ y⊑post𝑓′
  = baff {postable𝑓 = postable𝑓′} {postable∪} ∪-lemma₇ y⊑post𝑓′
tmp {conxy = con-s conxy} x⊑post𝑓 y⊑post𝑓′ = {!!}
tmp {conxy = con-refl-ℕ} {postable𝑓′ = postable𝑓′} {postable∪} _ y⊑post𝑓′
  = baff {postable𝑓 = postable𝑓′} {postable∪} ∪-lemma₇ y⊑post𝑓′
tmp {conxy = con-refl-𝒰} {postable𝑓′ = postable𝑓′} {postable∪} _ y⊑post𝑓′
  = baff {postable𝑓 = postable𝑓′} {postable∪} ∪-lemma₇ y⊑post𝑓′
tmp {conxy = con-λ x} x⊑post𝑓 y⊑post𝑓′ = {!!}
tmp {conxy = con-Π conxy x} x⊑post𝑓 y⊑post𝑓′ = {!!}

⊑ᵤ-trans : ∀ {i} → {x y z : Nbh {i}} → x ⊑ᵤ y → y ⊑ᵤ z →
           x ⊑ᵤ z
⊑ᵤ-trans ⊑ᵤ-bot y⊑z = ⊑ᵤ-bot
⊑ᵤ-trans ⊑ᵤ-refl-0 y⊑z = y⊑z
⊑ᵤ-trans ⊑ᵤ-refl-ℕ y⊑z = y⊑z
⊑ᵤ-trans ⊑ᵤ-refl-𝒰 y⊑z = y⊑z
⊑ᵤ-trans (⊑ᵤ-s x⊑y) (⊑ᵤ-s y⊑z)
  = ⊑ᵤ-s (⊑ᵤ-trans x⊑y y⊑z)
⊑ᵤ-trans (⊑ᵤ-λ p₁) (⊑ᵤ-λ p₂)
  = {!!}
⊑ᵤ-trans (⊑ᵤ-Π x⊑y 𝑓⊑𝑔) (⊑ᵤ-Π y⊑z 𝑔⊑ℎ)
  = ⊑ᵤ-Π (⊑ᵤ-trans x⊑y y⊑z) (⊑ᵤ-trans 𝑓⊑𝑔 𝑔⊑ℎ)
