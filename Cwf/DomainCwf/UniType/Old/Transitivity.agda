module Cwf.UniType.Transitivity where

open import Base.Core
open import Base.FinFun
open import Cwf.UniType.AxiomProofs
open import Cwf.UniType.Definition
open import Cwf.UniType.Lemmata
open import Cwf.UniType.PrePost
open import Cwf.UniType.Relation

open import Agda.Builtin.Size

postProofIrr : ∀ {i} → {𝑓 : FinFun (Nbh {i}) (Nbh {i})} →
               ∀ {postable𝑓 postable𝑓′} →
               post 𝑓 postable𝑓 ⊑ᵤ post 𝑓 postable𝑓′
postProofIrr {𝑓 = ∅} = ⊑ᵤ-bot
postProofIrr {𝑓 = (_ , y) ∷ 𝑓} {post-cons postable𝑓 _} {post-cons postable𝑓′ _}
  = donkey {x = y} {post 𝑓 postable𝑓} {y} {post 𝑓 postable𝑓′} ⊑ᵤ-refl (postProofIrr {𝑓 = 𝑓})

gringo : ∀ {i} → {𝑓 𝑓′ : FinFun (Nbh {i}) (Nbh {i})} →
         ∀ {postable𝑓 postable∪} →
         post 𝑓 postable𝑓 ⊑ᵤ post (𝑓 ∪ 𝑓′) postable∪
gringo {postable𝑓 = post-nil} = ⊑ᵤ-bot
gringo {𝑓 = _ ∷ 𝑓} {𝑓′} {post-cons _ _} {post-cons _ _}
  = donkey ⊑ᵤ-refl (gringo {𝑓 = 𝑓})

gringu : ∀ {i} → {𝑓 𝑓′ : FinFun (Nbh {i}) (Nbh {i})} →
         {postable𝑓 : Postable 𝑓} → ∀ {postable𝑓′ postable∪} →
         post 𝑓′ postable𝑓′ ⊑ᵤ post (𝑓 ∪ 𝑓′) postable∪
gringu {postable𝑓 = post-nil} {postable𝑓′}
  = postProofIrr {postable𝑓 = postable𝑓′}
gringu {postable𝑓 = post-cons postable𝑓 _} {postable∪ = post-cons _ _}
  = goblet (gringu {postable𝑓 = postable𝑓})

tmpb : ∀ {i} → {𝑓 𝑓′ : FinFun (Nbh {i}) (Nbh {i})} →
       ∀ {postable𝑓 postable𝑓′ postable∪ con𝑓𝑓′} →
       ((post 𝑓 postable𝑓) ⊔ᵤ (post 𝑓′ postable𝑓′) [ con𝑓𝑓′ ]) ⊑ᵤ
       post (𝑓 ∪ 𝑓′) postable∪
tmpb {postable𝑓 = post-nil} {post-nil} = ⊑ᵤ-bot
tmpb {𝑓′ = _ ∷ 𝑓} {post-nil} {post-cons _ _} {post-cons _ _} {con𝑓𝑓′}
  = ⊑ᵤ-⊔ ⊑ᵤ-bot (donkey ⊑ᵤ-refl (postProofIrr {𝑓 = 𝑓})) con𝑓𝑓′
tmpb {postable𝑓 = post-cons postable𝑓 _} {postable∪ = post-cons _ _} {con𝑓𝑓′}
  = ⊑ᵤ-⊔ proof₁ proof₂ con𝑓𝑓′
  where proof₁ = donkey ⊑ᵤ-refl (gringo {postable𝑓 = postable𝑓})
        proof₂ = goblet (gringu {postable𝑓 = postable𝑓})

postulate tmpc : ∀ {i} → {𝑓 𝑓′ : FinFun (Nbh {i}) (Nbh {i})} →
                 ∀ {preable𝑓 preable𝑓′ preable∪ con𝑓𝑓′} →
                 pre (𝑓 ∪ 𝑓′) preable∪ ⊑ᵤ
                 ((pre 𝑓 preable𝑓) ⊔ᵤ (pre 𝑓′ preable𝑓′) [ con𝑓𝑓′ ])

postulate cheat : {P : Set} → P

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

⊑ᵤ-trans : ∀ {i} → {x y z : Nbh {i}} → x ⊑ᵤ y → y ⊑ᵤ z →
           x ⊑ᵤ z

⊑ᵤ-trans' : ∀ {i} → {𝑓 𝑓′ 𝑓″ : FinFun (Nbh {i}) (Nbh {i})} →
            ∀ {con𝑓 con𝑓′ con𝑓″} → λᵤ 𝑓 con𝑓 ⊑ᵤ λᵤ 𝑓′ con𝑓′ →
            λᵤ 𝑓′ con𝑓′ ⊑ᵤ λᵤ 𝑓″ con𝑓″ → ∀ {x y} → (x , y) ∈ 𝑓 →
            λ-proof 𝑓″ con𝑓″ x y

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
      ; p𝑓⊑post = ⊑ᵤ-trans (donkey {conzw = cheat} y⊑post recp𝑓⊑post) (tmpb {𝑓 = sub})
      ; pre⊑p𝑓 = ⊑ᵤ-trans (tmpc {𝑓 = sub} {con𝑓𝑓′ = cheat}) (donkey pre⊑x recpre⊑p𝑓)
      ; sub⊆𝑓′ = ∪-lemma₁ sub⊆𝑓 recsub⊆𝑓
      }

⊑ᵤ-trans ⊑ᵤ-bot y⊑z = ⊑ᵤ-bot
⊑ᵤ-trans ⊑ᵤ-refl-0 y⊑z = y⊑z
⊑ᵤ-trans ⊑ᵤ-refl-ℕ y⊑z = y⊑z
⊑ᵤ-trans ⊑ᵤ-refl-𝒰 y⊑z = y⊑z
⊑ᵤ-trans (⊑ᵤ-s x⊑y) (⊑ᵤ-s y⊑z)
  = ⊑ᵤ-s (⊑ᵤ-trans x⊑y y⊑z)
⊑ᵤ-trans {x = λᵤ _ con𝑓} (⊑ᵤ-λ p₁) (⊑ᵤ-λ p₂)
  = ⊑ᵤ-λ (⊑ᵤ-trans' {con𝑓 = con𝑓} (⊑ᵤ-λ p₁) (⊑ᵤ-λ p₂))
⊑ᵤ-trans (⊑ᵤ-Π x⊑y 𝑓⊑𝑔) (⊑ᵤ-Π y⊑z 𝑔⊑ℎ)
  = ⊑ᵤ-Π (⊑ᵤ-trans x⊑y y⊑z) (⊑ᵤ-trans 𝑓⊑𝑔 𝑔⊑ℎ)

⊑ᵤ-trans' {𝑓′ = ∅} _ _ _ = cheat
⊑ᵤ-trans' {𝑓′ = (x , y) ∷ 𝑓′} {𝑓″ = 𝑓″} a b (there _) = cheat
⊑ᵤ-trans' {𝑓′ = (x , y) ∷ 𝑓′} {𝑓″ = 𝑓″} a b here with (Ω ((x , y) ∷ 𝑓′) 𝑓″ {preable𝑓 = cheat} {postable𝑓 = cheat} b)
... | record { sub = sub ; preablesub = preablesub ; postablesub = postablesub ; p𝑓⊑post = p𝑓⊑post ; pre⊑p𝑓 = pre⊑p𝑓 ; sub⊆𝑓′ = sub⊆𝑓′ }
  = record
      { sub = sub
      ; sub⊆𝑓 = sub⊆𝑓′
      ; preablesub = preablesub
      ; postablesub = postablesub
      ; y⊑post = ⊑ᵤ-trans cheat p𝑓⊑post
      ; pre⊑x = ⊑ᵤ-trans pre⊑p𝑓 cheat
      }
