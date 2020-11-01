{-# OPTIONS --safe --sized-types #-}

module Ucwf.DomainUcwf.UniType.Transitivity where

open import Base.Core
open import Base.FinFun
open import Ucwf.DomainUcwf.UniType.AxiomProofs
open import Ucwf.DomainUcwf.UniType.Definition
open import Ucwf.DomainUcwf.UniType.Lemmata
open import Ucwf.DomainUcwf.UniType.Relation
open import Ucwf.DomainUcwf.UniType.PrePost

open import Agda.Builtin.Size

private
  variable
    i j : Size

record ⊑ᵤ-proof₂ (𝑓 : FinFunₛ {i}) (𝑓′ : FinFunₛ {j}) :
                 Set where
  field
    sub : FinFunₛ
    p𝑓⊑ᵤpost : (post 𝑓) ⊑ᵤ (post sub)
    pre⊑ᵤp𝑓 : (pre sub) ⊑ᵤ (pre 𝑓)
    sub⊆𝑓′ : sub ⊆ 𝑓′

Ω-post : ∀ {i j} → {x y : UniNbh {i}} →
         {𝑓 𝑓′ : FinFunₛ {j}} → x ⊑ᵤ post 𝑓 →
         y ⊑ᵤ post 𝑓′ → (x ⊔ᵤ y [ con-all ]) ⊑ᵤ post (𝑓 ∪ 𝑓′)
Ω-post {x = x} {y} {𝑓} {𝑓′} x⊑post𝑓 y⊑post𝑓′ rewrite (post-≡ 𝑓 𝑓′)
  = ⊑ᵤ-⊔ᵤ-lemma₃ x y (post 𝑓) (post 𝑓′) x⊑post𝑓 y⊑post𝑓′

Ω-pre : ∀ {i j} → {x y : UniNbh {i}} →
        {𝑓 𝑓′ : FinFunₛ {j}} → pre 𝑓 ⊑ᵤ x →
        pre 𝑓′ ⊑ᵤ y → pre (𝑓 ∪ 𝑓′) ⊑ᵤ (x ⊔ᵤ y [ con-all ])
Ω-pre {x = x} {y} {𝑓} {𝑓′} pre𝑓⊑x pre𝑓′⊑y rewrite (pre-≡ 𝑓 𝑓′)
  = ⊑ᵤ-⊔ᵤ-lemma₃ (pre 𝑓) (pre 𝑓′) x y pre𝑓⊑x pre𝑓′⊑y

Ω : ∀ {i j} → (𝑓 : FinFunₛ {i}) → (𝑓′ : FinFunₛ {j}) →
    (λᵤ 𝑓) ⊑ᵤ (λᵤ 𝑓′) → ⊑ᵤ-proof₂ {i} {j} 𝑓 𝑓′
Ω ∅ 𝑓′ _ =
  record { sub = ∅
         ; p𝑓⊑ᵤpost = ⊑ᵤ-intro₁
         ; pre⊑ᵤp𝑓 = ⊑ᵤ-intro₁
         ; sub⊆𝑓′ = ∅-isSubset
         }
Ω ((x₁ , x₂) ∷ 𝑓″) 𝑓′ (⊑ᵤ-intro₂ _ _ p)
  with (p x₁ x₂ here)
Ω ((x₁ , x₂) ∷ 𝑓″) 𝑓′ (⊑ᵤ-intro₂ _ _ p)
  | record { sub = sub
           ; y⊑ᵤpost = y⊑ᵤpost
           ; pre⊑ᵤx = pre⊑ᵤx
           ; sub⊆𝑓′ = sub⊆𝑓′
           }
  = record { sub = sub ∪ sub′
           ; p𝑓⊑ᵤpost = Ω-post {𝑓 = sub} y⊑ᵤpost p𝑓⊑ᵤpost′
           ; pre⊑ᵤp𝑓 = Ω-pre {𝑓 = sub} pre⊑ᵤx pre⊑ᵤp𝑓′
           ; sub⊆𝑓′ = ∪-lemma₁ sub⊆𝑓′ sub′⊆𝑓′
           }
  where recur = Ω 𝑓″ 𝑓′ (⊑ᵤ-intro₂ 𝑓″ 𝑓′
                (λ a b ab∈𝑓″ → p a b (there ab∈𝑓″)))
        sub′ = ⊑ᵤ-proof₂.sub recur
        p𝑓⊑ᵤpost′ = ⊑ᵤ-proof₂.p𝑓⊑ᵤpost recur
        pre⊑ᵤp𝑓′ = ⊑ᵤ-proof₂.pre⊑ᵤp𝑓 recur
        sub′⊆𝑓′ = ⊑ᵤ-proof₂.sub⊆𝑓′ recur

⊑ᵤ-trans : ∀ {i x} → {y : UniNbh {i}} → ∀ {z} →
           x ⊑ᵤ y → y ⊑ᵤ z → x ⊑ᵤ z

⊑ᵤ-trans' : ∀ {i} → ∀ 𝑓 → (𝑓′ : FinFunₛ {i}) → ∀ 𝑓″ →
            (λᵤ 𝑓) ⊑ᵤ (λᵤ 𝑓′) → (λᵤ 𝑓′) ⊑ᵤ (λᵤ 𝑓″) →
            ∀ x′ y′ → (x′ , y′) ∈ 𝑓 → ⊑ᵤ-proof 𝑓″ x′ y′

⊑ᵤ-trans {x = ⊥ᵤ} _ _ = ⊑ᵤ-intro₁
⊑ᵤ-trans {x = λᵤ ∅} {⊥ᵤ} {⊥ᵤ} ()
⊑ᵤ-trans {x = λᵤ ∅} {λᵤ 𝑓′} {⊥ᵤ} (⊑ᵤ-intro₂ _ _ _) ()
⊑ᵤ-trans {x = λᵤ ∅} {λᵤ 𝑓′} {λᵤ 𝑓″} _ _ = ∅-⊥ᵤ
⊑ᵤ-trans {x = λᵤ (x ∷ 𝑔)} {λᵤ 𝑓′} {λᵤ 𝑓″} x⊑y y⊑z
  = ⊑ᵤ-intro₂ (x ∷ 𝑔) 𝑓″ (⊑ᵤ-trans' (x ∷ 𝑔) 𝑓′ 𝑓″ x⊑y y⊑z)

⊑ᵤ-trans' 𝑓 𝑓′ 𝑓″ (⊑ᵤ-intro₂ _ _ p) 𝑓′⊑𝑓″ x y xy∈𝑓
  with (p x y xy∈𝑓)
⊑ᵤ-trans' 𝑓 𝑓′ 𝑓″ 𝑓⊑𝑓′ 𝑓′⊑𝑓″ x y xy∈𝑓
  | record { sub = sub′ ; sub⊆𝑓′ = sub⊆𝑓′ }
  with (Ω sub′ 𝑓″ (shrink⊑ᵤ {𝑓′ = 𝑓′} 𝑓′⊑𝑓″ sub⊆𝑓′))
⊑ᵤ-trans' 𝑓 𝑓′ 𝑓″ (⊑ᵤ-intro₂ _ _ p) 𝑓′⊑𝑓″ x y xy∈𝑓
  | record { sub = sub′
           ; pre⊑ᵤx = pre′⊑ᵤx
           ; y⊑ᵤpost = y⊑ᵤpost′
           ; sub⊆𝑓′ = sub′⊆𝑓′
           }
  | record { sub = sub″
           ; p𝑓⊑ᵤpost = p𝑓⊑ᵤpost″
           ; pre⊑ᵤp𝑓 = pre″⊑ᵤp𝑓
           ; sub⊆𝑓′ = sub″⊆𝑓″
           }
  = record { sub = sub″
           ; y⊑ᵤpost = ⊑ᵤ-trans y⊑ᵤpost′ p𝑓⊑ᵤpost″
           ; pre⊑ᵤx = ⊑ᵤ-trans pre″⊑ᵤp𝑓 pre′⊑ᵤx
           ; sub⊆𝑓′ = sub″⊆𝑓″
           }
