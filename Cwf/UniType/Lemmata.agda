module Cwf.UniType.Lemmata where

open import Base.Core
open import Base.FinFun
open import Cwf.UniType.Definition
open import Cwf.UniType.Relation

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Size

getCff : ∀ {i} → {𝑓 : FinFun (Nbh {i}) (Nbh {i})} →
         {x y x′ y′ : Nbh {i}} → ConFinFun 𝑓 →
         (x , y) ∈ 𝑓 → (x′ , y′) ∈ 𝑓 →
         Con x x′ → Con y y′
getCff (cff p) = p

cffSym : ∀ {i} → {𝑓 𝑔 : FinFun (Nbh {i}) (Nbh {i})} →
         ConFinFun (𝑓 ∪ 𝑔) → ConFinFun (𝑔 ∪ 𝑓)
cffSym {𝑓 = 𝑓} (cff p)
  = cff λ xy∈𝑓∪𝑔 x′y′∈𝑓∪𝑔 → p (∪-lemma₈ {𝑓′ = 𝑓} xy∈𝑓∪𝑔)
    (∪-lemma₈ {𝑓′ = 𝑓} x′y′∈𝑓∪𝑔)

conSym : ∀ {i} → {x y : Nbh {i}} → Con x y → Con y x
conSym con-⊥₁ = con-⊥₂
conSym con-⊥₂ = con-⊥₁
conSym con-refl-0 = con-refl-0
conSym (con-s consxsy) = con-s (conSym consxsy)
conSym con-refl-ℕ = con-refl-ℕ
conSym con-refl-𝒰 = con-refl-𝒰
conSym (con-Π {𝑓 = 𝑓} conxy cff𝑓∪𝑔)
  = con-Π (conSym conxy) (cffSym {𝑓 = 𝑓} cff𝑓∪𝑔)
conSym (con-λ {𝑓 = 𝑓} cff∪) = con-λ (cffSym {𝑓 = 𝑓} cff∪)

liftλ-proof : ∀ {i} → {𝑓 𝑓′ : FinFun (Nbh {i}) (Nbh {i})} →
              ∀ {con𝑓 con𝑓′ x y} → 𝑓 ⊆ 𝑓′ →
              λ-proof 𝑓 con𝑓 x y → λ-proof 𝑓′ con𝑓′ x y
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

shrinkλ-proof : ∀ {i} → {𝑓 𝑓′ 𝑓″ : FinFun (Nbh {i}) (Nbh {i})} →
                ∀ {con𝑓′ con𝑓″} → 𝑓 ⊆ 𝑓′ →
                λᵤ 𝑓′ con𝑓′ ⊑ᵤ λᵤ 𝑓″ con𝑓″ →
                ∀ {x y} → (x , y) ∈ 𝑓 →
                λ-proof 𝑓″ con𝑓″ x y
shrinkλ-proof 𝑓⊆𝑓′ (⊑ᵤ-λ p) xy∈𝑓 = p (𝑓⊆𝑓′ xy∈𝑓)

duff : ∀ {i} → ∀ {𝑓 𝑓′ 𝑓″ : FinFun (Nbh {i}) (Nbh {i})} →
       ∀ {cff𝑓′ cff𝑓′∪𝑓″} →
       (∀ {x y} → (x , y) ∈ 𝑓 → λ-proof 𝑓′ cff𝑓′ x y) →
       ∀ {x y} → (x , y) ∈ 𝑓 → λ-proof (𝑓′ ∪ 𝑓″) cff𝑓′∪𝑓″ x y
duff p₁ xy∈𝑓 with (p₁ xy∈𝑓)
... | record
        { sub = sub
        ; sub⊆𝑓 = sub⊆𝑓
        ; preablesub = preablesub
        ; postablesub = postablesub
        ; y⊑post = y⊑post
        ; pre⊑x = pre⊑x
        }
  = record
      { sub = sub
      ; sub⊆𝑓 = ⊆-trans sub⊆𝑓 ∪-lemma₆
      ; preablesub = preablesub
      ; postablesub = postablesub
      ; y⊑post = y⊑post
      ; pre⊑x = pre⊑x
      }

daff : ∀ {i} → ∀ {𝑓 𝑓′ 𝑓″ : FinFun (Nbh {i}) (Nbh {i})} →
       ∀ {cff𝑓″ cff𝑓′∪𝑓″} →
       (∀ {x y} → (x , y) ∈ 𝑓 → λ-proof 𝑓″ cff𝑓″ x y) →
       ∀ {x y} → (x , y) ∈ 𝑓 → λ-proof (𝑓′ ∪ 𝑓″) cff𝑓′∪𝑓″ x y
daff p₁ xy∈𝑓 with (p₁ xy∈𝑓)
... | record
        { sub = sub
        ; sub⊆𝑓 = sub⊆𝑓
        ; preablesub = preablesub
        ; postablesub = postablesub
        ; y⊑post = y⊑post
        ; pre⊑x = pre⊑x
        }
  = record
      { sub = sub
      ; sub⊆𝑓 = ⊆-trans sub⊆𝑓 ∪-lemma₇
      ; preablesub = preablesub
      ; postablesub = postablesub
      ; y⊑post = y⊑post
      ; pre⊑x = pre⊑x
      }

giblet : ∀ {i} → {x y z : Nbh {i}} → ∀ {conyz} → x ⊑ᵤ y → x ⊑ᵤ (y ⊔ᵤ z [ conyz ])
giblet ⊑ᵤ-bot = ⊑ᵤ-bot
giblet {conyz = con-⊥₂} ⊑ᵤ-refl-0 = ⊑ᵤ-refl-0
giblet {conyz = con-refl-0} ⊑ᵤ-refl-0 = ⊑ᵤ-refl-0
giblet {conyz = con-⊥₂} ⊑ᵤ-refl-ℕ = ⊑ᵤ-refl-ℕ
giblet {conyz = con-refl-ℕ} ⊑ᵤ-refl-ℕ = ⊑ᵤ-refl-ℕ
giblet {conyz = con-⊥₂} ⊑ᵤ-refl-𝒰 = ⊑ᵤ-refl-𝒰
giblet {conyz = con-refl-𝒰} ⊑ᵤ-refl-𝒰 = ⊑ᵤ-refl-𝒰
giblet {conyz = con-⊥₂} (⊑ᵤ-s x⊑y) = ⊑ᵤ-s x⊑y
giblet {conyz = con-s conyz} (⊑ᵤ-s x⊑y) = ⊑ᵤ-s (giblet x⊑y)
giblet {conyz = con-⊥₂} (⊑ᵤ-λ p) = ⊑ᵤ-λ p
giblet {conyz = con-λ _} (⊑ᵤ-λ p) = ⊑ᵤ-λ (duff p)
giblet {conyz = con-⊥₂} (⊑ᵤ-Π x⊑y 𝑓⊑𝑔) = ⊑ᵤ-Π x⊑y 𝑓⊑𝑔
giblet {z = Π _ _ conℎ} {conyz = con-Π _ cff𝑔∪ℎ} (⊑ᵤ-Π x⊑y 𝑓⊑𝑔)
  = ⊑ᵤ-Π (giblet x⊑y) (giblet {conyz = con-λ {con𝑔 = conℎ} cff𝑔∪ℎ} 𝑓⊑𝑔)

goblet : ∀ {i} → {x y z : Nbh {i}} → ∀ {conyz} → x ⊑ᵤ z → x ⊑ᵤ (y ⊔ᵤ z [ conyz ])
goblet ⊑ᵤ-bot = ⊑ᵤ-bot
goblet {conyz = con-⊥₁} ⊑ᵤ-refl-0 = ⊑ᵤ-refl-0
goblet {conyz = con-refl-0} ⊑ᵤ-refl-0 = ⊑ᵤ-refl-0
goblet {conyz = con-⊥₁} ⊑ᵤ-refl-ℕ = ⊑ᵤ-refl-ℕ
goblet {conyz = con-refl-ℕ} ⊑ᵤ-refl-ℕ = ⊑ᵤ-refl-ℕ
goblet {conyz = con-⊥₁} ⊑ᵤ-refl-𝒰 = ⊑ᵤ-refl-𝒰
goblet {conyz = con-refl-𝒰} ⊑ᵤ-refl-𝒰 = ⊑ᵤ-refl-𝒰
goblet {conyz = con-⊥₁} (⊑ᵤ-s x⊑z) = ⊑ᵤ-s x⊑z
goblet {conyz = con-s _} (⊑ᵤ-s x⊑z) = ⊑ᵤ-s (goblet x⊑z)
goblet {conyz = con-⊥₁} (⊑ᵤ-λ p) = ⊑ᵤ-λ p
goblet {conyz = con-λ _} (⊑ᵤ-λ p) = ⊑ᵤ-λ (daff p)
goblet {conyz = con-⊥₁} (⊑ᵤ-Π x⊑z 𝑓⊑ℎ) = ⊑ᵤ-Π x⊑z 𝑓⊑ℎ
goblet {conyz = con-Π conyz x} (⊑ᵤ-Π x⊑z (⊑ᵤ-λ p))
  = ⊑ᵤ-Π (goblet x⊑z) (⊑ᵤ-λ (daff p))

doff : ∀ {i} → ∀ {𝑓 𝑓′ 𝑔 𝑔′ : FinFun (Nbh {i}) (Nbh {i})} →
       ∀ {cff𝑔 cff𝑔′ cff𝑔∪𝑔′} →
       (∀ {x y} → (x , y) ∈ 𝑓 → λ-proof 𝑔 cff𝑔 x y) →
       (∀ {x y} → (x , y) ∈ 𝑓′ → λ-proof 𝑔′ cff𝑔′ x y) →
       ∀ {x y} → (x , y) ∈ (𝑓 ∪ 𝑓′) → λ-proof (𝑔 ∪ 𝑔′) cff𝑔∪𝑔′ x y
doff {𝑓 = 𝑓} _ _ xy∈𝑓∪𝑓′ with (∪-lemma₂ {𝑓 = 𝑓} xy∈𝑓∪𝑓′)
doff p₁ _ _ | inl xy∈𝑓 with (p₁ xy∈𝑓)
doff _ _ _  | _
  | record { sub = sub
           ; sub⊆𝑓 = sub⊆𝑓
           ; preablesub = preablesub
           ; postablesub = postablesub
           ; y⊑post = y⊑post
           ; pre⊑x = pre⊑x
           }
  = record
      { sub = sub
      ; sub⊆𝑓 = ⊆-trans sub⊆𝑓 ∪-lemma₆
      ; preablesub = preablesub
      ; postablesub = postablesub
      ; y⊑post = y⊑post
      ; pre⊑x = pre⊑x
      }
doff _ p₂ _ | inr xy∈𝑓′ with (p₂ xy∈𝑓′)
doff _ _ _  | _
  | record { sub = sub
           ; sub⊆𝑓 = sub⊆𝑓
           ; preablesub = preablesub
           ; postablesub = postablesub
           ; y⊑post = y⊑post
           ; pre⊑x = pre⊑x
           }
  = record
      { sub = sub
      ; sub⊆𝑓 = ⊆-trans sub⊆𝑓 ∪-lemma₇
      ; preablesub = preablesub
      ; postablesub = postablesub
      ; y⊑post = y⊑post
      ; pre⊑x = pre⊑x
      }

donkey : ∀ {i} → {x y z w : Nbh {i}} → ∀ {conxy conzw} →
         x ⊑ᵤ z → y ⊑ᵤ w → (x ⊔ᵤ y [ conxy ]) ⊑ᵤ (z ⊔ᵤ w [ conzw ])
donkey {y = ⊥} ⊑ᵤ-bot _ = ⊑ᵤ-bot
donkey {y = 0ₙ} ⊑ᵤ-bot y⊑w = goblet y⊑w
donkey {y = sᵤ y} {conzw = con-⊥₁} ⊑ᵤ-bot (⊑ᵤ-s y⊑w) = ⊑ᵤ-s y⊑w
donkey {y = sᵤ y} {conzw = con-s conzw} ⊑ᵤ-bot (⊑ᵤ-s y⊑w) = ⊑ᵤ-s (goblet y⊑w)
donkey {y = ℕ} ⊑ᵤ-bot y⊑w = goblet y⊑w
donkey {y = 𝒰} ⊑ᵤ-bot y⊑w = goblet y⊑w
donkey {y = λᵤ _ _} ⊑ᵤ-bot y⊑w = goblet y⊑w
donkey {y = Π _ _ _} ⊑ᵤ-bot y⊑w = goblet y⊑w
donkey {conzw = con-⊥₂} ⊑ᵤ-refl-0 ⊑ᵤ-bot = ⊑ᵤ-refl-0
donkey {conzw = con-refl-0} ⊑ᵤ-refl-0 ⊑ᵤ-bot = ⊑ᵤ-refl-0
donkey {conzw = con-refl-0} ⊑ᵤ-refl-0 ⊑ᵤ-refl-0 = ⊑ᵤ-refl-0
donkey {conzw = con-⊥₂} ⊑ᵤ-refl-ℕ ⊑ᵤ-bot = ⊑ᵤ-refl-ℕ
donkey {conzw = con-refl-ℕ} ⊑ᵤ-refl-ℕ ⊑ᵤ-bot = ⊑ᵤ-refl-ℕ
donkey {conzw = con-refl-ℕ} ⊑ᵤ-refl-ℕ ⊑ᵤ-refl-ℕ = ⊑ᵤ-refl-ℕ
donkey {conzw = con-⊥₂} ⊑ᵤ-refl-𝒰 ⊑ᵤ-bot = ⊑ᵤ-refl-𝒰
donkey {conzw = con-refl-𝒰} ⊑ᵤ-refl-𝒰 ⊑ᵤ-bot = ⊑ᵤ-refl-𝒰
donkey {conzw = con-refl-𝒰} ⊑ᵤ-refl-𝒰 ⊑ᵤ-refl-𝒰 = ⊑ᵤ-refl-𝒰
donkey {conzw = con-⊥₂} (⊑ᵤ-s x⊑z) ⊑ᵤ-bot = ⊑ᵤ-s x⊑z
donkey {conzw = con-s conzw} (⊑ᵤ-s x⊑z) ⊑ᵤ-bot
  = ⊑ᵤ-s (giblet x⊑z)
donkey {conxy = con-s conxy} {conzw = con-s conzw} (⊑ᵤ-s x⊑z) (⊑ᵤ-s y⊑w)
  = ⊑ᵤ-s (donkey x⊑z y⊑w)
donkey {conxy = con-⊥₂} {con-⊥₂} (⊑ᵤ-λ p) _ = ⊑ᵤ-λ p
donkey {conxy = con-⊥₂} {con-λ _} (⊑ᵤ-λ p) _ = ⊑ᵤ-λ (duff p)
donkey {conxy = con-λ _} {con-λ _} (⊑ᵤ-λ p₁) (⊑ᵤ-λ p₂) = ⊑ᵤ-λ (doff p₁ p₂)
donkey {conxy = con-⊥₂} {con-⊥₂} (⊑ᵤ-Π x⊑z 𝑓⊑ℎ) _
  = ⊑ᵤ-Π x⊑z 𝑓⊑ℎ
donkey {conxy = con-⊥₂} {con-Π _ _} (⊑ᵤ-Π x⊑z (⊑ᵤ-λ p)) x₁
  = ⊑ᵤ-Π (giblet x⊑z) (⊑ᵤ-λ (duff p))
donkey {conxy = con-Π conxy x₃} {con-Π conzw x₅} (⊑ᵤ-Π x⊑z (⊑ᵤ-λ p₁)) (⊑ᵤ-Π x⊑w (⊑ᵤ-λ p₂))
  = ⊑ᵤ-Π (donkey x⊑z x⊑w) (⊑ᵤ-λ (doff p₁ p₂))
