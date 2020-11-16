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
