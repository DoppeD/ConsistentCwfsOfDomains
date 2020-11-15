module Cwf.UniType.Relation where

open import Base.Core
open import Base.FinFun
open import Cwf.UniType.Definition
open import Cwf.UniType.PrePost

open import Agda.Builtin.Size

record λ-proof {i : Size} (𝑓 : FinFun (Nbh {i}) (Nbh {i}))
               (con𝑓 : ConFinFun 𝑓) (x y : Nbh {i}) :
               Set
data _⊑ᵤ_ : ∀ {i} → Nbh {i} → Nbh {i} → Set

record λ-proof {i} 𝑓 con𝑓 x y where
  inductive
  field
    sub : FinFun (Nbh {i}) (Nbh {i})
    sub⊆𝑓 : sub ⊆ 𝑓
    preablesub : Preable sub
    postablesub : Postable sub
    y⊑post : y ⊑ᵤ (post sub postablesub)
    pre⊑x : (pre sub preablesub) ⊑ᵤ x

data _⊑ᵤ_ where
  ⊑ᵤ-bot : ∀ {i} → {x : Nbh {i}} → ⊥ ⊑ᵤ x
  ⊑ᵤ-refl-0 : ∀ {i} → 0ₙ {i} ⊑ᵤ 0ₙ
  ⊑ᵤ-refl-ℕ : ∀ {i} → ℕ {i} ⊑ᵤ ℕ
  ⊑ᵤ-refl-𝒰 : ∀ {i} → 𝒰 {i} ⊑ᵤ 𝒰
  ⊑ᵤ-s : ∀ {i} → {x y : Nbh {i}} → x ⊑ᵤ y → sᵤ x ⊑ᵤ sᵤ y
  ⊑ᵤ-λ : ∀ {i} → {𝑓 𝑔 : FinFun (Nbh {i}) (Nbh {i})} → ∀ {con𝑓 con𝑔} →
         (∀ {x y} → (x , y) ∈ 𝑓 → λ-proof {i} 𝑓 con𝑓 x y) →
         (λᵤ 𝑓 con𝑓) ⊑ᵤ (λᵤ 𝑔 con𝑔)
  ⊑ᵤ-Π : ∀ {i} → {x y : Nbh {i}} → {𝑓 𝑔 : FinFun (Nbh {i}) (Nbh {i})} →
         ∀ {con𝑓 con𝑔} → x ⊑ᵤ y → (λᵤ 𝑓 con𝑓) ⊑ᵤ (λᵤ 𝑔 con𝑔) →
         (Π x 𝑓 con𝑓) ⊑ᵤ (Π y 𝑔 con𝑔)
