module Cwf.UniType.PrePost where

open import Base.Core
open import Base.FinFun
open import Cwf.UniType.Definition

data Preable : ∀ {i} → FinFun (Nbh {i}) (Nbh {i}) → Set
pre : ∀ {i} → (𝑓 : FinFun (Nbh {i}) (Nbh {i})) → Preable 𝑓 → Nbh {i}

data Preable  where
  pre-nil : ∀ {i} → Preable {i} ∅
  pre-cons : ∀ {i} → {x y : Nbh {i}} → {𝑓 : FinFun (Nbh {i}) (Nbh {i})} →
             (preable𝑓 : Preable 𝑓) → Con x (pre 𝑓 preable𝑓) →
             Preable ((x , y) ∷ 𝑓)

pre ∅ _ = ⊥
pre ((x , y) ∷ 𝑓) (pre-cons preable𝑓 conxpre𝑓)
  = x ⊔ᵤ (pre 𝑓 preable𝑓) [ conxpre𝑓 ]

data Postable : ∀ {i} → FinFun (Nbh {i}) (Nbh {i}) → Set
post : ∀ {i} → (𝑓 : FinFun (Nbh {i}) (Nbh {i})) → Postable 𝑓 → Nbh {i}

data Postable  where
  post-nil : ∀ {i} → Postable {i} ∅
  post-cons : ∀ {i} → {x y : Nbh {i}} → {𝑓 : FinFun (Nbh {i}) (Nbh {i})} →
              (postable𝑓 : Postable 𝑓) → Con y (post 𝑓 postable𝑓) →
              Postable ((x , y) ∷ 𝑓)

post ∅ _ = ⊥
post ((x , y) ∷ 𝑓) (post-cons postable𝑓 conypost𝑓)
  = y ⊔ᵤ (post 𝑓 postable𝑓) [ conypost𝑓 ]
