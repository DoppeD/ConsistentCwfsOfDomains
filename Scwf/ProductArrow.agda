{-# OPTIONS --safe #-}

module Scwf.ProductArrow where

open import Base.Variables
open import Scwf.Product

record ProductArrow-scwf : Set₂ where
  field
    prod-scwf : Prod-scwf
  open Prod-scwf prod-scwf public
  field
    _⇒_ : Ty → Ty → Ty

    lam : ∀ {Γ 𝐴 𝐵} → Tm (_•_ {m} Γ 𝐴) 𝐵 → Tm Γ (𝐴 ⇒ 𝐵)
    ap  : ∀ {Γ 𝐴 𝐵} → Tm Γ (𝐴 ⇒ 𝐵) → Tm {m} Γ 𝐴 → Tm Γ 𝐵

    lamSub : ∀ {Γ Δ 𝐴 𝐵} → (γ : Sub {n} {m} Δ Γ) →
             (𝑡 : Tm (Γ • 𝐴) 𝐵) →
             (lam 𝑡 [ γ ]) ≈ (lam (𝑡 [ ⟨ γ ∘ p Δ 𝐴 , q Δ 𝐴 ⟩ ]))
    apSub  : ∀ {Γ Δ 𝐴 𝐵} → (γ : Sub {n} {m} Δ Γ) →
             (𝑡 : Tm Γ (𝐴 ⇒ 𝐵)) → (𝑢 : Tm Γ 𝐴) →
             (ap (𝑡 [ γ ]) (𝑢 [ γ ])) ≈ (ap 𝑡 𝑢 [ γ ])

    β : ∀ {Γ 𝐴 𝐵} → {𝑡 : Tm {m} Γ 𝐴} → {𝑢 : Tm (Γ • 𝐴) 𝐵} →
        (ap (lam 𝑢) 𝑡) ≈ (𝑢 [ ⟨ id Γ , 𝑡 ⟩ ])

    lamCong : ∀ {Γ 𝐴 𝐵} → {𝑡 𝑡′ : Tm (_•_ {m} Γ 𝐴) 𝐵} →
              𝑡 ≈ 𝑡′ → (lam 𝑡) ≈ (lam 𝑡′)
    apCong  : ∀ {Γ 𝐴 𝐵} → {𝑡 𝑡′ : Tm {m} Γ (𝐴 ⇒ 𝐵)} →
              ∀ {𝑢 𝑢′} → 𝑡 ≈ 𝑡′ → 𝑢 ≈ 𝑢′ →
              (ap 𝑡 𝑢) ≈ (ap 𝑡′ 𝑢′)
