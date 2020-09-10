{-# OPTIONS --safe #-}

module Scwf.Product where

open import Base.Variables
open import Scwf.Plain

open import Agda.Builtin.Nat

record Prod-scwf : Set₂ where
  field
    scwf : Scwf
  open Scwf scwf public
  field
    _×_ : Ty → Ty → Ty

    fst : ∀ {Γ 𝐴 𝐵} → Tm {m} Γ (𝐴 × 𝐵) → Tm Γ 𝐴
    snd : ∀ {Γ 𝐴 𝐵} → Tm {m} Γ (𝐴 × 𝐵) → Tm Γ 𝐵
    <_,_> : ∀ {Γ 𝐴 𝐵} → Tm {m} Γ 𝐴 → Tm Γ 𝐵 → Tm Γ (𝐴 × 𝐵)

    fstAxiom : ∀ {Γ 𝐴 𝐵} → {𝑡 : Tm {m} Γ 𝐴} → {𝑢 : Tm Γ 𝐵} →
               fst < 𝑡 , 𝑢 > ≈ 𝑡
    sndAxiom : ∀ {Γ 𝐴 𝐵} → {𝑡 : Tm {m} Γ 𝐴} → {𝑢 : Tm Γ 𝐵} →
               snd < 𝑡 , 𝑢 > ≈ 𝑢
    pairSub : ∀ {Γ Δ 𝐴 𝐵} → {𝑡 : Tm Γ 𝐴} → {𝑢 : Tm Γ 𝐵} →
              {γ : Sub {n} {m} Δ Γ} →
              (< 𝑡 , 𝑢 > [ γ ]) ≈ < 𝑡 [ γ ] , 𝑢 [ γ ] >

    fstCong : ∀ {Γ 𝐴 𝐵} → {𝑡 𝑡′ : Tm {m} Γ (𝐴 × 𝐵)} → 𝑡 ≈ 𝑡′ →
              fst 𝑡 ≈ fst 𝑡′
    sndCong : ∀ {Γ 𝐴 𝐵} → {𝑡 𝑡′ : Tm {m} Γ (𝐴 × 𝐵)} → 𝑡 ≈ 𝑡′ →
              snd 𝑡 ≈ snd 𝑡′
    pairCong : ∀ {Γ 𝐴 𝐵} → {𝑡 𝑡′ : Tm {m} Γ 𝐴} → {𝑢 𝑢′ : Tm Γ 𝐵} →
               𝑡 ≈ 𝑡′ → 𝑢 ≈ 𝑢′ →
               < 𝑡 , 𝑢 > ≈ < 𝑡′ , 𝑢′ >

    -- We merge the ℕ₁-structure with the ×-structure.
    ℕ₁ : Ty
    0₁ : ∀ {Γ} → Tm {m} Γ ℕ₁
    ℕ₁-sub : ∀ {Γ Δ} → {γ : Sub {n} {m} Δ Γ} →
             (0₁ [ γ ]) ≈ 0₁
