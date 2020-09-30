{-# OPTIONS --safe #-}

module Ucwf.LambdaBeta where

open import Base.Variables
open import Ucwf.Plain

open import Agda.Builtin.Nat

record λβ-ucwf : Set₂ where
  field
    ucwf : Ucwf
  open Ucwf ucwf public
  field
    lam : Tm (suc m) → Tm m
    ap  : Tm m → Tm m → Tm m

    lamSub : (γ : Sub n m) → (𝑡 : Tm (suc m)) →
             (lam 𝑡 [ γ ]) ≈ (lam (𝑡 [ ⟨ γ ∘ p , q ⟩ ]))
    apSub : (γ : Sub n m) → (𝑡 𝑢 : Tm m) →
            ap (𝑡 [ γ ]) (𝑢 [ γ ]) ≈ (ap 𝑡 𝑢 [ γ ])
            
    β : {𝑡 : Tm m} → {𝑢 : Tm (suc m)} →
        ap (lam 𝑢) 𝑡 ≈ (𝑢 [ ⟨ id , 𝑡 ⟩ ])

    lamCong : ∀ {𝑡 𝑡′ : Tm (suc m)} → 𝑡 ≈ 𝑡′ →
              lam 𝑡 ≈ lam 𝑡′
    apCong : {𝑡 𝑡′ : Tm m} → ∀ {𝑢 𝑢′} →
             𝑡 ≈ 𝑡′ → 𝑢 ≈ 𝑢′ →
             ap 𝑡 𝑢 ≈ ap 𝑡′ 𝑢′
