{-# OPTIONS --safe #-}

module Ucwf.Plain where

open import Base.Core using (Rel ; IsEquivalence)
open import Base.Variables

open import Agda.Builtin.Nat

record Ucwf : Set₂ where
  field
    Tm : Nat → Set₁
    Sub : Nat → Nat → Set₁

    _≈_ : Rel (Tm n)
    _≊_ : Rel (Sub m n)

    isEquivT : IsEquivalence (_≈_ {n})
    isEquivS : IsEquivalence (_≊_ {m} {n})

    q : Tm (suc n)
    _[_] : Tm n → Sub m n → Tm m

    id : Sub n n
    _∘_ : Sub n o → Sub m n → Sub m o
    ⟨⟩ : Sub n 0
    ⟨_,_⟩ : Sub m n → Tm m → Sub m (suc n)
    p : Sub (suc n) n

    idL : (γ : Sub n m) → (id ∘ γ) ≊ γ
    idR : (γ : Sub n m) → (γ ∘ id) ≊ γ
    subAssoc : (γ : Sub m n) → (δ : Sub n o) →
               (θ : Sub o r) →
               ((θ ∘ δ) ∘ γ) ≊ (θ ∘ (δ ∘ γ))

    idSub : (𝑡 : Tm n) → (𝑡 [ id ]) ≈ 𝑡
    compSub : (𝑡 : Tm n) → (γ : Sub m n) →
              (δ : Sub o m) →
              (𝑡 [ (γ ∘ δ) ]) ≈ ((𝑡 [ γ ]) [ δ ])

    id₀ : id ≊ ⟨⟩
    <>-zero : (γ : Sub m n) → (⟨⟩ ∘ γ) ≊ ⟨⟩

    pCons : (γ : Sub n m) → (𝑡 : Tm n) →
            (p ∘ ⟨ γ , 𝑡 ⟩) ≊ γ
    qCons : (γ : Sub n m) → (𝑡 : Tm n) →
            (q [ ⟨ γ , 𝑡 ⟩ ]) ≈ 𝑡
    idExt : (id {suc m}) ≊ ⟨ p , q ⟩
    compExt : (𝑡 : Tm n) → (γ : Sub n m) → (δ : Sub m n) →
              (⟨ γ , 𝑡 ⟩ ∘ δ) ≊ ⟨ γ ∘ δ , 𝑡 [ δ ] ⟩

    subCong : {𝑡 𝑡′ : Tm m} → {γ γ′ : Sub n m} →
              𝑡 ≈ 𝑡′ → γ ≊ γ′ →
              (𝑡 [ γ ]) ≈ (𝑡′ [ γ′ ])
    <,>-cong : {𝑡 𝑡′ : Tm m} → {γ γ′ : Sub m n} →
               𝑡 ≈ 𝑡′ → γ ≊ γ′ →
               ⟨ γ , 𝑡 ⟩ ≊ ⟨ γ′ , 𝑡′ ⟩
    ∘-cong : {γ δ : Sub n o} → {γ′ δ′ : Sub m n} →
             γ ≊ δ →
             γ′ ≊ δ′ → (γ ∘ γ′) ≊ (δ ∘ δ′)
