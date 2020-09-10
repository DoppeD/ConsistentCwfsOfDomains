{-# OPTIONS --safe #-}

module Scwf.Plain where

open import Base.Core using (Rel ; IsEquivalence)
open import Base.Variables

open import Agda.Builtin.Nat

record Scwf : Set₂ where
  field
    Ty : Set₁
    Ctx : Nat → Set₁
    Tm : Ctx n → Ty → Set₁
    Sub : Ctx m → Ctx n → Set₁

    _≈_ : ∀ {Γ 𝐴} → Rel (Tm {n} Γ 𝐴)
    _≊_ : ∀ {Γ Δ} → Rel (Sub {m} {n} Γ Δ)

    isEquivT : ∀ {Γ 𝐴} → IsEquivalence (_≈_ {n} {Γ} {𝐴})
    isEquivS : ∀ {Γ Δ} → IsEquivalence (_≊_ {m} {n} {Γ} {Δ})

    ◇ : Ctx zero

    _•_ : Ctx n → Ty → Ctx (suc n)

    q : (Γ : Ctx n) → (𝐴 : Ty) → Tm (Γ • 𝐴) 𝐴
    _[_] : ∀ {𝐴 Γ Δ} → Tm {n} Δ 𝐴 → Sub {m} Γ Δ → Tm Γ 𝐴

    id : (Γ : Ctx n) → Sub Γ Γ
    _∘_ : ∀ {Γ Δ Θ} → Sub {n} {o} Δ Θ → Sub {m} Γ Δ → Sub Γ Θ
    ⟨⟩ : {Γ : Ctx n} → Sub Γ ◇
    ⟨_,_⟩ : ∀ {Γ Δ 𝐴} → Sub {n} {m} Δ Γ → Tm Δ 𝐴 → Sub Δ (Γ • 𝐴)
    p : (Γ : Ctx n) → (𝐴 : Ty) → Sub (Γ • 𝐴) Γ

    idL : ∀ {Γ Δ} → (γ : Sub {n} {m} Δ Γ) → ((id Γ) ∘ γ) ≊ γ
    idR : ∀ {Γ Δ} → (γ : Sub {n} {m} Δ Γ) → (γ ∘ (id Δ)) ≊ γ
    subAssoc : ∀ {Γ Δ Θ Λ} → (γ : Sub {m} {n} Γ Δ) →
               (δ : Sub {n} {o} Δ Θ) → (θ : Sub {o} {r} Θ Λ) →
               ((θ ∘ δ) ∘ γ) ≊ (θ ∘ (δ ∘ γ))

    idSub : ∀ {Γ 𝐴} → (𝑡 : Tm {n} Γ 𝐴) → (𝑡 [ id Γ ]) ≈ 𝑡
    compSub : ∀ {Γ Δ Θ 𝐴} → (𝑡 : Tm {n} Δ 𝐴) →
              (γ : Sub {m} Γ Δ) → (δ : Sub {o} Θ Γ) →
              (𝑡 [ γ ∘ δ ]) ≈ ((𝑡 [ γ ]) [ δ ])

    id₀ : id ◇ ≊ ⟨⟩
    <>-zero : ∀ {Γ Δ} → (γ : Sub {m} {n} Γ Δ) → (⟨⟩ ∘ γ) ≊ ⟨⟩

    pCons : ∀ {𝐴 Γ Δ} → (γ : Sub {n} {m} Δ Γ) → (𝑡 : Tm Δ 𝐴) →
            ((p Γ 𝐴) ∘ ⟨ γ , 𝑡 ⟩) ≊ γ
    qCons : ∀ {𝐴 Γ Δ} → (γ : Sub {n} {m} Δ Γ) → (𝑡 : Tm Δ 𝐴) →
            ((q Γ 𝐴) [ ⟨ γ , 𝑡 ⟩ ]) ≈ 𝑡
    idExt : ∀ {𝐴 Γ} → (id (_•_ {m} Γ 𝐴)) ≊ ⟨ p Γ 𝐴 , q Γ 𝐴 ⟩
    compExt : ∀ {Γ Δ 𝐴} → (𝑡 : Tm Δ 𝐴) →
              (γ : Sub {n} {m} Δ Γ) → (δ : Sub Γ Δ) →
              (⟨ γ , 𝑡 ⟩ ∘ δ) ≊ ⟨ γ ∘ δ , 𝑡 [ δ ] ⟩

    subCong : ∀ {𝐴 Γ Δ} → {𝑡 𝑡′ : Tm {m} Γ 𝐴} →
              {γ γ′ : Sub {n} Δ Γ} → 𝑡 ≈ 𝑡′ →
              γ ≊ γ′ → (𝑡 [ γ ]) ≈ (𝑡′ [ γ′ ])
    <,>-cong : ∀ {𝐴 Γ Δ} → {𝑡 𝑡′ : Tm {m} Γ 𝐴} →
               {γ γ′ : Sub {m} {n} Γ Δ} → 𝑡 ≈ 𝑡′ →
               γ ≊ γ′ → ⟨ γ , 𝑡 ⟩ ≊ ⟨ γ′ , 𝑡′ ⟩
    ∘-cong : ∀ {Γ Δ Θ} → {γ δ : Sub {n} {o} Δ Θ} →
             {γ′ δ′ : Sub {m} Γ Δ} → γ ≊ δ →
             γ′ ≊ δ′ → (γ ∘ γ′) ≊ (δ ∘ δ′)
