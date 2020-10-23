{-# OPTIONS --safe #-}

module PCF.PCF where

open import Base.Variables
open import Scwf.Plain
open import Scwf.ProductArrow

record PCF : Set₂ where
  field
    productArrow-scwf : ProductArrow-scwf
  open ProductArrow-scwf productArrow-scwf public
  field
    -- Types
    Nat : Ty
    Bool : Ty

    -- Terms
    zero : ∀ {m Γ} → Tm {m} Γ Nat
    true : ∀ {m Γ} → Tm {m} Γ Bool
    false : ∀ {m Γ} → Tm {m} Γ Bool

    -- Functions
    suc : ∀ {m Γ} → Tm {m} Γ (Nat ⇒ Nat)
    pred : ∀ {m Γ} → Tm {m} Γ (Nat ⇒ Nat)
    iszero : ∀ {m Γ} → Tm {m} Γ (Nat ⇒ Bool)
    fix : ∀ {m Γ 𝐴} → Tm {m} Γ ((𝐴 ⇒ 𝐴) ⇒ 𝐴)

    -- Equations
    predeq : ∀ {m Γ n} →
             ap {m} {Γ} pred (ap suc n) ≈ n
    iszeroeq₁ : ∀ {m Γ} →
                ap {m} {Γ} iszero zero ≈ true
    iszeroeq₂ : ∀ {m Γ n} →
                ap {m} {Γ} iszero (ap suc n) ≈ false
    fixeq : ∀ {m Γ 𝐴} → (f : Tm {m} Γ (𝐴 ⇒ 𝐴)) →
            ap fix f ≈ ap f (ap fix f)
