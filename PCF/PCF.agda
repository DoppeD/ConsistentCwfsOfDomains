module PCF.PCF where

open import Base.Variables
open import Scwf.Plain
open import Scwf.ProductArrow

open import Agda.Builtin.Nat renaming (Nat to AgdaNat ; suc to AgdaSuc)
  hiding (zero)

record PCF : Set₂ where
  field
    productArrow-scwf : ProductArrow-scwf
  open ProductArrow-scwf productArrow-scwf public
  field
    -- Types
    Nat : Ty
    Bool : Ty

    -- Terms
    num : ∀ {m Γ} → (n : AgdaNat) → Tm {m} Γ Nat
    true : ∀ {m Γ} → Tm {m} Γ Bool
    false : ∀ {m Γ} → Tm {m} Γ Bool

    -- Functions
    suc : ∀ {m Γ} → Tm {m} Γ (Nat ⇒ Nat)
    pred : ∀ {m Γ} → Tm {m} Γ (Nat ⇒ Nat)
    zero : ∀ {m Γ} → Tm {m} Γ (Nat ⇒ Nat)
    iszero : ∀ {m Γ} → Tm {m} Γ (Nat ⇒ Bool)
    fix : ∀ {m Γ} → Tm {m} Γ ((Nat ⇒ Nat) ⇒ Nat)

    -- Equations
    suceq : ∀ {m Γ} → ∀ n →
            ap {m} {Γ} suc (num n) ≈ num (AgdaSuc n)
    predeq : ∀ {m Γ} → ∀ n →
             ap {m} {Γ} pred (num (AgdaSuc n)) ≈ num n
    zeroeq : ∀ {m Γ} → ∀ n →
             ap {m} {Γ} zero (num n) ≈ num 0
    iszeroeq₁ : ∀ {m Γ} → ap {m} {Γ} iszero (num 0) ≈ true
    iszeroeq₂ : ∀ {m Γ} → ∀ n →
                ap {m} {Γ} iszero (num (AgdaSuc n)) ≈ false
    fixeq : ∀ {m Γ} → ∀ f →
            ap {m} {Γ} fix f ≈ ap f (ap fix f)
