module PCF.PCF where

open import Base.Variables
open import Scwf.Plain
open import Scwf.ProductArrow

open import Agda.Builtin.Nat renaming (Nat to AgdaNat)

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

    -- Equations
