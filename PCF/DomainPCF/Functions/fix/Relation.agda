{-# OPTIONS --safe #-}

open import Base.Core

module PCF.DomainPCF.Functions.fix.Relation (𝐴 : Ty) where

open import Base.FinFun
open import Base.Variables hiding (𝐴)
open import NbhSys.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.ArrowStructure.NbhSys.ConFinFun 𝐴 𝐴
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Definition
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Instance

-- Example: From z = {(⊥, s ⊥), (s ⊥, s 0)} we can construct
-- proofs of derFrom⊥ z ⊥, derFrom⊥ z (s ⊥), and
-- derFrom⊥ z (s 0). Thus we have in the _fix↦_-relation
-- the following pairs (among others):
-- (z, ⊥), (z (s ⊥), (z (s 0))
data derFrom⊥ (𝑔 : NbhSys.Nbh (𝐴 ⇒ 𝐴)) :
              NbhSys.Nbh 𝐴 → Set where
  df⊥-intro₁ : ∀ {x} → [ 𝐴 ] x ⊑ (NbhSys.⊥ 𝐴) → derFrom⊥ 𝑔 x
  df⊥-intro₂ : ∀ {x y} → derFrom⊥ 𝑔 x →
               [ 𝐴 ⇒ 𝐴 ] 𝐹 ((x , y) ∷ ∅) singletonIsCon ⊑ 𝑔 →
               derFrom⊥ 𝑔 y

data _fix↦_ : Valuation Γ → ArrNbh (𝐴 ⇒ 𝐴) 𝐴 → Set where
  fix↦-intro₁ : {𝑥 : Valuation Γ} → 𝑥 fix↦ ⊥ₑ
  fix↦-intro₂ : {𝑥 : Valuation Γ} → ∀ {𝑓 con𝑓} →
                (∀ {𝑔 fp} → (𝑔 , fp) ∈ 𝑓 → derFrom⊥ 𝑔 fp) →
                𝑥 fix↦ (𝐹 𝑓 con𝑓)
