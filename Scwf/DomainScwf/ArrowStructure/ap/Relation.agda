{-# OPTIONS --safe #-}

open import Base.Core

module Scwf.DomainScwf.ArrowStructure.ap.Relation (𝐴 𝐵 : Ty) where

open import Base.FinFun
open import Base.Variables hiding (𝐴 ; 𝐵)
open import NbhSys.Definition
open import Scwf.DomainScwf.Appmap.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Instance
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Definition
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Instance

data [_,_]_ap↦_ (𝑡 : Term Γ (𝐴 ⇒ 𝐵))
                (𝑢 : Term Γ 𝐴) (𝑥 : Valuation Γ) :
                NbhSys.Nbh 𝐵 → Set where
  ap↦-intro₁ : ∀ {x} → [ 𝐵 ] x ⊑ NbhSys.⊥ 𝐵 →
               [ 𝑡 , 𝑢 ] 𝑥 ap↦ x
  ap↦-intro₂ : ∀ {x y 𝑓} con𝑓 conxy →
               [ 𝑡 ] 𝑥 ↦ (𝐹 𝑓 con𝑓) → [ 𝑢 ] 𝑥 ↦ x →
               [ 𝐴 ⇒ 𝐵 ] (𝐹 ((x , y) ∷ ∅) conxy) ⊑ (𝐹 𝑓 con𝑓) →
               [ 𝑡 , 𝑢 ] 𝑥 ap↦ y
