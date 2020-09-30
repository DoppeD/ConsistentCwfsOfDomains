{-# OPTIONS --safe #-}

open import Base.Core

module Scwf.DomainScwf.ArrowStructure.lam.Relation (𝐴 𝐵 : Ty) where

open import Base.FinFun
open import Base.Variables hiding (𝐴 ; 𝐵)
open import NbhSys.Definition
open import Scwf.DomainScwf.Appmap.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Definition 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.ConFinFun 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Instance

data [_]_lam↦_ (𝑡 : tAppmap (𝐴 :: Γ) [ 𝐵 ]) :
               Valuation Γ → Valuation [ ArrNbhSys 𝐴 𝐵 ] →
               Set where
  lam↦-intro₁ : ∀ {𝑥} → [ 𝑡 ] 𝑥 lam↦ ⟪ ⊥ₑ ⟫
  lam↦-intro₂ : {𝑥 : Valuation Γ} → {𝑓 : NbhFinFun 𝐴 𝐵} →
                (con𝑓 : ConFinFun 𝑓) →
                (∀ {x y} → < x , y > ∈ 𝑓 →
                [ 𝑡 ] ⟪ x , 𝑥 ⟫ ↦ ⟪ y ⟫) →
                [ 𝑡 ] 𝑥 lam↦ ⟪ 𝐹 𝑓 con𝑓 ⟫
