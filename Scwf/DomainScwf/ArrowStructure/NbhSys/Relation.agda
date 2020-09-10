{-# OPTIONS --safe #-}

open import Base.Core

module Scwf.DomainScwf.ArrowStructure.NbhSys.Relation
  (𝐴 𝐵 : Ty) where

open import Base.FinFun
open import NbhSys.Definition
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Definition 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.PrePost 𝐴 𝐵

record ⊑ₑ-proof (𝑓 : NbhFinFun 𝐴 𝐵) (x : NbhSys.Nbh 𝐴)
                (y : NbhSys.Nbh 𝐵) :
                Set where
  field
    sub : NbhFinFun 𝐴 𝐵
    y⊑post : [ 𝐵 ] y ⊑ (post sub)
    pre⊑x : [ 𝐴 ] (pre sub) ⊑ x
    sub⊆𝑓 : sub ⊆ 𝑓

data _⊑ₑ_ : ArrNbh → ArrNbh → Set where
  ⊑ₑ-intro₁ : ∀ {x} → ⊥ₑ ⊑ₑ x
  ⊑ₑ-intro₂ : ∀ 𝑓 𝑓′ →
              (∀ x y → < x , y > ∈ 𝑓 → ⊑ₑ-proof 𝑓′ x y) →
              (𝐹 𝑓) ⊑ₑ (𝐹 𝑓′)
