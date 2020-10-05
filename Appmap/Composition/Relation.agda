{-# OPTIONS --safe #-}

module Appmap.Composition.Relation where

open import Appmap.Definition
open import Base.Core
open import Base.Variables
open import NbhSys.Definition

data _∘↦_ (δ : Appmap 𝐵 𝐶) (γ : Appmap 𝐴 𝐵) :
          NbhSys.Nbh 𝐴 → NbhSys.Nbh 𝐶 → Set where
  ∘↦-intro : ∀ {x y z} → [ γ ] x ↦ y → [ δ ] y ↦ z →
             _∘↦_ δ γ x z
