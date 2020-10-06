{-# OPTIONS --safe #-}

open import Base.Core
open import NbhSys.Definition

module Appmap.PrincipalIdeal.Relation
  (𝐴 𝐵 : Ty) (gen : NbhSys.Nbh 𝐵) where

open import Base.Variables hiding (𝐴 ; 𝐵)

data _ideal↦_ : NbhSys.Nbh 𝐴 → NbhSys.Nbh 𝐵 → Set where
  ideal↦-intro : ∀ {x y} → [ 𝐵 ] y ⊑ gen → x ideal↦ y
