{-# OPTIONS --safe #-}

open import Base.Variables
open import Appmap.Definition

module Appmap.Composition.AxiomProofs
  (δ : Appmap 𝐵 𝐶) (γ : Appmap 𝐴 𝐵) where

open import Appmap.Composition.Relation
open import Base.Core
open import NbhSys.Definition
open import NbhSys.Lemmata

∘↦-mono : ∀ {x y z} → [ 𝐴 ] x ⊑ y →
          _∘↦_ δ γ x z → _∘↦_ δ γ y z
∘↦-mono {y = y} {z} x⊑y (∘↦-intro γx↦y δy↦z)
  = ∘↦-intro (Appmap.↦-mono γ x⊑y γx↦y) δy↦z

∘↦-bottom : ∀ {x} → _∘↦_ δ γ x (NbhSys.⊥ 𝐶)
∘↦-bottom {x = x}
  = ∘↦-intro (Appmap.↦-bottom γ) (Appmap.↦-bottom δ)

∘↦-↓closed : ∀ {x z w} → [ 𝐶 ] z ⊑ w →
             _∘↦_ δ γ x w → _∘↦_ δ γ x z
∘↦-↓closed {x = x} {z} z⊑w (∘↦-intro γx↦y δy↦w)
  = ∘↦-intro γx↦y (Appmap.↦-↓closed δ z⊑w δy↦w)

∘↦-↑directed : ∀ {x z w} → _∘↦_ δ γ x z → _∘↦_ δ γ x w →
               ∀ conzw →
               _∘↦_ δ γ x ([ 𝐶 ] z ⊔ w [ conzw ])
∘↦-↑directed  (∘↦-intro γx↦y δy↦z)
  (∘↦-intro γx↦y' δy'↦w) conzw
  = ∘↦-intro γx↦y⊔y' δy⊔y'↦z⊔w
    where conyy′ = Appmap.↦-con γ γx↦y γx↦y' (conRefl 𝐴)
          γx↦y⊔y' = Appmap.↦-↑directed γ γx↦y γx↦y' conyy′
          y⊑y⊔y′ = NbhSys.⊑-⊔-fst 𝐵 conyy′
          δy⊔y'↦z = Appmap.↦-mono δ y⊑y⊔y′ δy↦z
          y′⊑y⊔y′ = NbhSys.⊑-⊔-snd 𝐵 conyy′
          δy⊔y'↦w = Appmap.↦-mono δ y′⊑y⊔y′ δy'↦w
          δy⊔y'↦z⊔w = Appmap.↦-↑directed δ δy⊔y'↦z δy⊔y'↦w conzw

∘↦-con : ∀ {x y x′ y′} → _∘↦_ δ γ x y → _∘↦_ δ γ x′ y′ →
         NbhSys.Con 𝐴 x x′ → NbhSys.Con 𝐶 y y′
∘↦-con {y = y} {y′ = y′}
  (∘↦-intro γx↦z δz↦y) (∘↦-intro γx′↦z′ δz′↦y′) conxx′
  = Appmap.↦-con δ δz↦y δz′↦y′ conzz′
  where conzz′ = Appmap.↦-con γ γx↦z γx′↦z′ conxx′
