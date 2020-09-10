{-# OPTIONS --safe #-}

module Appmap.Lemmata where

open import Appmap.Definition
open import NbhSys.Definition
open import NbhSys.Lemmata

private
  variable
    𝒟 𝒟′ : NbhSys

appmapLemma₁ : {γ : Appmap 𝒟 𝒟′} → ∀ {x y z} → [ γ ] x ↦ z →
               (con : NbhSys.Con 𝒟 x y) → [ γ ] ([ 𝒟 ] x ⊔ y [ con ]) ↦ z
appmapLemma₁ {𝒟 = 𝒟} {γ = γ} γx↦z con
  = Appmap.↦-mono γ (NbhSys.⊑-⊔-fst 𝒟 con) γx↦z

appmapLemma₂ : {γ : Appmap 𝒟 𝒟′} → ∀ {x y z} → [ γ ] y ↦ z →
               (con : NbhSys.Con 𝒟 x y) → [ γ ] ([ 𝒟 ] x ⊔ y [ con ]) ↦ z
appmapLemma₂ {𝒟 = 𝒟}{γ = γ} γy↦z con
  = Appmap.↦-mono γ (NbhSys.⊑-⊔-snd 𝒟 con) γy↦z

appmapLemma₃ : {γ : Appmap 𝒟 𝒟′} → ∀ x y z w →
               [ γ ] x ↦ z → [ γ ] y ↦ w →
               (conxy : NbhSys.Con 𝒟 x y) → (conzw : NbhSys.Con 𝒟′ z w) →
               [ γ ] ([ 𝒟 ] x ⊔ y [ conxy ]) ↦ ([ 𝒟′ ] z ⊔ w [ conzw ])
appmapLemma₃ {γ = γ} x y z w γx↦z γy↦w conxy conzw
  = Appmap.↦-↑directed γ γ⊔↦z γ⊔↦w conzw
  where γ⊔↦z = appmapLemma₁ {γ = γ} γx↦z conxy
        γ⊔↦w = appmapLemma₂ {γ = γ} γy↦w conxy
