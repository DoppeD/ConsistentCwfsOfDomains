{-# OPTIONS --safe #-}

module Appmap.Lemmata where

open import Appmap.Definition
open import NbhSys.Definition
open import NbhSys.Lemmata

private
  variable
    𝒟 𝒟′ : NbhSys

appmapLemma₁ : {γ : Appmap 𝒟 𝒟′} → ∀ {x y z} →
               (con : NbhSys.Con 𝒟 x y) →
               [ γ ] x ↦ z → [ γ ] ([ 𝒟 ] x ⊔ y [ con ]) ↦ z
appmapLemma₁ {𝒟} {γ = γ} con γx↦z
  = Appmap.↦-mono γ (NbhSys.⊑-⊔-fst 𝒟 con) γx↦z

appmapLemma₂ : {γ : Appmap 𝒟 𝒟′} → ∀ {x y z} →
               (con : NbhSys.Con 𝒟 x y) →
               [ γ ] y ↦ z → [ γ ] ([ 𝒟 ] x ⊔ y [ con ]) ↦ z
appmapLemma₂ {𝒟} {γ = γ} con γy↦z
  = Appmap.↦-mono γ (NbhSys.⊑-⊔-snd 𝒟 con) γy↦z

appmapLemma₃ : {γ : Appmap 𝒟 𝒟′} → ∀ x y z w →
               (conxy : NbhSys.Con 𝒟 x y) →
               (conzw : NbhSys.Con 𝒟′ z w) →
               [ γ ] x ↦ z → [ γ ] y ↦ w →
               [ γ ] ([ 𝒟 ] x ⊔ y [ conxy ]) ↦ ([ 𝒟′ ] z ⊔ w [ conzw ])
appmapLemma₃ {γ = γ} x y z w conxy conzw γx↦z γy↦w
  = Appmap.↦-↑directed γ γ⊔↦z γ⊔↦w conzw
  where γ⊔↦z = appmapLemma₁ {γ = γ} conxy γx↦z
        γ⊔↦w = appmapLemma₂ {γ = γ} conxy γy↦w
