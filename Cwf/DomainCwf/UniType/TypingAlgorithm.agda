{-# OPTIONS --safe --sized-types #-}

module Cwf.DomainCwf.UniType.TypingAlgorithm where

open import Base.Core
open import Cwf.DomainCwf.UniType.Consistency
open import Cwf.DomainCwf.UniType.ConsistencyLemmata
open import Cwf.DomainCwf.UniType.FinFun
open import Cwf.DomainCwf.UniType.Definition
open import Cwf.DomainCwf.UniType.Relation

open import Agda.Builtin.Sigma
open import Agda.Builtin.Size

data _Type : ∀ {i} → Nbh {i} → Set
data _˸_ : ∀ {i} → Nbh {i} → Nbh {i} → Set
record apSet {i : Size} (f : FinFun {i}) (u v : Nbh {i}) : Set

data _Type where
  isType-I : ∀ {i} → {U u u′ : Nbh {i}} → U Type → u ˸ U → u′ ˸ U → (I U u u′) Type
  isType-ℕ : ∀ {i} → ℕ {i} Type
  isType-𝒰 : ∀ {i} → 𝒰 {i} Type
  isType-Π : ∀ {i} → {U : Nbh {i}} → {f : FinFun {i}} → U Type →
             (∀ {u V} → (u , V) ∈ f → (u ˸ U) ⊠ (V Type)) →
             (Π U f) Type

data _˸_ where
  ⊥:U : ∀ {i} → {U : Nbh {i}} → U Type → ⊥ ˸ U
  0:ℕ : ∀ {i} → 0ᵤ {i} ˸ ℕ
  s:N : ∀ {i} → {u : Nbh {i}} → u ˸ ℕ → s u ˸ ℕ
  F:Π : ∀ {i} → {U : Nbh {i}} → {g f : FinFun {i}} →
        (∀ {u v} → (u , v) ∈ f → u ˸ U) →
        (∀ {u v} → (u , v) ∈ f → apSet g u v) →
        (F f) ˸ (Π U g)
  refl:I : ∀ {i} → {U u : Nbh {i}} → U Type → u ˸ U → refl u ˸ I U u u
  I:𝒰 : ∀ {i} → {U u v : Nbh {i}} → U ˸ 𝒰 → u ˸ U → v ˸ U → I U u v ˸ 𝒰
  Π:𝒰 : ∀ {i} → {U : Nbh {i}} → {f : FinFun {i}} →  U ˸ 𝒰 →
        (∀ {u V} → (u , V) ∈ f → (u ˸ U) ⊠ (V ˸ 𝒰)) →
        (Π U f) ˸ 𝒰
  ℕ:𝒰 : ∀ {i} → ℕ {i} ˸ 𝒰

record apSet {i} f u v where
  inductive
  field
    ⊑proof : ⊑-proof f u ⊥
    isLargest : {⊑proof′ : ⊑-proof f u ⊥} → pre (⊑-proof.sub ⊑proof′) ⊑ pre (⊑-proof.sub ⊑proof)
    v:post : v ˸ post (⊑-proof.sub ⊑proof)
