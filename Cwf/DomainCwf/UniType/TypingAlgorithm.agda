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

record apSet {i : Size} (f : FinFun {i}) (u : Nbh {i}) : Set where
  field
    ⊑proof : ⊑-proof f u ⊥
    isLargest : {⊑proof′ : ⊑-proof f u ⊥} → pre (⊑-proof.sub ⊑proof′) ⊑ pre (⊑-proof.sub ⊑proof)

data _Type : ∀ {i} → Nbh {i} → Set
data _˸_ : ∀ {i} → Nbh {i} → Nbh {i} → Set

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
  F:Π : ∀ {U g f} →
        (∀ {u v} → (u , v) ∈ f → u ˸ U) →
        (∀ {u v} → (u , v) ∈ f → (apset : apSet g u) → v ˸ post (⊑-proof.sub (apSet.⊑proof apset))) →
        (F f) ˸ (Π U g)
  refl:I : ∀ {i} → {U u : Nbh {i}} → U Type → u ˸ U → refl u ˸ I U u u
  Π:𝒰 : ∀ {U f} → U ˸ 𝒰 →
        (∀ {u V} → (u , V) ∈ f → (u ˸ U) ∧ (V ˸ 𝒰)) →
        (Π U f) ˸ 𝒰
  ℕ:𝒰 : ∀ {i} → ℕ {i} ˸ 𝒰
