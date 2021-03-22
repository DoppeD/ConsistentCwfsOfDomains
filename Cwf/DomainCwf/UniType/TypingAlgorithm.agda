module Cwf.DomainCwf.UniType.TypingAlgorithm where

open import Base.Core
open import Cwf.DomainCwf.UniType.Consistency
open import Cwf.DomainCwf.UniType.ConsistencyLemmata
open import Cwf.DomainCwf.UniType.FinFun
open import Cwf.DomainCwf.UniType.Definition
open import Cwf.DomainCwf.UniType.Relation

open import Agda.Builtin.Sigma

data _Type : Nbh → Set
data _⦂_ : Nbh → Nbh → Set

data _Type where
  isType-ℕ : ℕ Type
  isType-𝒰 : 𝒰 Type
  isType-Π : ∀ {U f} → U Type →
             (∀ {u V} → (u , V) ∈ f → (u ⦂ U) ∧ (V Type)) →
             (Π U f) Type

data _⦂_ where
  ⊥:U : ∀ {U} → U Type → ⊥ ⦂ U
  0:ℕ : 0ᵤ ⦂ ℕ
  s:N : ∀ {u} → u ⦂ ℕ → s u ⦂ ℕ
  F:Π : ∀ {U g f} →
        (∀ {u v} → (u , v) ∈ f → u ⦂ U) →
        (∀ {u v} → (u , v) ∈ f → Σ (⊑-proof g u ⊥) λ uv⊑g → v ⦂ post (⊑-proof.sub uv⊑g)) →
        (F f) ⦂ (Π U g)
  refl:I : ∀ {U u} → U Type → u ⦂ U → refl u ⦂ I U u u
  Π:𝒰 : ∀ {U f} → U ⦂ 𝒰 →
        (∀ {u V} → (u , V) ∈ f → (u ⦂ U) ∧ (V ⦂ 𝒰)) →
        (Π U f) ⦂ 𝒰
  ℕ:𝒰 : ℕ ⦂ 𝒰

-- We want v ⦂ F (u).
-- ⊑-proof g u ⊥ gives us ONE preable (and postable) subset of g, but we want the largest possible such subset.
-- Is what we have here equivalent?
-- First, does the fact that v ⦂ post sub for some sub ⊆ g imply that v ⦂ post Ω for the largest such Ω ⊆ g?
-- If not, we should be able to define this set Ω.
-- Second, does the converse hold? Does it have to?
