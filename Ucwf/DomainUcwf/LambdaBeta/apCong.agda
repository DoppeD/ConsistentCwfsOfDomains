{-# OPTIONS --safe --sized-types #-}

module Ucwf.DomainUcwf.LambdaBeta.apCong where

open import Appmap.Equivalence
open import Base.Variables
open import Ucwf.DomainUcwf.Appmap.Definition
open import Ucwf.DomainUcwf.Appmap.Valuation
open import Ucwf.DomainUcwf.LambdaBeta.ap.Instance
open import Ucwf.DomainUcwf.LambdaBeta.ap.Relation
open import Ucwf.DomainUcwf.UniType.Definition

private
  variable
    𝑡 𝑡′ 𝑢 𝑢′ : uAppmap n 1

apCongLemma : 𝑡 ≼ 𝑡′ → 𝑢 ≼ 𝑢′ →
              ∀ {𝑥 𝑦} → [ ap 𝑡 𝑢 ] 𝑥 ↦ 𝑦 →
              [ ap 𝑡′ 𝑢′ ] 𝑥 ↦ 𝑦
apCongLemma _ _ {𝑦 = ⟪ ⊥ᵤ ,, ⟪⟫ ⟫} _ = ap↦-intro₁
apCongLemma (≼-intro 𝑡≼𝑡′) (≼-intro 𝑢≼𝑢′) {𝑦 = ⟪ λᵤ 𝑓 ,, ⟪⟫ ⟫}
  (ap↦-intro₂ 𝑡𝑥↦𝑔 𝑢𝑥↦z z𝑓⊑𝑔)
  = ap↦-intro₂ (𝑡≼𝑡′ 𝑡𝑥↦𝑔) (𝑢≼𝑢′ 𝑢𝑥↦z) z𝑓⊑𝑔

apCong : 𝑡 ≈ 𝑡′ → 𝑢 ≈ 𝑢′ → ap 𝑡 𝑢 ≈ ap 𝑡′ 𝑢′
apCong (≈-intro 𝑡≼𝑡′ 𝑡′≼𝑡) (≈-intro 𝑢≼𝑢′ 𝑢′≼𝑢)
  = ≈-intro (≼-intro (apCongLemma 𝑡≼𝑡′ 𝑢≼𝑢′))
            (≼-intro (apCongLemma 𝑡′≼𝑡 𝑢′≼𝑢))