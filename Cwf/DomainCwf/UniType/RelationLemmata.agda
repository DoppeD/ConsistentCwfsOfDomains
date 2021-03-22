{-# OPTIONS --safe --sized-types #-}

module Cwf.DomainCwf.UniType.RelationLemmata where

open import Base.Core
open import Cwf.DomainCwf.UniType.AxiomProofs
open import Cwf.DomainCwf.UniType.Consistency
open import Cwf.DomainCwf.UniType.Definition
open import Cwf.DomainCwf.UniType.FinFun
open import Cwf.DomainCwf.UniType.Relation

grow-⊑ : ∀ {i} → {f g h : FinFun {i}} → g ⊆ h →
        (∀ {u v} → (u , v) ∈ f → ⊑-proof g u v) →
        ∀ {u v} → (u , v) ∈ f → ⊑-proof h u v
grow-⊑ g⊆h p uv∈f with (p uv∈f)
... | record { sub = sub ; sub⊆g = sub⊆g ; pre⊑u = pre⊑u ; v⊑post = v⊑post }
  = record
      { sub = sub
      ; sub⊆g = ⊆-trans sub⊆g g⊆h
      ; pre⊑u = pre⊑u
      ; v⊑post = v⊑post
      }

shrink-⊑ : ∀ {i} → {f f′ g : FinFun {i}} → f′ ⊆ f → (F f) ⊑ (F g) →
           ∀ {u v} → (u , v) ∈ f′ → ⊑-proof g u v
shrink-⊑ f′⊆f (⊑-F conf cong p) uv∈f′ = p (f′⊆f uv∈f′)

⊑-⊔-lemma₁ : ∀ {i} → {u v w : Nbh {i}} → u ⊑ v → con (v ⊔ w) → u ⊑ (v ⊔ w)
⊑-⊔-lemma₁ (⊑-bot _) convw = ⊑-bot convw
⊑-⊔-lemma₁ {w = ⊥} ⊑-0 _ = ⊑-0
⊑-⊔-lemma₁ {w = 0ᵤ} ⊑-0 _ = ⊑-0
⊑-⊔-lemma₁ {w = ⊥} (⊑-s u⊑v) _ = ⊑-s u⊑v
⊑-⊔-lemma₁ {w = s _} (⊑-s u⊑v) convw = ⊑-s (⊑-⊔-lemma₁ u⊑v convw)
⊑-⊔-lemma₁ {w = ⊥} ⊑-ℕ _ = ⊑-ℕ
⊑-⊔-lemma₁ {w = ℕ} ⊑-ℕ _ = ⊑-ℕ
⊑-⊔-lemma₁ {w = ⊥} (⊑-F conf cong p) _ = ⊑-F conf cong p
⊑-⊔-lemma₁ {w = F h} (⊑-F conf cong p) conuw = ⊑-F conf conuw (grow-⊑ ∪-lemma₃ p)
⊑-⊔-lemma₁ {w = ⊥} (⊑-rfl u⊑v) _ = ⊑-rfl u⊑v
⊑-⊔-lemma₁ {w = refl _} (⊑-rfl u⊑v) convw = ⊑-rfl (⊑-⊔-lemma₁ u⊑v convw)
⊑-⊔-lemma₁ {w = ⊥} (⊑-I U⊑U′ u⊑u′ v⊑v′) _ = ⊑-I U⊑U′ u⊑u′ v⊑v′
⊑-⊔-lemma₁ {w = I _ _ _} (⊑-I U⊑U′ u⊑u′ v⊑v′) (conUU′ , (conuu′ , convv′))
  = ⊑-I (⊑-⊔-lemma₁ U⊑U′ conUU′) (⊑-⊔-lemma₁ u⊑u′ conuu′) (⊑-⊔-lemma₁ v⊑v′ convv′)
⊑-⊔-lemma₁ {w = ⊥} (⊑-Π u⊑v f⊑g) _ = ⊑-Π u⊑v f⊑g
⊑-⊔-lemma₁ {w = Π _ _} (⊑-Π u⊑v f⊑g) _ with (orderOnlyCon f⊑g)
⊑-⊔-lemma₁ {w = Π _ _} (⊑-Π u⊑v (⊑-F _ _ p)) (convw , congh) | (conf , _) =
  ⊑-Π (⊑-⊔-lemma₁ u⊑v convw) (⊑-F conf congh (grow-⊑ ∪-lemma₃ p))
⊑-⊔-lemma₁ {w = ⊥} ⊑-𝒰 _ = ⊑-𝒰
⊑-⊔-lemma₁ {w = 𝒰} ⊑-𝒰 _ = ⊑-𝒰

⊑-⊔-lemma₂ : ∀ {i} → {u v w : Nbh {i}} → u ⊑ w → con (v ⊔ w) → u ⊑ (v ⊔ w)
⊑-⊔-lemma₂ (⊑-bot _) conuw = ⊑-bot conuw
⊑-⊔-lemma₂ {v = ⊥} ⊑-0 _ = ⊑-0
⊑-⊔-lemma₂ {v = 0ᵤ} ⊑-0 _ = ⊑-0
⊑-⊔-lemma₂ {v = ⊥} (⊑-s u⊑w) _ = ⊑-s u⊑w
⊑-⊔-lemma₂ {v = s _} (⊑-s u⊑w) conuw = ⊑-s (⊑-⊔-lemma₂ u⊑w conuw)
⊑-⊔-lemma₂ {v = ⊥} ⊑-ℕ _ = ⊑-ℕ
⊑-⊔-lemma₂ {v = ℕ} ⊑-ℕ _ = ⊑-ℕ
⊑-⊔-lemma₂ {v = ⊥} (⊑-F conf cong p) conuw = ⊑-F conf cong p
⊑-⊔-lemma₂ {v = F _} (⊑-F conf cong p) conuw = ⊑-F conf conuw (grow-⊑ ∪-lemma₄ p)
⊑-⊔-lemma₂ {v = ⊥} (⊑-rfl u⊑w) _ = ⊑-rfl u⊑w
⊑-⊔-lemma₂ {v = refl _} (⊑-rfl u⊑w) conuw = ⊑-rfl (⊑-⊔-lemma₂ u⊑w conuw)
⊑-⊔-lemma₂ {v = ⊥} (⊑-I U⊑U″ u⊑u″ v⊑v″) _ = ⊑-I U⊑U″ u⊑u″ v⊑v″
⊑-⊔-lemma₂ {v = I _ _ _} (⊑-I U⊑U″ u⊑u″ v⊑v″) (conU′U″ , (conu′u″ , conv′v″))
  = ⊑-I (⊑-⊔-lemma₂ U⊑U″ conU′U″) (⊑-⊔-lemma₂ u⊑u″ conu′u″) (⊑-⊔-lemma₂ v⊑v″ conv′v″)

⊑-⊔-lemma₂ {v = ⊥} (⊑-Π u⊑w f⊑h) conuw = ⊑-Π u⊑w f⊑h
⊑-⊔-lemma₂ {v = Π _ _} (⊑-Π u⊑w f⊑h) conuw with (orderOnlyCon f⊑h)
⊑-⊔-lemma₂ {v = Π _ _} (⊑-Π u⊑w (⊑-F _ _ p)) (conuw , confh) | (conf , _)
  = ⊑-Π (⊑-⊔-lemma₂ u⊑w conuw) (⊑-F conf confh (grow-⊑ ∪-lemma₄ p))
⊑-⊔-lemma₂ {v = ⊥} ⊑-𝒰 _ = ⊑-𝒰
⊑-⊔-lemma₂ {v = 𝒰} ⊑-𝒰 _ = ⊑-𝒰

⊑-⊔-lemma₃ : ∀ {i} → {u v u′ v′ : Nbh {i}} → u ⊑ u′ → v ⊑ v′ → con (u ⊔ v) → con (u′ ⊔ v′) → (u ⊔ v) ⊑ (u′ ⊔ v′)
⊑-⊔-lemma₃ u⊑u′ v⊑v′ conuv conu′v′
  = ⊑-⊔ (⊑-⊔-lemma₁ u⊑u′ conu′v′) (⊑-⊔-lemma₂ v⊑v′ conu′v′) conuv
