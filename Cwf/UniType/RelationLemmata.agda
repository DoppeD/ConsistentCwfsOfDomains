module Cwf.UniType.RelationLemmata where

open import Base.Core
open import Cwf.UniType.AxiomProofs
open import Cwf.UniType.Consistency
open import Cwf.UniType.Definition
open import Cwf.UniType.FinFun
open import Cwf.UniType.Relation

googa : ∀ {f g h} → g ⊆ h →
        (∀ {u v} → (u , v) ∈ f → ⊑-proof g u v) →
        ∀ {u v} → (u , v) ∈ f → ⊑-proof h u v
googa g⊆h p uv∈f with (p uv∈f)
... | record { sub = sub ; preable = preable ; sub⊆g = sub⊆g ; pre⊑u = pre⊑u ; v⊑post = v⊑post }
  = record
      { sub = sub
      ; preable = preable
      ; sub⊆g = ⊆-trans sub⊆g g⊆h
      ; pre⊑u = pre⊑u
      ; v⊑post = v⊑post
      }

⊑-⊔-lemma₁ : ∀ {i} → {u v w : Nbh {i}} → u ⊑ v → con (v ⊔ w) → u ⊑ (v ⊔ w)
⊑-⊔-lemma₁ (⊑-bot _) convw = ⊑-bot convw
⊑-⊔-lemma₁ {w = ⊥} ⊑-0 _ = ⊑-0
⊑-⊔-lemma₁ {w = 0ᵤ} ⊑-0 _ = ⊑-0
⊑-⊔-lemma₁ {w = ⊥} (⊑-s u⊑v) _ = ⊑-s u⊑v
⊑-⊔-lemma₁ {w = s _} (⊑-s u⊑v) convw = ⊑-s (⊑-⊔-lemma₁ u⊑v convw)
⊑-⊔-lemma₁ {w = ⊥} ⊑-ℕ _ = ⊑-ℕ
⊑-⊔-lemma₁ {w = ℕ} ⊑-ℕ _ = ⊑-ℕ
⊑-⊔-lemma₁ {w = ⊥} (⊑-F conf cong p) _ = ⊑-F conf cong p
⊑-⊔-lemma₁ {w = F h} (⊑-F conf cong p) conuw = ⊑-F conf conuw (googa ∪-lemma₃ p)
⊑-⊔-lemma₁ {w = ⊥} (⊑-Π u⊑v f⊑g) _ = ⊑-Π u⊑v f⊑g
⊑-⊔-lemma₁ {w = Π _ _} (⊑-Π u⊑v f⊑g) _ with (orderOnlyCon f⊑g)
⊑-⊔-lemma₁ {w = Π _ _} (⊑-Π u⊑v (⊑-F _ _ p)) (convw , congh) | (conf , _) =
  ⊑-Π (⊑-⊔-lemma₁ u⊑v convw) (⊑-F conf congh (googa ∪-lemma₃ p))
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
⊑-⊔-lemma₂ {v = F _} (⊑-F conf cong p) conuw = ⊑-F conf conuw (googa ∪-lemma₄ p)
⊑-⊔-lemma₂ {v = ⊥} (⊑-Π u⊑w f⊑h) conuw = ⊑-Π u⊑w f⊑h
⊑-⊔-lemma₂ {v = Π _ _} (⊑-Π u⊑w f⊑h) conuw with (orderOnlyCon f⊑h)
⊑-⊔-lemma₂ {v = Π _ _} (⊑-Π u⊑w (⊑-F _ _ p)) (conuw , confh) | (conf , _)
  = ⊑-Π (⊑-⊔-lemma₂ u⊑w conuw) (⊑-F conf confh (googa ∪-lemma₄ p))
⊑-⊔-lemma₂ {v = ⊥} ⊑-𝒰 _ = ⊑-𝒰
⊑-⊔-lemma₂ {v = 𝒰} ⊑-𝒰 _ = ⊑-𝒰

⊑-⊔-lemma₃ : ∀ {u v u′ v′} → u ⊑ u′ → v ⊑ v′ → con (u ⊔ v) → con (u′ ⊔ v′) → (u ⊔ v) ⊑ (u′ ⊔ v′)
⊑-⊔-lemma₃ u⊑u′ v⊑v′ conuv conu′v′
  = ⊑-⊔ (⊑-⊔-lemma₁ u⊑u′ conu′v′) (⊑-⊔-lemma₂ v⊑v′ conu′v′) conuv
