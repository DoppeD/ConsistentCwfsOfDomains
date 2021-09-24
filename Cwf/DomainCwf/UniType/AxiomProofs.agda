module Cwf.DomainCwf.UniType.AxiomProofs where

open import Base.Core
open import Base.FinFun
open import Cwf.DomainCwf.UniType.Consistency
open import Cwf.DomainCwf.UniType.ConsistencyLemmata
open import Cwf.DomainCwf.UniType.Definition
open import Cwf.DomainCwf.UniType.Relation

⊑-reflLemma₁ : ∀ {u v} → u ⊑ v → (u ⊔ ⊥) ⊑ v
⊑-reflLemma₁ (⊑-bot conv) = ⊑-bot conv
⊑-reflLemma₁ ⊑-0 = ⊑-0
⊑-reflLemma₁ (⊑-s u⊑v) = ⊑-s u⊑v
⊑-reflLemma₁ ⊑-ℕ = ⊑-ℕ
⊑-reflLemma₁ (⊑-F conf cong f⊑g) = ⊑-F conf cong f⊑g
⊑-reflLemma₁ (⊑-rfl u⊑v) = ⊑-rfl u⊑v
⊑-reflLemma₁ (⊑-I U⊑U′ u⊑u′ v⊑v′) = ⊑-I U⊑U′ u⊑u′ v⊑v′
⊑-reflLemma₁ (⊑-Π u⊑v f⊑g) = ⊑-Π u⊑v f⊑g
⊑-reflLemma₁ ⊑-𝒰 = ⊑-𝒰

⊑-reflLemma₂ : ∀ {u v} → u ⊑ v → u ⊑ (v ⊔ ⊥)
⊑-reflLemma₂ {v = v} (⊑-bot conv) = ⊑-bot (conAssoc' {v} conv)
⊑-reflLemma₂ ⊑-0 = ⊑-0
⊑-reflLemma₂ (⊑-s u⊑v) = ⊑-s u⊑v
⊑-reflLemma₂ ⊑-ℕ = ⊑-ℕ
⊑-reflLemma₂ (⊑-F conf cong f⊑g) = ⊑-F conf cong f⊑g
⊑-reflLemma₂ (⊑-I U⊑U′ u⊑u′ v⊑v′) = ⊑-I U⊑U′ u⊑u′ v⊑v′
⊑-reflLemma₂ (⊑-rfl u⊑v) = ⊑-rfl u⊑v
⊑-reflLemma₂ (⊑-Π u⊑v f⊑g) = ⊑-Π u⊑v f⊑g
⊑-reflLemma₂ ⊑-𝒰 = ⊑-𝒰

⊑-refl : ∀ {u} → con u → u ⊑ u
⊑-refl' : ∀ {f u v} → conFinFun f → (u , v) ∈ f → ⊑-proof f u v

⊑-refl {⊥} conu = ⊑-bot *
⊑-refl {0ᵤ} conu = ⊑-0
⊑-refl {s u} conu = ⊑-s (⊑-refl conu)
⊑-refl {ℕ} conu = ⊑-ℕ
⊑-refl {F f} conu = ⊑-F conu conu (⊑-refl' conu)
⊑-refl {refl u} conu = ⊑-rfl (⊑-refl conu)
⊑-refl {I U u v} (conU , (conu , conv))
  = ⊑-I (⊑-refl conU) (⊑-refl conu) (⊑-refl conv)
⊑-refl {Π u f} (conu , conf)
  = ⊑-Π (⊑-refl conu) (⊑-F conf conf (⊑-refl' conf))
⊑-refl {𝒰} conu = ⊑-𝒰

⊑-refl' (_ , conElemsf) uv∈f with (conElemsf uv∈f)
⊑-refl' {u = u} {v} _ uv∈f | (conu , conv)
  = record
      { sub = (u , v) ∷ ∅
      ; sub⊆g = ⊆-lemma₅ uv∈f
      ; pre⊑u = ⊑-reflLemma₁ (⊑-refl conu)
      ; v⊑post = ⊑-reflLemma₂ (⊑-refl conv)
      }

⊑-⊥ : ∀ {u} → con u → ⊥ ⊑ u
⊑-⊥ conu = ⊑-bot conu

⊑-⊔' : ∀ {f g h} → (F f) ⊑ (F h) → (F g) ⊑ (F h) →
       ∀ {u v} → (u , v) ∈ (f ∪ g) → ⊑-proof h u v
⊑-⊔' {f} (⊑-F _ _ p₁) (⊑-F _ _ p₂) uv∈f∪g with (∪-lemma₂ {𝑓 = f} uv∈f∪g)
... | inl uv∈f = p₁ uv∈f
... | inr uv∈g = p₂ uv∈g

⊑-⊔ : ∀ {u v w} → u ⊑ w → v ⊑ w → con (u ⊔ v) → (u ⊔ v) ⊑ w
⊑-⊔ u⊑w (⊑-bot _) _ = ⊑-reflLemma₁ u⊑w
⊑-⊔ (⊑-bot _) ⊑-0 _ = ⊑-0
⊑-⊔ ⊑-0 ⊑-0 _ = ⊑-0
⊑-⊔ (⊑-bot _) (⊑-s v⊑w) _ = ⊑-s v⊑w
⊑-⊔ (⊑-s u⊑w) (⊑-s v⊑w) conuv = ⊑-s (⊑-⊔ u⊑w v⊑w conuv)
⊑-⊔ (⊑-bot _) ⊑-ℕ _ = ⊑-ℕ
⊑-⊔ ⊑-ℕ ⊑-ℕ _ = ⊑-ℕ
⊑-⊔ (⊑-bot _) (⊑-F cong conh p) _ = ⊑-F cong conh p
⊑-⊔ (⊑-F conf conh p₁) (⊑-F cong _ p₂) conuv
  = ⊑-F conuv conh (⊑-⊔' (⊑-F conf conh p₁) (⊑-F cong conh p₂))
⊑-⊔ (⊑-bot _) (⊑-rfl v⊑w) _ = ⊑-rfl v⊑w
⊑-⊔ (⊑-rfl u⊑w) (⊑-rfl v⊑w) conuv = ⊑-rfl (⊑-⊔ u⊑w v⊑w conuv)
⊑-⊔ (⊑-bot _) (⊑-I U′⊑U″ u′⊑u″ v′⊑v″) conuv = ⊑-I U′⊑U″ u′⊑u″ v′⊑v″
⊑-⊔ (⊑-I U⊑U″ u⊑u″ v⊑v″) (⊑-I U′⊑U″ u′⊑u″ v′⊑v″) (conUU′ , (conuu′ , convv′))
  = ⊑-I (⊑-⊔ U⊑U″ U′⊑U″ conUU′) (⊑-⊔ u⊑u″ u′⊑u″ conuu′) (⊑-⊔ v⊑v″ v′⊑v″ convv′)
⊑-⊔ (⊑-bot _) (⊑-Π v⊑w g⊑h) conuv = ⊑-Π v⊑w g⊑h
⊑-⊔ (⊑-Π u⊑w f⊑h) (⊑-Π v⊑w g⊑h) (conuv , confg)
  = ⊑-Π (⊑-⊔ u⊑w v⊑w conuv) (⊑-⊔ f⊑h g⊑h confg)
⊑-⊔ (⊑-bot _) ⊑-𝒰 conuv = ⊑-𝒰
⊑-⊔ ⊑-𝒰 ⊑-𝒰 conuv = ⊑-𝒰

⊑-⊔-fst' : ∀ {f g u v} → conFinFun (f ∪ g) → (u , v) ∈ f → ⊑-proof (f ∪ g) u v
⊑-⊔-fst' confg uv∈f = ⊑-refl' confg (∪-lemma₃ uv∈f)

⊑-⊔-fst : ∀ {u v} → con (u ⊔ v) → u ⊑ (u ⊔ v)
⊑-⊔-fst {⊥} conuv = ⊑-bot conuv
⊑-⊔-fst {0ᵤ} {⊥} _ = ⊑-refl *
⊑-⊔-fst {0ᵤ} {0ᵤ} _ = ⊑-refl *
⊑-⊔-fst {s _} {⊥} conuv = ⊑-refl conuv
⊑-⊔-fst {s _} {s _} conuv = ⊑-s (⊑-⊔-fst conuv)
⊑-⊔-fst {ℕ} {⊥} _ = ⊑-refl *
⊑-⊔-fst {ℕ} {ℕ} _ = ⊑-refl *
⊑-⊔-fst {F _} {⊥} conuv = ⊑-refl conuv
⊑-⊔-fst {F _} {F _} conuv =
  ⊑-F (subsetIsCon ∪-lemma₃ conuv) conuv (⊑-⊔-fst' conuv)
⊑-⊔-fst {refl _} {⊥} conuv = ⊑-refl conuv
⊑-⊔-fst {refl _} {refl _} conuv = ⊑-rfl (⊑-⊔-fst conuv)
⊑-⊔-fst {I _ _ _} {⊥} conuv = ⊑-refl conuv
⊑-⊔-fst {I _ _ _} {I _ _ _} (conUU′ , (conuu′ , convv′))
  = ⊑-I (⊑-⊔-fst conUU′) (⊑-⊔-fst conuu′) (⊑-⊔-fst convv′)
⊑-⊔-fst {Π _ _} {⊥} conuv = ⊑-refl conuv
⊑-⊔-fst {Π _ _} {Π _ _} (conuv , confg)
  = ⊑-Π (⊑-⊔-fst conuv) (⊑-F (subsetIsCon ∪-lemma₃ confg) confg (⊑-⊔-fst' confg))
⊑-⊔-fst {𝒰} {⊥} _ = ⊑-refl *
⊑-⊔-fst {𝒰} {𝒰} _ = ⊑-refl *

⊑-⊔-snd' : ∀ {f g u v} → conFinFun (f ∪ g) → (u , v) ∈ g → ⊑-proof (f ∪ g) u v
⊑-⊔-snd' confg uv∈g = ⊑-refl' confg (∪-lemma₄ uv∈g)

⊑-⊔-snd : ∀ {u v} → con (u ⊔ v) → v ⊑ (u ⊔ v)
⊑-⊔-snd {⊥} conuv = ⊑-refl conuv
⊑-⊔-snd {0ᵤ} {⊥} _ = ⊑-bot *
⊑-⊔-snd {0ᵤ} {0ᵤ} _ = ⊑-refl *
⊑-⊔-snd {s _} {⊥} conuv = ⊑-bot conuv
⊑-⊔-snd {s _} {s _} conuv = ⊑-s (⊑-⊔-snd conuv)
⊑-⊔-snd {ℕ} {⊥} conuv = ⊑-bot *
⊑-⊔-snd {ℕ} {ℕ} conuv = ⊑-refl *
⊑-⊔-snd {F _} {⊥} conuv = ⊑-bot conuv
⊑-⊔-snd {F _} {F _} conuv
  = ⊑-F (subsetIsCon ∪-lemma₄ conuv) conuv (⊑-⊔-snd' conuv)
⊑-⊔-snd {refl _} {⊥} conuv = ⊑-bot conuv
⊑-⊔-snd {refl _} {refl _} conuv = ⊑-rfl (⊑-⊔-snd conuv)
⊑-⊔-snd {I _ _ _} {⊥} conuv = ⊑-bot conuv
⊑-⊔-snd {I _ _ _} {I _ _ _} (conUU′ , (conuu′ , convv′))
  = ⊑-I (⊑-⊔-snd conUU′) (⊑-⊔-snd conuu′) (⊑-⊔-snd convv′)
⊑-⊔-snd {Π _ _} {⊥} conuv = ⊑-bot conuv
⊑-⊔-snd {Π _ _} {Π _ _} (conuv , confg)
  = ⊑-Π (⊑-⊔-snd conuv) (⊑-F (subsetIsCon ∪-lemma₄ confg) confg (⊑-⊔-snd' confg))
⊑-⊔-snd {𝒰} {⊥} _ = ⊑-bot *
⊑-⊔-snd {𝒰} {𝒰} _ = ⊑-refl *
