--{-# OPTIONS --safe #-}

module Cwf.DomainCwf.UniType.AxiomProofs where

open import Base.Core
open import Base.FinFun
open import Cwf.DomainCwf.UniType.AssignSize
open import Cwf.DomainCwf.UniType.Consistency
--open import Cwf.DomainCwf.UniType.ConsistencyLemmata
open import Cwf.DomainCwf.UniType.Definition
open import Cwf.DomainCwf.UniType.Relation

open import Data.Nat.Base hiding (ℕ) renaming (_⊔_ to max)
open import Data.Nat.Induction
open import Data.Nat.Properties
open import Induction.WellFounded

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
⊑-reflLemma₂ {v = v} (⊑-bot conv) = {!!} -- ⊑-bot (conAssoc' {u = v} conv)
⊑-reflLemma₂ ⊑-0 = ⊑-0
⊑-reflLemma₂ (⊑-s u⊑v) = ⊑-s u⊑v
⊑-reflLemma₂ ⊑-ℕ = ⊑-ℕ
⊑-reflLemma₂ (⊑-F conf cong f⊑g) = ⊑-F conf cong f⊑g
⊑-reflLemma₂ (⊑-I U⊑U′ u⊑u′ v⊑v′) = ⊑-I U⊑U′ u⊑u′ v⊑v′
⊑-reflLemma₂ (⊑-rfl u⊑v) = ⊑-rfl u⊑v
⊑-reflLemma₂ (⊑-Π u⊑v f⊑g) = ⊑-Π u⊑v f⊑g
⊑-reflLemma₂ ⊑-𝒰 = ⊑-𝒰

⊑-refl : ∀ {u p} → con' u p → u ⊑ u
⊑-refl {⊥} _ = ⊑-bot *
⊑-refl {0ᵤ} _ = ⊑-0
⊑-refl {s u} {acc rs} conu = ⊑-s (⊑-refl conu)
⊑-refl {ℕ} _ = ⊑-ℕ
⊑-refl {F f} {acc rs} (conPairsf , conElemsf) = ⊑-F cff cff f⊑f
  where cff : conFinFun f
        cff = (λ uv∈f u′v′∈f → wfIrrelevantPairs uv∈f u′v′∈f (conPairsf uv∈f u′v′∈f))
            , λ uv∈f → wfIrrelevantElems uv∈f (conElemsf uv∈f)
        f⊑f : ∀ {u v} → (u , v) ∈ f → ⊑-proof f u v
        f⊑f {u} {v} uv∈f =
          record { sub = (u , v) ∷ ∅
                 ; sub⊆g = ⊆-lemma₅ uv∈f
                 ; pre⊑u = ⊑-reflLemma₁ (⊑-refl {p = rs _ (s≤s (uv∈f⇒u≤f f u v uv∈f))} (wfIrrelevant {u} (⊠-fst (conElemsf uv∈f))))
                 ; v⊑post = ⊑-reflLemma₂ (⊑-refl {p = rs _ (s≤s (uv∈f⇒v≤f f u v uv∈f))} (wfIrrelevant {v} (⊠-snd (conElemsf uv∈f))))
                 }
⊑-refl {refl u} {acc rs} conu = ⊑-rfl (⊑-refl conu)
⊑-refl {I U u u′} {acc rs} (conU , (conu , conu′))
  = ⊑-I (⊑-refl {p = rs _ U<IUuu′} (wfIrrelevant {U} conU))
        (⊑-refl {p = rs _ (u<IUuu′ {U})} (wfIrrelevant {u} conu))
        (⊑-refl {p = rs _ (u′<IUuu′ {U})} (wfIrrelevant {u′} conu′))
⊑-refl {Π U f} {acc rs} (conU , (conPairsf , conElemsf))
  = ⊑-Π (⊑-refl {U} {p = rs _ (s≤s (m≤m⊔n _ _))} (wfIrrelevant {U} conU)) (⊑-F cff cff f⊑f)
  where cff : conFinFun f
        cff = (λ uv∈f u′v′∈f → wfIrrelevantPairs uv∈f u′v′∈f (conPairsf uv∈f u′v′∈f))
            , λ uv∈f → wfIrrelevantElems uv∈f (conElemsf uv∈f)
        f⊑f : ∀ {u v} → (u , v) ∈ f → ⊑-proof f u v
        f⊑f {u} {v} uv∈f =
          record { sub = (u , v) ∷ ∅
                 ; sub⊆g = ⊆-lemma₅ uv∈f
                 ; pre⊑u = ⊑-reflLemma₁ (⊑-refl {p = rs _ (uv∈f⇒u<ΠUf uv∈f)} (wfIrrelevant {u} (⊠-fst (conElemsf uv∈f))))
                 ; v⊑post = ⊑-reflLemma₂ (⊑-refl {p = rs _ (uv∈f⇒v<ΠUf uv∈f)} (wfIrrelevant {v} (⊠-snd (conElemsf uv∈f))))
                 }
⊑-refl {𝒰} _ = ⊑-𝒰

⊑-⊥ : ∀ {u} → con u → ⊥ ⊑ u
⊑-⊥ conu = ⊑-bot conu

⊑-⊔' : ∀ {f g h} → (F f) ⊑ (F h) → (F g) ⊑ (F h) →
       ∀ {u v} → (u , v) ∈ (f ∪ g) → ⊑-proof h u v
⊑-⊔' {f = f} (⊑-F _ _ p₁) (⊑-F _ _ p₂) uv∈f∪g with (∪-lemma₂ {𝑓 = f} uv∈f∪g)
... | inl uv∈f = p₁ uv∈f
... | inr uv∈g = p₂ uv∈g

⊑-⊔ : ∀ {u v w p} → u ⊑ w → v ⊑ w → con' (u ⊔ v) p → (u ⊔ v) ⊑ w
⊑-⊔ u⊑w (⊑-bot _) _ = ⊑-reflLemma₁ u⊑w
⊑-⊔ (⊑-bot _) ⊑-0 _ = ⊑-0
⊑-⊔ ⊑-0 ⊑-0 _ = ⊑-0
⊑-⊔ (⊑-bot _) (⊑-s v⊑w) _ = ⊑-s v⊑w
⊑-⊔ {u} {v} {p = acc rs} (⊑-s u⊑w) (⊑-s v⊑w) conuv
  = ⊑-s (⊑-⊔ {p = rs _ (s≤s ≤-refl)} u⊑w v⊑w conuv)
⊑-⊔ (⊑-bot _) ⊑-ℕ _ = ⊑-ℕ
⊑-⊔ ⊑-ℕ ⊑-ℕ _ = ⊑-ℕ
⊑-⊔ (⊑-bot _) (⊑-F cong conh p) _ = ⊑-F cong conh p
⊑-⊔ {F f} {F g} {p = acc rs} (⊑-F conf conh p₁) (⊑-F cong _ p₂) (conPairsf , conElemsf)
  = ⊑-F cff conh (⊑-⊔' (⊑-F conf conh p₁) (⊑-F cong conh p₂))
  where cff : conFinFun (f ∪ g)
        cff = (λ uv∈f u′v′∈f → wfIrrelevantPairs uv∈f u′v′∈f (conPairsf uv∈f u′v′∈f))
            , λ uv∈f → wfIrrelevantElems uv∈f (conElemsf uv∈f)
⊑-⊔ (⊑-bot _) (⊑-rfl v⊑w) _ = ⊑-rfl v⊑w
⊑-⊔  {p = acc rs} (⊑-rfl u⊑w) (⊑-rfl v⊑w) conuv
  = ⊑-rfl (⊑-⊔ u⊑w v⊑w conuv)
⊑-⊔ (⊑-bot _) (⊑-I U′⊑U″ u′⊑u″ v′⊑v″) conuv = ⊑-I U′⊑U″ u′⊑u″ v′⊑v″
⊑-⊔ {p = acc rs} (⊑-I U⊑U″ u⊑u″ v⊑v″) (⊑-I U′⊑U″ u′⊑u″ v′⊑v″) (conUU′ , (conuu′ , convv′))
  = ⊑-I (⊑-⊔ U⊑U″ U′⊑U″ conUU′) (⊑-⊔ u⊑u″ u′⊑u″ conuu′) (⊑-⊔ v⊑v″ v′⊑v″ convv′)
⊑-⊔ (⊑-bot _) (⊑-Π v⊑w g⊑h) conuv = ⊑-Π v⊑w g⊑h
⊑-⊔ {Π U f} {Π V g} {p = acc rs} (⊑-Π u⊑w f⊑h) (⊑-Π v⊑w g⊑h) (conuv , (conPairs , conElems))
  = ⊑-Π (⊑-⊔ u⊑w v⊑w conuv) (⊑-⊔ {p = rs _ (s≤s (m≤n⊔m _ _))} f⊑h g⊑h (cff {rs _ (s≤s (m≤n⊔m _ _))}))
  where cff : ∀ {p} → con' (F (f ∪ g)) p
        cff {acc rs} = (λ uv∈f u′v′∈f → wfIrrelevantPairs uv∈f u′v′∈f (conPairs uv∈f u′v′∈f))
                     , λ uv∈f → wfIrrelevantElems uv∈f (conElems uv∈f)
⊑-⊔ (⊑-bot _) ⊑-𝒰 _ = ⊑-𝒰
⊑-⊔ ⊑-𝒰 ⊑-𝒰 _ = ⊑-𝒰

⊑-⊔-fst' : ∀ {f g u v p} → conFinFun' (f ∪ g) p → (u , v) ∈ f → ⊑-proof (f ∪ g) u v
⊑-⊔-fst' {u = u} {v} {p = acc rs} (_ , conElems) uv∈f
  = record { sub = (u , v) ∷ ∅
           ; sub⊆g = ⊆-lemma₅ (∪-lemma₃ uv∈f)
           ; pre⊑u = ⊑-reflLemma₁ (⊑-refl (⊠-fst (conElems (∪-lemma₃ uv∈f))))
           ; v⊑post = ⊑-reflLemma₂ (⊑-refl (⊠-snd (conElems (∪-lemma₃ uv∈f))))
           }

⊑-⊔-fst : ∀ {u v p} → con' (u ⊔ v) p → u ⊑ (u ⊔ v)
⊑-⊔-fst {⊥} {v} conuv = ⊑-bot (wfIrrelevant {v} conuv)
⊑-⊔-fst {0ᵤ} {⊥} _ = ⊑-0
⊑-⊔-fst {0ᵤ} {0ᵤ} _ = ⊑-0
⊑-⊔-fst {s u} {⊥} {acc rs} conuv = ⊑-s (⊑-refl conuv)
⊑-⊔-fst {s u} {s v} {acc rs} conuv = ⊑-s (⊑-⊔-fst conuv)
⊑-⊔-fst {ℕ} {⊥} _ = ⊑-ℕ
⊑-⊔-fst {ℕ} {ℕ} _ = ⊑-ℕ
⊑-⊔-fst {F f} {⊥} {acc rs} (conPairsf , conElemsf) = ⊑-refl {p = <-wellFounded _} cff
  where cff : conFinFun f
        cff = (λ uv∈f u′v′∈f → wfIrrelevantPairs uv∈f u′v′∈f (conPairsf uv∈f u′v′∈f))
            , λ uv∈f → wfIrrelevantElems uv∈f (conElemsf uv∈f)
⊑-⊔-fst {F f} {F g} {acc rs} (conPairs , conElems)
  = ⊑-F {!!} cff∪ (⊑-⊔-fst' {p = <-wellFounded _} cff∪)
  -- ⊑-F (subsetIsCon ∪-lemma₃ conuv) conuv (⊑-⊔-fst' conuv)
  where cff∪ : conFinFun (f ∪ g)
        cff∪ = (λ uv∈f u′v′∈f → wfIrrelevantPairs uv∈f u′v′∈f (conPairs uv∈f u′v′∈f))
            , λ uv∈f → wfIrrelevantElems uv∈f (conElems uv∈f)
⊑-⊔-fst {refl u} {⊥} {acc rs} conuv = ⊑-rfl (⊑-refl conuv)
⊑-⊔-fst {refl u} {refl v} {acc rs} conuv = ⊑-rfl (⊑-⊔-fst conuv)
⊑-⊔-fst {I U u u′} {⊥} {acc rs} (conU , (conu , conu′))
  = ⊑-I (⊑-refl conU) (⊑-refl conu) (⊑-refl conu′)
⊑-⊔-fst {I U u u′} {I V v v′} {acc rs} (conUV , (conuv , conu′v′))
  = ⊑-I (⊑-⊔-fst conUV) (⊑-⊔-fst conuv) (⊑-⊔-fst conu′v′)
⊑-⊔-fst {Π U f} {⊥} {acc rs} (conU , (conPairsf , conElemsf))
  = ⊑-Π (⊑-refl conU) (⊑-refl {p = <-wellFounded _} cff)
  where cff : conFinFun f
        cff = (λ uv∈f u′v′∈f → wfIrrelevantPairs uv∈f u′v′∈f (conPairsf uv∈f u′v′∈f))
            , λ uv∈f → wfIrrelevantElems uv∈f (conElemsf uv∈f)
⊑-⊔-fst {Π U f} {Π V g} {acc rs} (conU , (conPairs , conElems))
  = ⊑-Π (⊑-⊔-fst conU) (⊑-F {!!} cff∪ (⊑-⊔-fst' {p = <-wellFounded _} cff∪))
  where cff∪ : conFinFun (f ∪ g)
        cff∪ = (λ uv∈f u′v′∈f → wfIrrelevantPairs uv∈f u′v′∈f (conPairs uv∈f u′v′∈f))
            , λ uv∈f → wfIrrelevantElems uv∈f (conElems uv∈f)
⊑-⊔-fst {𝒰} {⊥} conuv = ⊑-𝒰
⊑-⊔-fst {𝒰} {𝒰} conuv = ⊑-𝒰
⊑-⊔-fst {incons} {p = acc rs} ()

⊑-⊔-snd' : ∀ {f g u v p} → conFinFun' (f ∪ g) p → (u , v) ∈ g → ⊑-proof (f ∪ g) u v
⊑-⊔-snd' {u = u} {v} {p = acc rs} (_ , conElems) uv∈f
  = record { sub = (u , v) ∷ ∅
           ; sub⊆g = ⊆-lemma₅ (∪-lemma₄ uv∈f)
           ; pre⊑u = ⊑-reflLemma₁ (⊑-refl (⊠-fst (conElems (∪-lemma₄ uv∈f))))
           ; v⊑post = ⊑-reflLemma₂ (⊑-refl (⊠-snd (conElems (∪-lemma₄ uv∈f))))
           }

⊑-⊔-snd : ∀ {u v p} → con' (u ⊔ v) p → v ⊑ (u ⊔ v)
⊑-⊔-snd {⊥} conuv = ⊑-refl conuv
⊑-⊔-snd {0ᵤ} {⊥} conuv = ⊑-bot *
⊑-⊔-snd {0ᵤ} {0ᵤ} conuv = ⊑-0
⊑-⊔-snd {s u} {⊥} {acc rs} conuv = ⊑-bot (wfIrrelevant {u} conuv)
⊑-⊔-snd {s u} {s v} {p = acc rs} conuv = ⊑-s (⊑-⊔-snd conuv)
⊑-⊔-snd {ℕ} {⊥} conuv = ⊑-bot *
⊑-⊔-snd {ℕ} {ℕ} conuv = ⊑-ℕ
⊑-⊔-snd {F f} {⊥} {acc rs} (conPairsf , conElemsf) = ⊑-bot cff
  where cff : conFinFun f
        cff = (λ uv∈f u′v′∈f → wfIrrelevantPairs uv∈f u′v′∈f (conPairsf uv∈f u′v′∈f))
            , λ uv∈f → wfIrrelevantElems uv∈f (conElemsf uv∈f)
⊑-⊔-snd {F f} {F g} {acc rs} (conPairs , conElems)
  = ⊑-F {!!} cff∪ (⊑-⊔-snd' {p = <-wellFounded _} cff∪)
  where cff∪ : conFinFun (f ∪ g)
        cff∪ = (λ uv∈f u′v′∈f → wfIrrelevantPairs uv∈f u′v′∈f (conPairs uv∈f u′v′∈f))
            , λ uv∈f → wfIrrelevantElems uv∈f (conElems uv∈f)
-- = ⊑-F (subsetIsCon ∪-lemma₄ conuv) conuv (⊑-⊔-snd' conuv)
⊑-⊔-snd {refl u} {⊥} {acc rs} conuv = ⊑-bot (wfIrrelevant {u} conuv)
⊑-⊔-snd {refl u} {refl v} {acc rs} conuv = ⊑-rfl (⊑-⊔-snd conuv)
⊑-⊔-snd {I U u u′} {⊥} {acc rs} (conU , (conu , conu′))
  = ⊑-bot (wfIrrelevant {U} conU , (wfIrrelevant {u} conu , wfIrrelevant {u′} conu′))
⊑-⊔-snd {I U u u′} {I V v v′} {acc rs} (conUV , (conuv , conu′v′))
  = ⊑-I (⊑-⊔-snd conUV) (⊑-⊔-snd conuv) (⊑-⊔-snd conu′v′)
⊑-⊔-snd {Π U f} {⊥} {acc rs} (conU , (conPairsf , conElemsf))
  = ⊑-bot ((wfIrrelevant {U} conU) , cff)
  where cff = ((λ {u} {v} {u′} {v′} uv∈f u′v′∈f conuu′ → wfIrrelevant {v ⊔ v′} (conPairsf uv∈f u′v′∈f (wfIrrelevant {u ⊔ u′} conuu′)))
            , (λ {u} {v} uv∈f → wfIrrelevant {u} (⊠-fst (conElemsf uv∈f)) , wfIrrelevant {v} (⊠-snd (conElemsf uv∈f))))
⊑-⊔-snd {Π U f} {Π V g} {acc rs} (conUV , (conPairs , conElems))
  = ⊑-Π (⊑-⊔-snd conUV) (⊑-F {!!} cff∪ (⊑-⊔-snd' {p = <-wellFounded _} cff∪))
  where cff∪ : conFinFun (f ∪ g)
        cff∪ = (λ uv∈f u′v′∈f → wfIrrelevantPairs uv∈f u′v′∈f (conPairs uv∈f u′v′∈f))
             , λ uv∈f → wfIrrelevantElems uv∈f (conElems uv∈f)
--   = ⊑-Π (⊑-⊔-snd conuv) (⊑-F (subsetIsCon ∪-lemma₄ confg) confg (⊑-⊔-snd' confg))
⊑-⊔-snd {𝒰} {⊥} conuv = ⊑-bot *
⊑-⊔-snd {𝒰} {𝒰} conuv = ⊑-𝒰
