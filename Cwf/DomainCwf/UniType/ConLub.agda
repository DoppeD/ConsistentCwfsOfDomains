{-# OPTIONS --safe --sized-types #-}

module Cwf.DomainCwf.UniType.ConLub where

open import Base.Core
open import Cwf.DomainCwf.UniType.Coherence
open import Cwf.DomainCwf.UniType.Consistency
open import Cwf.DomainCwf.UniType.ConsistencyLemmata
open import Cwf.DomainCwf.UniType.Definition
open import Cwf.DomainCwf.UniType.FinFun
open import Cwf.DomainCwf.UniType.Relation
open import Cwf.DomainCwf.UniType.RelationLemmata

open import Agda.Builtin.Equality

⊔-assoc : ∀ {i} → {u v w : Nbh {i}} → con (u ⊔ v) → con (v ⊔ w) →
          ((u ⊔ v) ⊔ w) ≡ (u ⊔ (v ⊔ w))
⊔-assoc {u = ⊥} _ _ = refl
⊔-assoc {u = 0ᵤ} {⊥} _ _ = refl
⊔-assoc {u = 0ᵤ} {0ᵤ} {⊥} _ _ = refl
⊔-assoc {u = 0ᵤ} {0ᵤ} {0ᵤ} _ _ = refl
⊔-assoc {u = s _} {⊥} _ _ = refl
⊔-assoc {u = s _} {s _} {⊥} _ _ = refl
⊔-assoc {u = s u} {s _} {s _} conuv convw
  rewrite (⊔-assoc {u = u} conuv convw) = refl
⊔-assoc {u = ℕ} {⊥} _ _ = refl
⊔-assoc {u = ℕ} {ℕ} {⊥} _ _ = refl
⊔-assoc {u = ℕ} {ℕ} {ℕ} _ _ = refl
⊔-assoc {u = F _} {⊥} _ _ = refl
⊔-assoc {u = F _} {F _} {⊥} _ _ = refl
⊔-assoc {u = F f} {F g} {F h} _ _
  rewrite (∪-assoc {f = f} {g} {h}) = refl
⊔-assoc {u = refl _} {⊥} _ _ = refl
⊔-assoc {u = refl _} {refl _} {⊥} _ _ = refl
⊔-assoc {u = refl u} {refl _} {refl _} conuv convw
  rewrite (⊔-assoc {u = u} conuv convw) = refl
⊔-assoc {u = I _ _ _} {⊥} _ _ = refl
⊔-assoc {u = I _ _ _} {I _ _ _} {⊥} _ _ = refl
⊔-assoc {u = I U u v} {I _ _ _} {I _ _ _} (conUU′ , (conuu′ , convv′)) (conU′U″ , (conu′u″ , conv′v″))
  rewrite (⊔-assoc {u = U} conUU′ conU′U″)
  rewrite (⊔-assoc {u = u} conuu′ conu′u″)
  rewrite (⊔-assoc {u = v} convv′ conv′v″)
  = refl
⊔-assoc {u = Π _ _} {⊥} _ _ = refl
⊔-assoc {u = Π _ _} {Π _ _} {⊥} _ _ = refl
⊔-assoc {u = Π u f} {Π _ g} {Π _ h} (conuv , _) (convw , _)
  rewrite (⊔-assoc {u = u} conuv convw)
  rewrite (∪-assoc {f = f} {g} {h}) = refl
⊔-assoc {u = 𝒰} {⊥} _ _ = refl
⊔-assoc {u = 𝒰} {𝒰} {⊥} _ _ = refl
⊔-assoc {u = 𝒰} {𝒰} {𝒰} _ _ = refl

preUnionLemma' : ∀ {i} → {f g : FinFun {i}} → con (pre f ⊔ pre g) → pre (f ∪ g) ≡ pre f ⊔ pre g
preUnionLemma' {f = ∅} _ = refl
preUnionLemma' {f = (u , v) ∷ f′} conprefg with (conLemma₁ {u = pre ((u , v) ∷ f′)} conprefg)
preUnionLemma' {f = (u , v) ∷ f′} conprefg | conpref with (conLemma₂ {u = u} conpref)
preUnionLemma' {f = (u , v) ∷ f′} {g} conprefg | conpref | conpref′
  rewrite (⊔-assoc {u = u} conpref (conLemma₂ {u = u} (conAssoc₂ {u = u} conprefg)))
  rewrite (preUnionLemma' {f = f′} {g} (conLemma₂ {u = u} (conAssoc₂ {u = u} conprefg)))
  = refl

preUnionLemma : ∀ {i} → {f g : FinFun {i}} → con (pre f ⊔ pre g) → con (pre (f ∪ g))
preUnionLemma {f = f} {g} conprefg
  rewrite (preUnionLemma' {f = f} {g} conprefg)
  = conprefg

postUnionLemma : ∀ {i} → {f g : FinFun {i}} → con (post f) → con (post (f ∪ g)) → con (post f ⊔ post g)
postUnionLemma' : ∀ {i} → {f g : FinFun {i}} → con (post f) → con (post (f ∪ g)) → post f ⊔ post g ≡ post (f ∪ g)

postUnionLemma {f = f} {g} conpostf conpostfg
  rewrite (postUnionLemma' {f = f} {g} conpostf conpostfg)
  = conpostfg

postUnionLemma' {f = ∅} _ _ = refl
postUnionLemma' {f = (u , v) ∷ f′} conpostf conpostfg
  rewrite (⊔-assoc {u = v} conpostf
          (postUnionLemma {f = f′} (conLemma₂ {u = v} conpostf) (conLemma₂ {u = v} conpostfg)))
  rewrite (postUnionLemma' {f = f′} (conLemma₂ {u = v} conpostf) (conLemma₂ {u = v} conpostfg))
  = refl

Con-⊔ : ∀ {i} → {u v w : Nbh {i}} → u ⊑ w → v ⊑ w → con (u ⊔ v)
Con-⊔' : ∀ {i} → {f g h : FinFun {i}} → ∀ {u v u′ v′} →
         conFinFun f → conFinFun g → conFinFun h →
         ⊑-proof h u v → ⊑-proof h u′ v′ →
         ((u , v) ∈ f) ∨ ((u , v) ∈ g) → ((u′ , v′) ∈ f) ∨ ((u′ , v′) ∈ g) →
         con (u ⊔ u′) → con (v ⊔ v′)

Con-⊔ (⊑-bot _) v⊑w with (orderOnlyCon v⊑w)
... | conv , _ = conv
Con-⊔ ⊑-0 (⊑-bot _) = *
Con-⊔ ⊑-0 ⊑-0 = *
Con-⊔ (⊑-s u⊑w) (⊑-bot _) with (orderOnlyCon u⊑w)
... | conu , _ = conu
Con-⊔ (⊑-s u⊑w) (⊑-s v⊑w) = Con-⊔ u⊑w v⊑w
Con-⊔ ⊑-ℕ (⊑-bot _) = *
Con-⊔ ⊑-ℕ ⊑-ℕ = *
Con-⊔ (⊑-F conf _ _) (⊑-bot _) = conf
Con-⊔ {u = F f} {F g} {F h} (⊑-F conf conh p₁) (⊑-F cong _ p₂)
  = (λ uv∈∪ u′v′∈∪ → Con-⊔' {f = f} conf cong conh (lemma uv∈∪) (lemma u′v′∈∪) (∪-lemma₂ uv∈∪) (∪-lemma₂ u′v′∈∪)) , lemma₂
  where lemma : ∀ {u v} → (u , v) ∈ (f ∪ g) → ⊑-proof h u v
        lemma uv∈∪ with (∪-lemma₂ {𝑓 = f} uv∈∪)
        ... | inl uv∈f = p₁ uv∈f
        ... | inr uv∈g = p₂ uv∈g
        lemma₂ : ∀ {u v} → (u , v) ∈ (f ∪ g) → con u ⊠ con v
        lemma₂ uv∈∪ with (∪-lemma₂ {𝑓 = f} uv∈∪)
        ... | inl uv∈f = ⊠-snd conf uv∈f
        ... | inr uv∈g = ⊠-snd cong uv∈g
Con-⊔ (⊑-rfl u⊑w) (⊑-bot _) with (orderOnlyCon u⊑w)
... | conu , _ = conu
Con-⊔ (⊑-rfl u⊑w) (⊑-rfl v⊑w) = Con-⊔ u⊑w v⊑w
Con-⊔ (⊑-I U⊑U″ u⊑u″ v⊑v″) (⊑-bot _) with (orderOnlyCon U⊑U″) | orderOnlyCon u⊑u″ | orderOnlyCon v⊑v″
... | (conU , _) | (conu , _) | (conv , _) = conU , (conu , conv)
Con-⊔ (⊑-I U⊑U″ u⊑u″ v⊑v″) (⊑-I U′⊑U″ u′⊑u″ v′⊑v″)
  = Con-⊔ U⊑U″ U′⊑U″ , (Con-⊔ u⊑u″ u′⊑u″ , Con-⊔ v⊑v″ v′⊑v″)
Con-⊔ (⊑-Π u⊑w f⊑h) (⊑-bot _) with (orderOnlyCon u⊑w) | orderOnlyCon f⊑h
... | (conu , _) | (conf , _) = conu , conf
Con-⊔ {u = Π _ f} {Π _ g} {Π _ h} (⊑-Π u⊑w (⊑-F conf conh p₁)) (⊑-Π v⊑w (⊑-F cong _ p₂))
  = (Con-⊔ u⊑w v⊑w) ,
    ((λ uv∈∪ u′v′∈∪ → Con-⊔' {f = f} conf cong conh (lemma uv∈∪) (lemma u′v′∈∪) (∪-lemma₂ uv∈∪) (∪-lemma₂ u′v′∈∪)) , lemma₂)
  where lemma : ∀ {u v} → (u , v) ∈ (f ∪ g) → ⊑-proof h u v
        lemma uv∈∪ with (∪-lemma₂ {𝑓 = f} uv∈∪)
        ... | inl uv∈f = p₁ uv∈f
        ... | inr uv∈g = p₂ uv∈g
        lemma₂ : ∀ {u v} → (u , v) ∈ (f ∪ g) → con u ⊠ con v
        lemma₂ uv∈∪ with (∪-lemma₂ {𝑓 = f} uv∈∪)
        ... | inl uv∈f = ⊠-snd conf uv∈f
        ... | inr uv∈g = ⊠-snd cong uv∈g
Con-⊔ ⊑-𝒰 (⊑-bot _) = *
Con-⊔ ⊑-𝒰 ⊑-𝒰 = *

Con-⊔' {u = u} {v} {u′} {v′} _ _ conh
  record { sub = sub ; preable = preable ; sub⊆g = sub⊆g ; pre⊑u = pre⊑u ; v⊑post = v⊑post }
  record { sub = sub′ ; preable = preable′ ; sub⊆g = sub⊆g′ ; pre⊑u = pre⊑u′ ; v⊑post = v⊑post′ }
  (inl uv∈f) (inr u′v′∈g) conuu′
  = Con-⊔ {u = v} {v′} (⊑-⊔-lemma₁ v⊑post conpostsubs) (⊑-⊔-lemma₂ v⊑post′ conpostsubs)
  where conpresubs : con (pre sub ⊔ pre sub′)
        conpresubs = Con-⊔ (⊑-⊔-lemma₁ pre⊑u conuu′) (⊑-⊔-lemma₂ pre⊑u′ conuu′)
        conpostsub : con (post sub)
        conpostsub = coherence {f = sub} (subsetIsCon sub⊆g conh) preable
        conpost∪ : con (post (sub ∪ sub′))
        conpost∪ = (coherence (subsetIsCon (∪-lemma₁ sub⊆g sub⊆g′) conh) (preUnionLemma  {f = sub} conpresubs))
        conpostsubs : con (post sub ⊔ post sub′)
        conpostsubs = postUnionLemma {f = sub} conpostsub conpost∪
Con-⊔' {u = u} {v} {u′} {v′} _ _ conh
  record { sub = sub ; preable = preable ; sub⊆g = sub⊆g ; pre⊑u = pre⊑u ; v⊑post = v⊑post }
  record { sub = sub′ ; preable = preable′ ; sub⊆g = sub⊆g′ ; pre⊑u = pre⊑u′ ; v⊑post = v⊑post′ }
  (inr uv∈g) (inl uv∈f) conuu′
  = Con-⊔ {u = v} {v′} (⊑-⊔-lemma₁ v⊑post conpostsubs) (⊑-⊔-lemma₂ v⊑post′ conpostsubs)
  where conpresubs : con (pre sub ⊔ pre sub′)
        conpresubs = Con-⊔ (⊑-⊔-lemma₁ pre⊑u conuu′) (⊑-⊔-lemma₂ pre⊑u′ conuu′)
        conpostsub : con (post sub)
        conpostsub = coherence {f = sub} (subsetIsCon sub⊆g conh) preable
        conpost∪ : con (post (sub ∪ sub′))
        conpost∪ = (coherence (subsetIsCon (∪-lemma₁ sub⊆g sub⊆g′) conh) (preUnionLemma  {f = sub} conpresubs))
        conpostsubs : con (post sub ⊔ post sub′)
        conpostsubs = postUnionLemma {f = sub} conpostsub conpost∪
Con-⊔' (conPairsf , _)  _ _ _ _ (inl uv∈f) (inl u′v′∈f) conuu′
  = conPairsf uv∈f u′v′∈f conuu′
Con-⊔' _ (conPairsg , _) _ _ _ (inr uv∈g) (inr u′v′∈g) conuu′
  = conPairsg uv∈g u′v′∈g conuu′
