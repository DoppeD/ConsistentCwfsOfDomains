module Cwf.DomainCwf.UniType.ConLub where

open import Base.Core
open import Base.FinFun
open import Cwf.DomainCwf.UniType.Coherence
open import Cwf.DomainCwf.UniType.Consistency
open import Cwf.DomainCwf.UniType.ConsistencyLemmata
open import Cwf.DomainCwf.UniType.Definition
open import Cwf.DomainCwf.UniType.Relation
open import Cwf.DomainCwf.UniType.RelationLemmata

open import Agda.Builtin.Equality

⊔-assoc : ∀ {u v w} → con (u ⊔ v) → con (v ⊔ w) →
          ((u ⊔ v) ⊔ w) ≡ (u ⊔ (v ⊔ w))
⊔-assoc {⊥} _ _ = refl
⊔-assoc {0ᵤ} {⊥} _ _ = refl
⊔-assoc {0ᵤ} {0ᵤ} {⊥} _ _ = refl
⊔-assoc {0ᵤ} {0ᵤ} {0ᵤ} _ _ = refl
⊔-assoc {s _} {⊥} _ _ = refl
⊔-assoc {s _} {s _} {⊥} _ _ = refl
⊔-assoc {s u} {s _} {s _} conuv convw
  rewrite (⊔-assoc {u} conuv convw) = refl
⊔-assoc {ℕ} {⊥} _ _ = refl
⊔-assoc {ℕ} {ℕ} {⊥} _ _ = refl
⊔-assoc {ℕ} {ℕ} {ℕ} _ _ = refl
⊔-assoc {F _} {⊥} _ _ = refl
⊔-assoc {F _} {F _} {⊥} _ _ = refl
⊔-assoc {F f} {F g} {F h} _ _
  rewrite (∪-assoc {𝑓 = f} {g} {h}) = refl
⊔-assoc {refl _} {⊥} _ _ = refl
⊔-assoc {refl _} {refl _} {⊥} _ _ = refl
⊔-assoc {refl u} {refl _} {refl _} conuv convw
  rewrite (⊔-assoc {u} conuv convw) = refl
⊔-assoc {I _ _ _} {⊥} _ _ = refl
⊔-assoc {I _ _ _} {I _ _ _} {⊥} _ _ = refl
⊔-assoc {I U u v} {I _ _ _} {I _ _ _} (conUU′ , (conuu′ , convv′)) (conU′U″ , (conu′u″ , conv′v″))
  rewrite (⊔-assoc {U} conUU′ conU′U″)
  rewrite (⊔-assoc {u} conuu′ conu′u″)
  rewrite (⊔-assoc {v} convv′ conv′v″)
  = refl
⊔-assoc {Π _ _} {⊥} _ _ = refl
⊔-assoc {Π _ _} {Π _ _} {⊥} _ _ = refl
⊔-assoc {Π u f} {Π _ g} {Π _ h} (conuv , _) (convw , _)
  rewrite (⊔-assoc {u} conuv convw)
  rewrite (∪-assoc {𝑓 = f} {g} {h}) = refl
⊔-assoc {𝒰} {⊥} _ _ = refl
⊔-assoc {𝒰} {𝒰} {⊥} _ _ = refl
⊔-assoc {𝒰} {𝒰} {𝒰} _ _ = refl

preUnionLemma' : ∀ {f g} → con (pre f ⊔ pre g) → pre (f ∪ g) ≡ pre f ⊔ pre g
preUnionLemma' {∅} _ = refl
preUnionLemma' {(u , v) ∷ f′} conprefg with (conLemma₁ {pre ((u , v) ∷ f′)} conprefg)
preUnionLemma' {(u , v) ∷ f′} conprefg | conpref with (conLemma₂ {u} conpref)
preUnionLemma' {(u , v) ∷ f′} {g} conprefg | conpref | conpref′
  rewrite (⊔-assoc {u} conpref (conLemma₂ {u} (conAssoc₂ {u} conprefg)))
  rewrite (preUnionLemma' {f′} {g} (conLemma₂ {u} (conAssoc₂ {u} conprefg)))
  = refl

preUnionLemma : ∀ {f g} → con (pre f ⊔ pre g) → con (pre (f ∪ g))
preUnionLemma {f} {g} conprefg
  rewrite (preUnionLemma' {f} {g} conprefg)
  = conprefg

postUnionLemma : ∀ {f g} → con (post f) → con (post (f ∪ g)) → con (post f ⊔ post g)
postUnionLemma' : ∀ {f g} → con (post f) → con (post (f ∪ g)) → post f ⊔ post g ≡ post (f ∪ g)

postUnionLemma {f} {g} conpostf conpostfg
  rewrite (postUnionLemma' {f = f} {g} conpostf conpostfg)
  = conpostfg

postUnionLemma' {∅} _ _ = refl
postUnionLemma' {(u , v) ∷ f′} conpostf conpostfg
  rewrite (⊔-assoc {v} conpostf
          (postUnionLemma {f′} (conLemma₂ {v} conpostf) (conLemma₂ {v} conpostfg)))
  rewrite (postUnionLemma' {f′} (conLemma₂ {v} conpostf) (conLemma₂ {v} conpostfg))
  = refl

Con-⊔ : ∀ {u v w} → u ⊑ w → v ⊑ w → con (u ⊔ v)
Con-⊔' : ∀ {f g h u v u′ v′} →
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
Con-⊔ {F f} {F g} {F h} (⊑-F conf conh p₁) (⊑-F cong _ p₂)
  = (λ uv∈∪ u′v′∈∪ → Con-⊔' {f} conf cong conh (lemma uv∈∪) (lemma u′v′∈∪) (∪-lemma₂ uv∈∪) (∪-lemma₂ u′v′∈∪)) , lemma₂
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
Con-⊔ {Π _ f} {Π _ g} {Π _ h} (⊑-Π u⊑w (⊑-F conf conh p₁)) (⊑-Π v⊑w (⊑-F cong _ p₂))
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
  record { sub = sub ; sub⊆g = sub⊆g ; pre⊑u = pre⊑u ; v⊑post = v⊑post }
  record { sub = sub′ ; sub⊆g = sub⊆g′ ; pre⊑u = pre⊑u′ ; v⊑post = v⊑post′ }
  (inl uv∈f) (inr u′v′∈g) conuu′
  = Con-⊔ {v} {v′} (⊑-⊔-lemma₁ v⊑post conpostsubs) (⊑-⊔-lemma₂ v⊑post′ conpostsubs)
  where conpresubs : con (pre sub ⊔ pre sub′)
        conpresubs = Con-⊔ (⊑-⊔-lemma₁ pre⊑u conuu′) (⊑-⊔-lemma₂ pre⊑u′ conuu′)
        conpostsub : con (post sub)
        conpostsub = coherence {f = sub} (subsetIsCon sub⊆g conh) (⊠-fst (orderOnlyCon pre⊑u))
        conpost∪ : con (post (sub ∪ sub′))
        conpost∪ = (coherence (subsetIsCon (∪-lemma₁ sub⊆g sub⊆g′) conh) (preUnionLemma  {f = sub} conpresubs))
        conpostsubs : con (post sub ⊔ post sub′)
        conpostsubs = postUnionLemma {sub} conpostsub conpost∪
Con-⊔' {u = u} {v} {u′} {v′} _ _ conh
  record { sub = sub ; sub⊆g = sub⊆g ; pre⊑u = pre⊑u ; v⊑post = v⊑post }
  record { sub = sub′ ; sub⊆g = sub⊆g′ ; pre⊑u = pre⊑u′ ; v⊑post = v⊑post′ }
  (inr uv∈g) (inl uv∈f) conuu′
  = Con-⊔ {v} {v′} (⊑-⊔-lemma₁ v⊑post conpostsubs) (⊑-⊔-lemma₂ v⊑post′ conpostsubs)
  where conpresubs : con (pre sub ⊔ pre sub′)
        conpresubs = Con-⊔ (⊑-⊔-lemma₁ pre⊑u conuu′) (⊑-⊔-lemma₂ pre⊑u′ conuu′)
        conpostsub : con (post sub)
        conpostsub = coherence {sub} (subsetIsCon sub⊆g conh) (⊠-fst (orderOnlyCon pre⊑u))
        conpost∪ : con (post (sub ∪ sub′))
        conpost∪ = (coherence (subsetIsCon (∪-lemma₁ sub⊆g sub⊆g′) conh) (preUnionLemma  {sub} conpresubs))
        conpostsubs : con (post sub ⊔ post sub′)
        conpostsubs = postUnionLemma {sub} conpostsub conpost∪
Con-⊔' (conPairsf , _)  _ _ _ _ (inl uv∈f) (inl u′v′∈f) conuu′
  = conPairsf uv∈f u′v′∈f conuu′
Con-⊔' _ (conPairsg , _) _ _ _ (inr uv∈g) (inr u′v′∈g) conuu′
  = conPairsg uv∈g u′v′∈g conuu′
