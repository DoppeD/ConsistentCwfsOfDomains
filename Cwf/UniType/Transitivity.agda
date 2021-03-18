module Cwf.UniType.Transitivity where

open import Base.Core
open import Cwf.UniType.AxiomProofs
open import Cwf.UniType.Coherence
open import Cwf.UniType.Consistency
open import Cwf.UniType.Definition
open import Cwf.UniType.FinFun
open import Cwf.UniType.Relation

open import Agda.Builtin.Equality

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

∪-assoc : ∀ {i} → {f g h : FinFun {i}} → (f ∪ (g ∪ h)) ≡ ((f ∪ g) ∪ h)
∪-assoc {f = ∅} {g} {h} = refl
∪-assoc {f = _ ∷ f} {g} {h} rewrite (∪-assoc {f = f} {g} {h}) = refl

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
⊔-assoc {u = Π _ _} {⊥} _ _ = refl
⊔-assoc {u = Π _ _} {Π _ _} {⊥} _ _ = refl
⊔-assoc {u = Π u f} {Π _ g} {Π _ h} (conuv , _) (convw , _)
  rewrite (⊔-assoc {u = u} conuv convw)
  rewrite (∪-assoc {f = f} {g} {h}) = refl
⊔-assoc {u = 𝒰} {⊥} _ _ = refl
⊔-assoc {u = 𝒰} {𝒰} {⊥} _ _ = refl
⊔-assoc {u = 𝒰} {𝒰} {𝒰} _ _ = refl

a : ∀ {i} → {f g : FinFun {i}} → con (pre f ⊔ pre g) → pre (f ∪ g) ≡ pre f ⊔ pre g
a {f = ∅} _ = refl
a {f = (u , v) ∷ f′} conprefg with (conLemma₁ {u = pre ((u , v) ∷ f′)} conprefg)
a {f = (u , v) ∷ f′} conprefg | conpref with (conLemma₂ {u = u} conpref)
a {f = (u , v) ∷ f′} {g} conprefg | conpref | conpref′
  rewrite (⊔-assoc {u = u} {pre f′} {pre g} conpref {!!})
  rewrite (a {f = f′} {g} (conLemma₂ {u = u} {pre f′ ⊔ pre g} (conAssoc₂ {u = u} conprefg)))
  = refl

b : ∀ {f g} → con (post f) → post (f ∪ g) ≡ (post f ⊔ post g)
b {∅} conpostf = refl
b {(u , v) ∷ f′} {g} conpostf
  rewrite (⊔-assoc {u = v} {post f′} {post g} conpostf {!!})
  rewrite (b {f′} {g} (conLemma₂ {u = v} conpostf))
  = refl

Ω : ∀ {f g} → F f ⊑ F g → con (pre f) → ⊑-proof g (pre f) (post f)
Ω {f = ∅} _ _
  = record
      { sub = ∅
      ; preable = *
      ; sub⊆g = ∅-isSubset
      ; pre⊑u = ⊑-bot *
      ; v⊑post = ⊑-bot *
      }
Ω {f = (u , v) ∷ f′} {g} (⊑-F conf cong p) conpref
  with (p here) | Ω {f′} (⊑-F (subsetIsCon ⊆-lemma₃ conf) cong (λ u′v′∈f′ → p (there u′v′∈f′))) (conLemma₂ {u = u} conpref)
... | record { sub = sub ; preable = preable ; sub⊆g = sub⊆g ; pre⊑u = pre⊑u ; v⊑post = v⊑post }
    | record { sub = rsub ; preable = rpreable ; sub⊆g = rsub⊆g ; pre⊑u = rpre⊑u ; v⊑post = rv⊑post }
  = record
      { sub = sub ∪ rsub
      ; preable = {!!}
      ; sub⊆g = ∪-lemma₁ sub⊆g rsub⊆g
      ; pre⊑u = lemma₁ (a {f = sub} {!!}) (⊑-⊔-lemma₃ pre⊑u rpre⊑u {!!} conpref)
      ; v⊑post = lemma₂ (b {sub} (coherence (subsetIsCon sub⊆g cong) preable)) (⊑-⊔-lemma₃ v⊑post rv⊑post (coherence conf conpref) {!!})
      }
  where lemma₁ : ∀ {u u′ v} → u′ ≡ u → u ⊑ v → u′ ⊑ v
        lemma₁ refl u⊑v = u⊑v
        lemma₂ : ∀ {u v v′} → v′ ≡ v → u ⊑ v → u ⊑ v′
        lemma₂ refl u⊑v = u⊑v

gf : ∀ {f g h u v} → (F f) ⊑ (F h) → (F g) ⊑ (F h) →
     (u , v) ∈ (f ∪ g) → ⊑-proof h u v
gf {f} (⊑-F _ _ p₁) (⊑-F _ _ p₂) uv∈∪ with (∪-lemma₂ {𝑓 = f} uv∈∪)
... | inl uv∈f = p₁ uv∈f
... | inr uv∈g = p₂ uv∈g

biff : ∀ {i} → {f g : FinFun {i}} → con (pre f ⊔ pre g) → con (pre (f ∪ g))
biff {f = f} {g} conprefg rewrite (a {f = f} {g} conprefg) = conprefg

baff : ∀ {i} → {f g : FinFun {i}} → con (post (f ∪ g)) → con (post f ⊔ post g)
baff {f = f} {g} conpostfg rewrite (b {f = f} {g} {!!}) = {!!}

Con-⊔ : ∀ {i} → {u v w : Nbh {i}} → u ⊑ w → v ⊑ w → con (u ⊔ v)
Con-⊔' : ∀ {i} → {f g h : FinFun {i}} → ∀ {u v u′ v′} → ⊑-proof h u v → ⊑-proof h u′ v′ →
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
  = (λ uv∈∪ u′v′∈∪ → Con-⊔' {f = f} (gf u⊑w v⊑w uv∈∪) (gf u⊑w v⊑w u′v′∈∪) (∪-lemma₂ uv∈∪) (∪-lemma₂ u′v′∈∪)) , {!!}
  where u⊑w = ⊑-F conf conh p₁
        v⊑w = ⊑-F cong conh p₂
Con-⊔ (⊑-Π x x₂) x₁ = {!!}
Con-⊔ ⊑-𝒰 (⊑-bot _) = *
Con-⊔ ⊑-𝒰 ⊑-𝒰 = *

Con-⊔' x x₁ (inl uv∈f) (inl u′v′∈f) conuu′ = {!!}
Con-⊔' {u = u} {v} {u′} {v′} record { sub = sub ; preable = preable ; sub⊆g = sub⊆g ; pre⊑u = pre⊑u ; v⊑post = v⊑post }
  record { sub = sub′ ; preable = preable′ ; sub⊆g = sub⊆g′ ; pre⊑u = pre⊑u′ ; v⊑post = v⊑post′ }
  (inl here) (inr here) conuu′
  = Con-⊔ {u = v} {v′} {post sub ⊔ post sub′} (⊑-⊔-lemma₁ v⊑post def) (⊑-⊔-lemma₂ v⊑post′ def)
  where abc : con (pre sub ⊔ pre sub′)
        abc = Con-⊔ {u = pre sub} {pre sub′} {u ⊔ u′} (⊑-⊔-lemma₁ pre⊑u conuu′) (⊑-⊔-lemma₂ pre⊑u′ conuu′)
        def : con (post sub ⊔ post sub′)
        def = baff {f = sub} {sub′} (coherence {f = sub ∪ sub′} {!!} (biff {f = sub} abc))
Con-⊔' x x₁ (inl here) (inr (there u′v′∈g)) conuu′ = {!!}
Con-⊔' x x₁ (inl (there uv∈f)) (inr here) conuu′ = {!!}
Con-⊔' x x₁ (inl (there uv∈f)) (inr (there u′v′∈g)) conuu′ = {!!}
Con-⊔' x x₁ (inr uv∈g) (inl u′v′∈f) conuu′ = {!!}
Con-⊔' x x₁ (inr uv∈g) (inr u′v′∈g) conuu′ = {!!}
