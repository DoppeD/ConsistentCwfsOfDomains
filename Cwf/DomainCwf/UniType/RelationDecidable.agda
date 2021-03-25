{-# OPTIONS --safe --sized-types #-}

module Cwf.DomainCwf.UniType.RelationDecidable where

open import Base.Core
open import Cwf.DomainCwf.UniType.AxiomProofs
open import Cwf.DomainCwf.UniType.Coherence
open import Cwf.DomainCwf.UniType.ConLub
open import Cwf.DomainCwf.UniType.Consistency
open import Cwf.DomainCwf.UniType.ConsistencyDecidable
open import Cwf.DomainCwf.UniType.ConsistencyLemmata
open import Cwf.DomainCwf.UniType.DecidableEquality
open import Cwf.DomainCwf.UniType.Definition
open import Cwf.DomainCwf.UniType.FinFun
open import Cwf.DomainCwf.UniType.Relation
open import Cwf.DomainCwf.UniType.RelationLemmata
open import Cwf.DomainCwf.UniType.Transitivity

open import Agda.Builtin.Equality
open import Agda.Builtin.Size

record Largest {i : Size} (f : FinFun {i}) (w : Nbh {i}) : Set where
  field
    sub : FinFun {i}
    sub⊆f : sub ⊆ f
    pre⊑w : pre sub ⊑ w
    allSmallerw : {u v : Nbh {i}} → (u , v) ∈ f → u ⊑ w → (u , v) ∈ sub

largest : ∀ {i} → (f : FinFun {i}) → (w : Nbh {i}) → con w →
          ({u v : Nbh {i}} → Decidable (u ⊑ v)) →
          Largest f w
largest {i} ∅ w conw _ =
  record
    { sub = ∅
    ; sub⊆f = ∅-isSubset
    ; pre⊑w = ⊑-bot conw
    ; allSmallerw = xy∈∅-abs
    }
largest ((u , v) ∷ f′) w conw dec
  with (dec {u} {w}) | largest f′ w conw dec
... | inl u⊑w | record { sub = sub ; sub⊆f = sub⊆f ; pre⊑w = pre⊑w ; allSmallerw = allSmallerw }
  = record
      { sub = (u , v) ∷ sub
      ; sub⊆f = ⊆-lemma₄ here (λ u′v′∈sub → there (sub⊆f u′v′∈sub))
      ; pre⊑w = ⊑-⊔ u⊑w pre⊑w (Con-⊔ u⊑w pre⊑w)
      ; allSmallerw = lemma
      }
      where lemma : ∀ {u′ v′} → (u′ , v′) ∈ ((u , v) ∷ f′) → u′ ⊑ w → (u′ , v′) ∈ ((u , v) ∷ sub)
            lemma here _ = here
            lemma (there u′v′∈f′) u′⊑w = there (allSmallerw u′v′∈f′ u′⊑w)
... | inr ¬u⊑w | record { sub = sub ; sub⊆f = sub⊆f ; pre⊑w = pre⊑w ; allSmallerw = allSmallerw }
  = record
      { sub = sub
      ; sub⊆f = λ u′v′∈sub → there (sub⊆f u′v′∈sub)
      ; pre⊑w = pre⊑w
      ; allSmallerw = lemma
      }
      where lemma : ∀ {u′ v′} → (u′ , v′) ∈ ((u , v) ∷ f′) → u′ ⊑ w → (u′ , v′) ∈ sub
            lemma here u′⊑w = ¬-elim (¬u⊑w u′⊑w)
            lemma (there u′v′∈f′) u′⊑w = allSmallerw u′v′∈f′ u′⊑w

preBiggest : ∀ {i} → {f : FinFun {i}} → con (pre f) → {u v : Nbh {i}} → (u , v) ∈ f → u ⊑ pre f
preBiggest conpref here = ⊑-⊔-fst conpref
preBiggest {f = (u′ , v′) ∷ f′} conpref (there uv∈f′) =
  ⊑-⊔-lemma₂ (preBiggest (conLemma₂ {u = u′} conpref) uv∈f′) conpref

isLargest' : ∀ {i} → {f : FinFun {i}} → conFinFun f → {w : Nbh {i}} → (lrg : Largest f w) →
             {g : FinFun {i}} → g ⊆ f → pre g ⊑ w →
             ∀ {u v} → (u , v) ∈ g → v ⊑ post (Largest.sub lrg)
isLargest' conf record { sub = sub ; sub⊆f = sub⊆f ; pre⊑w = pre⊑w ; allSmallerw = allSmallerw } g⊆f preg⊑w uv∈g
  = lemma (allSmallerw (g⊆f uv∈g) (⊑-trans (preBiggest (⊠-fst (orderOnlyCon preg⊑w)) uv∈g) preg⊑w))
          (coherence (subsetIsCon sub⊆f conf)
          (⊠-fst (orderOnlyCon pre⊑w)))
  where lemma : ∀ {i} → {f : FinFun {i}} → {u v : Nbh {i}} → (u , v) ∈ f → con (post f) → v ⊑ post f
        lemma here conpostf = ⊑-⊔-fst conpostf
        lemma {f = (u′ , v′) ∷ f′} (there uv∈f′) conpostf
          = ⊑-⊔-lemma₂ (lemma uv∈f′ (conLemma₂ {u = v′} conpostf)) conpostf

isLargest : ∀ {i} → {f : FinFun {i}} → conFinFun f → {w : Nbh {i}} → {con w} → (lrg : Largest f w) →
            {g : FinFun {i}} → g ⊆ f → pre g ⊑ w →
            post g ⊑ post (Largest.sub lrg)
isLargest conf record { sub = sub ; sub⊆f = sub⊆f ; pre⊑w = pre⊑w ; allSmallerw = allSmallerw } {g = ∅} _ _
  = ⊑-bot (coherence (subsetIsCon sub⊆f conf) (⊠-fst (orderOnlyCon pre⊑w)))
isLargest conf {w} {conw} lrg {g = (u , v) ∷ g′} g⊆f preg⊑w
  = ⊑-⊔ (isLargest' conf lrg g⊆f preg⊑w here)
        (isLargest conf {w} {conw} lrg (⊆-lemma₂ g⊆f) (⊑-trans (⊑-⊔-snd (⊠-fst (orderOnlyCon preg⊑w))) preg⊑w))
        (coherence (subsetIsCon g⊆f conf) (⊠-fst (orderOnlyCon preg⊑w)))

FRelationDecidable' : ∀ {i} → {f g : FinFun {i}} → conFinFun f → conFinFun g →
                      ({u v : Nbh {i}} → Decidable (u ⊑ v)) →
                      {u v : Nbh {i}} → (u , v) ∈ f → Decidable (⊑-proof g u v)
FRelationDecidable' {g = g} (_ , conElemsf) _ dec {u} uv∈f
  with (largest g u (⊠-fst (conElemsf uv∈f)) dec)
FRelationDecidable' _ _ dec {u} {v} _ | record { sub = sub }
  with (dec {v} {post sub})
FRelationDecidable' {g = _} _ _ _ _
  | record { sub = sub ; sub⊆f = sub⊆g ; pre⊑w = pre⊑u ; allSmallerw = allSmallerw } | inl v⊑postsub
  = inl (record { sub = sub ; sub⊆g = sub⊆g ; pre⊑u = pre⊑u ; v⊑post = v⊑postsub })
FRelationDecidable' {f = f} {g} (_ , conElemsf) cong _ {u} {v} uv∈f
  | record { sub = sub ; sub⊆f = sub⊆g ; pre⊑w = pre⊑u ; allSmallerw = allSmallerw } | inr ¬v⊑postsub
  = inr lemma
  where lrg : Largest g u
        lrg = record { sub = sub ; sub⊆f = sub⊆g ; pre⊑w = pre⊑u ; allSmallerw = allSmallerw }
        lemma : ¬ (⊑-proof g u v)
        lemma record { sub = sub′ ; sub⊆g = sub⊆g′ ; pre⊑u = pre⊑u′ ; v⊑post = v⊑post′ }
          = ¬v⊑postsub (⊑-trans v⊑post′ (isLargest cong {u} {⊠-fst (conElemsf uv∈f)} lrg sub⊆g′ pre⊑u′))

FrelationDecidable : ∀ {i} → {f g : FinFun {i}} → ({u v : Nbh {i}} → Decidable (u ⊑ v)) →
                     Decidable ((F f) ⊑ (F g))
FrelationDecidable p = {!!}

relationDecidable : ∀ {i} → {u v : Nbh {i}} → Decidable (u ⊑ v)
relationDecidable {u = ⊥} {v} with (consistencyDecidable {u = v})
... | inl conv = inl (⊑-bot conv)
... | inr ¬conv = inr lemma
  where lemma : ¬ (⊥ ⊑ v)
        lemma (⊑-bot conv) = ¬conv conv
relationDecidable {u = 0ᵤ} {v} = {!!}
relationDecidable {u = s u} {v} = {!!}
relationDecidable {u = ℕ} {v} = {!!}
relationDecidable {u = F f} {⊥} = {!!}
relationDecidable {u = F f} {0ᵤ} = {!!}
relationDecidable {u = F f} {s v} = {!!}
relationDecidable {u = F f} {ℕ} = {!!}
relationDecidable {u = F f} {F g}
  = FrelationDecidable {f = f} {g} (\{u} {v} → relationDecidable {u = u} {v})
relationDecidable {u = F f} {refl v} = {!!}
relationDecidable {u = F f} {I v v₁ v₂} = {!!}
relationDecidable {u = F f} {Π v x₁} = {!!}
relationDecidable {u = F f} {𝒰} = {!!}
relationDecidable {u = F f} {incons} = {!!}
relationDecidable {u = refl u} {v} = {!!}
relationDecidable {u = I U u u′} {v} = {!!}
relationDecidable {u = Π u f} {v} = {!!}
relationDecidable {u = 𝒰} {v} = {!!}
relationDecidable {u = incons} {v} = {!!}
