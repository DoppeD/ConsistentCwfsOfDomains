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
    allSmalleru : {u v : Nbh {i}} → (u , v) ∈ f → u ⊑ w → (u , v) ∈ sub

largest : ∀ {i} → (f : FinFun {i}) → (w : Nbh {i}) → con w →
          (∀ {u v} → (u , v) ∈ f → Decidable (u ⊑ w)) →
          Largest f w
largest {i} ∅ w conw _ =
  record
    { sub = ∅
    ; sub⊆f = ∅-isSubset
    ; pre⊑w = ⊑-bot conw
    ; allSmalleru = xy∈∅-abs
    }
largest ((u , v) ∷ f′) w conw p
  with (p here) | largest f′ w conw λ u′v′∈f′ → p (there u′v′∈f′)
... | inl u⊑w | record { sub = sub ; sub⊆f = sub⊆f ; pre⊑w = pre⊑w ; allSmalleru = allSmalleru }
  = record
      { sub = (u , v) ∷ sub
      ; sub⊆f = ⊆-lemma₄ here (λ u′v′∈sub → there (sub⊆f u′v′∈sub))
      ; pre⊑w = ⊑-⊔ u⊑w pre⊑w (Con-⊔ u⊑w pre⊑w)
      ; allSmalleru = lemma
      }
      where lemma : ∀ {u′ v′} → (u′ , v′) ∈ ((u , v) ∷ f′) → u′ ⊑ w → (u′ , v′) ∈ ((u , v) ∷ sub)
            lemma here _ = here
            lemma (there u′v′∈f′) u′⊑w = there (allSmalleru u′v′∈f′ u′⊑w)
... | inr ¬u⊑w | record { sub = sub ; sub⊆f = sub⊆f ; pre⊑w = pre⊑w ; allSmalleru = allSmalleru }
  = record
      { sub = sub
      ; sub⊆f = λ u′v′∈sub → there (sub⊆f u′v′∈sub)
      ; pre⊑w = pre⊑w
      ; allSmalleru = lemma
      }
      where lemma : ∀ {u′ v′} → (u′ , v′) ∈ ((u , v) ∷ f′) → u′ ⊑ w → (u′ , v′) ∈ sub
            lemma here u′⊑w = ¬-elim (¬u⊑w u′⊑w)
            lemma (there u′v′∈f′) u′⊑w = allSmalleru u′v′∈f′ u′⊑w

preBiggest : ∀ {i} → {f : FinFun {i}} → con (pre f) → {u v : Nbh {i}} → (u , v) ∈ f → u ⊑ pre f
preBiggest conpref here = ⊑-⊔-fst conpref
preBiggest {f = (u′ , v′) ∷ f′} conpref (there uv∈f′) =
  ⊑-⊔-lemma₂ (preBiggest (conLemma₂ {u = u′} conpref) uv∈f′) conpref

isLargest' : ∀ {i} → {f : FinFun {i}} → conFinFun f → {w : Nbh {i}} → (lrg : Largest f w) →
             {g : FinFun {i}} → g ⊆ f → pre g ⊑ w →
             ∀ {u v} → (u , v) ∈ g → v ⊑ post (Largest.sub lrg)
isLargest' conf record { sub = sub ; sub⊆f = sub⊆f ; pre⊑w = pre⊑w ; allSmalleru = allSmalleru } g⊆f preg⊑w uv∈g
  = lemma (allSmalleru (g⊆f uv∈g) (⊑-trans (preBiggest (⊠-fst (orderOnlyCon preg⊑w)) uv∈g) preg⊑w))
          (coherence (subsetIsCon sub⊆f conf)
          (⊠-fst (orderOnlyCon pre⊑w)))
  where lemma : ∀ {i} → {f : FinFun {i}} → {u v : Nbh {i}} → (u , v) ∈ f → con (post f) → v ⊑ post f
        lemma here conpostf = ⊑-⊔-fst conpostf
        lemma {f = (u′ , v′) ∷ f′} (there uv∈f′) conpostf
          = ⊑-⊔-lemma₂ (lemma uv∈f′ (conLemma₂ {u = v′} conpostf)) conpostf

isLargest : ∀ {i} → {f : FinFun {i}} → conFinFun f → {w : Nbh {i}} → {con w} → (lrg : Largest f w) →
            {g : FinFun {i}} → g ⊆ f → pre g ⊑ w →
            post g ⊑ post (Largest.sub lrg)
isLargest conf record { sub = sub ; sub⊆f = sub⊆f ; pre⊑w = pre⊑w ; allSmalleru = allSmalleru } {g = ∅} _ _
  = ⊑-bot (coherence (subsetIsCon sub⊆f conf) (⊠-fst (orderOnlyCon pre⊑w)))
isLargest conf {w} {conw} lrg {g = (u , v) ∷ g′} g⊆f preg⊑w
  = ⊑-⊔ (isLargest' conf lrg g⊆f preg⊑w here)
        (isLargest conf {w} {conw} lrg (⊆-lemma₂ g⊆f) (⊑-trans (⊑-⊔-snd (⊠-fst (orderOnlyCon preg⊑w))) preg⊑w))
        (coherence (subsetIsCon g⊆f conf) (⊠-fst (orderOnlyCon preg⊑w)))

kldfs : ∀ {i} → {f g : FinFun {i}} → conFinFun f → {v : Nbh {i}} →
        (∀ {u′ v′} → (u′ , v′) ∈ f → Decidable (v ⊑ v′)) →
        g ⊆ f → Decidable (v ⊑ post g)
kldfs {g = ∅} _ {v} _ _ with (decidableEquality {u = v} {⊥})
... | inl refl = inl (⊑-bot *)
... | inr ¬v≡⊥ = inr lemma
  where lemma : ¬ (v ⊑ ⊥)
        lemma (⊑-bot _) = ¬v≡⊥ refl
kldfs {g = (u′ , v′) ∷ g′} conf {v} decSnd g⊆f
  with (decSnd (g⊆f here)) | kldfs {g = g′} conf decSnd (⊆-lemma₂ g⊆f)
... | inl v⊑v′ | _ = inl (⊑-⊔-lemma₁ v⊑v′ {!!})
... | inr ¬v⊑v′ | inl v⊑post′ = inl (⊑-⊔-lemma₂ v⊑post′ {!!})
... | inr ¬v⊑v′ | inr ¬v⊑post′ = inr lemma
  where lemma : ¬ (v ⊑ (v′ ⊔ post g′))
        lemma x = {!!} -- If a ⊑ (b ⊔ c) then either a ⊑ b or a ⊑ c is false!

idfso : ∀ {i} → {f g : FinFun {i}} → conFinFun f → conFinFun g →
        {u v : Nbh {i}} → (u , v) ∈ f →
        (∀ {u′ v′} → (u′ , v′) ∈ g → Decidable (u′ ⊑ u)) →
        (∀ {u′ v′} → (u′ , v′) ∈ g → Decidable (v ⊑ v′)) →
        Decidable (⊑-proof g u v)
idfso {g = g} (_ , conElemsf) cong {u = u} {v} uv∈f decFst _
  with (largest g u (⊠-fst (conElemsf uv∈f)) decFst)
idfso {f = f} {g} (_ , conElemsf) cong {u = u} {v} uv∈f decFst decSnd
  | record { sub = sub ; sub⊆f = sub⊆g ; pre⊑w = pre⊑w ; allSmalleru = allSmalleru }
  with (kldfs {f = g} {sub} cong decSnd sub⊆g)
... | inl v⊑post = inl (record { sub = sub ; sub⊆g = sub⊆g ; pre⊑u = pre⊑w ; v⊑post = v⊑post })
... | inr ¬v⊑post = inr lemma
  where lrg : Largest g u
        lrg = record { sub = sub ; sub⊆f = sub⊆g ; pre⊑w = pre⊑w ; allSmalleru = allSmalleru }
        lemma : ¬ (⊑-proof g u v)
        lemma record { sub = sub′ ; sub⊆g = sub⊆g′ ; v⊑post = v⊑post ; pre⊑u = pre⊑u } =
          ¬v⊑post (⊑-trans v⊑post (isLargest {f = g} cong {w = u} {⊠-fst (conElemsf uv∈f)} lrg {g = sub′} sub⊆g′ pre⊑u))

FrelationDecidable : ∀ {i} → {f g : FinFun {i}} → (∀ {u v u′ v′} → (u , v) ∈ f → (u′ , v′) ∈ f → Decidable (u ⊑ u′)) →
                     Decidable ((F f) ⊑ (F g))
FrelationDecidable p = {!!}
-- For every (u , v) ∈ g, if F f ⊑ (F (largest g u)) then (and only then) is F f ⊑ F g.
-- One direction is easy: F (largest g u) ⊑ F g since it is a subset of g, and by transitivity F f ⊑ F g.
-- For the other direction, if F f ⊑ F g, then F f ⊑ (F (largest g u)) by transitivity, because F sub ⊑ F (largest g u)
-- for any sub ⊆ g such that (pre sub) ⊑ w.

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
  = FrelationDecidable {f = f} {g} (\{u} {v} {u′} {v} _ _ → relationDecidable {u = u} {u′})
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
