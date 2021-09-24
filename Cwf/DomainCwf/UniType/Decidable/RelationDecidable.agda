module Cwf.DomainCwf.UniType.Decidable.RelationDecidable where

open import Base.Core
open import Base.FinFun
open import Cwf.DomainCwf.UniType.AxiomProofs
open import Cwf.DomainCwf.UniType.Coherence
open import Cwf.DomainCwf.UniType.ConLub
open import Cwf.DomainCwf.UniType.Consistency
open import Cwf.DomainCwf.UniType.ConsistencyLemmata
open import Cwf.DomainCwf.UniType.Decidable.ConsistencyDecidable
open import Cwf.DomainCwf.UniType.Decidable.EqualityDecidable
open import Cwf.DomainCwf.UniType.Definition
open import Cwf.DomainCwf.UniType.Relation
open import Cwf.DomainCwf.UniType.RelationLemmata
--open import Cwf.DomainCwf.UniType.Transitivity

open import Agda.Builtin.Equality

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

FrelationDecidable' : ∀ {i} → {f g : FinFun {i}} → conFinFun f → conFinFun g →
                      ({u v : Nbh {i}} → Decidable (u ⊑ v)) →
                      {u v : Nbh {i}} → (u , v) ∈ f → Decidable (⊑-proof g u v)
FrelationDecidable' {g = g} (_ , conElemsf) _ dec {u} uv∈f
  with (largest g u (⊠-fst (conElemsf uv∈f)) dec)
FrelationDecidable' _ _ dec {u} {v} _ | record { sub = sub }
  with (dec {v} {post sub})
FrelationDecidable' {g = _} _ _ _ _
  | record { sub = sub ; sub⊆f = sub⊆g ; pre⊑w = pre⊑u ; allSmallerw = allSmallerw } | inl v⊑postsub
  = inl (record { sub = sub ; sub⊆g = sub⊆g ; pre⊑u = pre⊑u ; v⊑post = v⊑postsub })
FrelationDecidable' {f = f} {g} (_ , conElemsf) cong _ {u} {v} uv∈f
  | record { sub = sub ; sub⊆f = sub⊆g ; pre⊑w = pre⊑u ; allSmallerw = allSmallerw } | inr ¬v⊑postsub
  = inr lemma
  where lrg : Largest g u
        lrg = record { sub = sub ; sub⊆f = sub⊆g ; pre⊑w = pre⊑u ; allSmallerw = allSmallerw }
        lemma : ¬ (⊑-proof g u v)
        lemma record { sub = sub′ ; sub⊆g = sub⊆g′ ; pre⊑u = pre⊑u′ ; v⊑post = v⊑post′ }
          = ¬v⊑postsub (⊑-trans v⊑post′ (isLargest cong {u} {⊠-fst (conElemsf uv∈f)} lrg sub⊆g′ pre⊑u′))

FrelationDecidable : ∀ {i} → {f g : FinFun {i}} → ({u v : Nbh {i}} → Decidable (u ⊑ v)) →
                     Decidable ((F f) ⊑ (F g))
FrelationDecidable {f = f} {g} _ with
  (consistencyDecidable {u = F f}) | consistencyDecidable {u = F g}
FrelationDecidable {f = f} {g} p | inl conf | inr ¬cong = inr lemma
  where lemma : ¬ (F f ⊑ F g)
        lemma (⊑-F _ cong _) = ¬cong cong
FrelationDecidable {f = f} {g} p | inr ¬conf | _ = inr lemma
  where lemma : ¬ (F f ⊑ F g)
        lemma (⊑-F conf _ _) = ¬conf conf
FrelationDecidable {f = ∅} {g} p | inl conf | inl cong
  = inl (⊑-F ((λ uv∈∅ _ _ → xy∈∅-abs uv∈∅) , xy∈∅-abs) cong xy∈∅-abs)
FrelationDecidable {f = (u , v) ∷ f′} {g} p | inl conf | inl cong
  with (FrelationDecidable' {f = (u , v) ∷ f′} {g} conf cong p here) | FrelationDecidable {f = f′} {g} p
FrelationDecidable {f = (u , v) ∷ f′} {g} _ | inl conf | inl cong | inl ⊑-p₁ | inl (⊑-F _ _ ⊑-p₂)
  = inl (⊑-F conf cong lemma)
  where lemma : ∀ {u′ v′} → (u′ , v′) ∈ ((u , v) ∷ f′) → ⊑-proof g u′ v′
        lemma here = ⊑-p₁
        lemma (there u′v′∈f′) = ⊑-p₂ u′v′∈f′
FrelationDecidable {f = (u , v) ∷ f′} {g} _ | inl conf | inl cong | inl ⊑-p₁ | inr ¬⊑-p₂ = inr lemma
  where lemma : ¬ (F ((u , v) ∷ f′) ⊑ F g)
        lemma (⊑-F _ _ ⊑-p₂) = ¬⊑-p₂ (⊑-F (subsetIsCon ⊆-lemma₃ conf) cong λ u′v′∈f′ → ⊑-p₂ (there u′v′∈f′))
FrelationDecidable {f = (u , v) ∷ f′} {g} _ | inl conf | inl cong | inr ¬⊑-p₁ | _ = inr lemma
  where lemma : ¬ (F ((u , v) ∷ f′) ⊑ F g)
        lemma (⊑-F _ _ ⊑-p₂) = ¬⊑-p₁ (⊑-p₂ here)

0relationDecidable : ∀ {i} → {v : Nbh {i}} → Decidable (0ᵤ ⊑ v)
0relationDecidable {v = ⊥} = inr lemma
  where lemma : ¬ (0ᵤ ⊑ ⊥)
        lemma ()
0relationDecidable {v = 0ᵤ} = inl ⊑-0
0relationDecidable {v = s v} = inr lemma
  where lemma : ¬ (0ᵤ ⊑ s v)
        lemma ()
0relationDecidable {v = ℕ} = inr lemma
  where lemma : ¬ (0ᵤ ⊑ ℕ)
        lemma ()
0relationDecidable {v = F f} = inr lemma
  where lemma : ¬ (0ᵤ ⊑ F f)
        lemma ()
0relationDecidable {v = refl v} = inr lemma
  where lemma : ¬ (0ᵤ ⊑ refl v)
        lemma ()
0relationDecidable {v = I U u v} = inr lemma
  where lemma : ¬ (0ᵤ ⊑ I U u v)
        lemma ()
0relationDecidable {v = Π U f} = inr lemma
  where lemma : ¬ (0ᵤ ⊑ Π U f)
        lemma ()
0relationDecidable {v = 𝒰} = inr lemma
  where lemma : ¬ (0ᵤ ⊑ 𝒰)
        lemma ()
0relationDecidable {v = incons} = inr lemma
  where lemma : ¬ (0ᵤ ⊑ incons)
        lemma ()

ℕrelationDecidable : ∀ {i} → {v : Nbh {i}} → Decidable (ℕ ⊑ v)
ℕrelationDecidable {v = ⊥} = inr lemma
  where lemma : ¬ (ℕ ⊑ ⊥)
        lemma ()
ℕrelationDecidable {v = 0ᵤ} = inr lemma
  where lemma : ¬ (ℕ ⊑ 0ᵤ)
        lemma ()
ℕrelationDecidable {v = s v} = inr lemma
  where lemma : ¬ (ℕ ⊑ s v)
        lemma ()
ℕrelationDecidable {v = ℕ} = inl ⊑-ℕ
ℕrelationDecidable {v = F f} = inr lemma
  where lemma : ¬ (ℕ ⊑ F f)
        lemma ()
ℕrelationDecidable {v = refl v} = inr lemma
  where lemma : ¬ (ℕ ⊑ refl v)
        lemma ()
ℕrelationDecidable {v = I U u v} = inr lemma
  where lemma : ¬ (ℕ ⊑ I U u v)
        lemma ()
ℕrelationDecidable {v = Π U f} = inr lemma
  where lemma : ¬ (ℕ ⊑ Π U f)
        lemma ()
ℕrelationDecidable {v = 𝒰} = inr lemma
  where lemma : ¬ (ℕ ⊑ 𝒰)
        lemma ()
ℕrelationDecidable {v = incons} = inr lemma
  where lemma : ¬ (ℕ ⊑ incons)
        lemma ()

𝒰relationDecidable : ∀ {i} → {v : Nbh {i}} → Decidable (𝒰 ⊑ v)
𝒰relationDecidable {v = ⊥} = inr lemma
  where lemma : ¬ (𝒰 ⊑ ⊥)
        lemma ()
𝒰relationDecidable {v = 0ᵤ} = inr lemma
  where lemma : ¬ (𝒰 ⊑ 0ᵤ)
        lemma ()
𝒰relationDecidable {v = s v} = inr lemma
  where lemma : ¬ (𝒰 ⊑ s v)
        lemma ()
𝒰relationDecidable {v = ℕ} = inr lemma
  where lemma : ¬ (𝒰 ⊑ ℕ)
        lemma ()
𝒰relationDecidable {v = F f} = inr lemma
  where lemma : ¬ (𝒰 ⊑ F f)
        lemma ()
𝒰relationDecidable {v = refl v} = inr lemma
  where lemma : ¬ (𝒰 ⊑ refl v)
        lemma ()
𝒰relationDecidable {v = I U u v} = inr lemma
  where lemma : ¬ (𝒰 ⊑ I U u v)
        lemma ()
𝒰relationDecidable {v = Π U f} = inr lemma
  where lemma : ¬ (𝒰 ⊑ Π U f)
        lemma ()
𝒰relationDecidable {v = 𝒰} = inl ⊑-𝒰
𝒰relationDecidable {v = incons} = inr lemma
  where lemma : ¬ (𝒰 ⊑ incons)
        lemma ()

relationDecidable : ∀ {i} → {u v : Nbh {i}} → Decidable (u ⊑ v)
relationDecidable {u = ⊥} {v} with (consistencyDecidable {u = v})
... | inl conv = inl (⊑-bot conv)
... | inr ¬conv = inr lemma
  where lemma : ¬ (⊥ ⊑ v)
        lemma (⊑-bot conv) = ¬conv conv
relationDecidable {u = 0ᵤ} {v} = 0relationDecidable
relationDecidable {u = s u} {⊥} = inr lemma
  where lemma : ¬ (s u ⊑ ⊥)
        lemma ()
relationDecidable {u = s u} {0ᵤ} = inr lemma
  where lemma : ¬ (s u ⊑ 0ᵤ)
        lemma ()
relationDecidable {u = s u} {s v}
  with (relationDecidable {u = u} {v})
... | inl u⊑v = inl (⊑-s u⊑v)
... | inr ¬u⊑v = inr lemma
  where lemma : ¬ (s u ⊑ s v)
        lemma (⊑-s u⊑v) = ¬u⊑v u⊑v
relationDecidable {u = s u} {ℕ} = inr lemma
  where lemma : ¬ (s u ⊑ ℕ)
        lemma ()
relationDecidable {u = s u} {F f} = inr lemma
  where lemma : ¬ (s u ⊑ F f)
        lemma ()
relationDecidable {u = s u} {refl v} = inr lemma
  where lemma : ¬ (s u ⊑ refl v)
        lemma ()
relationDecidable {u = s u} {I U v v′} = inr lemma
  where lemma : ¬ (s u ⊑ I U v v′)
        lemma ()
relationDecidable {u = s u} {Π U f} = inr lemma
  where lemma : ¬ (s u ⊑ Π U f)
        lemma ()
relationDecidable {u = s u} {𝒰} = inr lemma
  where lemma : ¬ (s u ⊑ 𝒰)
        lemma ()
relationDecidable {u = s u} {incons} = inr lemma
  where lemma : ¬ (s u ⊑ incons)
        lemma ()
relationDecidable {u = ℕ} {v} = ℕrelationDecidable
relationDecidable {u = F f} {⊥} = inr lemma
  where lemma : ¬ (F f ⊑ ⊥)
        lemma ()
relationDecidable {u = F f} {0ᵤ} = inr lemma
  where lemma : ¬ (F f ⊑ 0ᵤ)
        lemma ()
relationDecidable {u = F f} {s v} = inr lemma
  where lemma : ¬ (F f ⊑ s v)
        lemma ()
relationDecidable {u = F f} {ℕ} = inr lemma
  where lemma : ¬ (F f ⊑ ℕ)
        lemma ()
relationDecidable {u = F f} {F g}
  = FrelationDecidable {f = f} {g} (λ {u} {v} → relationDecidable {u = u} {v})
relationDecidable {u = F f} {refl v} = inr lemma
  where lemma : ¬ (F f ⊑ refl v)
        lemma ()
relationDecidable {u = F f} {I U u v} = inr lemma
  where lemma : ¬ (F f ⊑ I U u v)
        lemma ()
relationDecidable {u = F f} {Π U g} = inr lemma
  where lemma : ¬ (F f ⊑ Π U g)
        lemma ()
relationDecidable {u = F f} {𝒰} = inr lemma
  where lemma : ¬ (F f ⊑ 𝒰)
        lemma ()
relationDecidable {u = F f} {incons} = inr lemma
  where lemma : ¬ (F f ⊑ incons)
        lemma ()
relationDecidable {u = refl u} {⊥} = inr lemma
  where lemma : ¬ (refl u ⊑ ⊥)
        lemma ()
relationDecidable {u = refl u} {0ᵤ} = inr lemma
  where lemma : ¬ (refl u ⊑ 0ᵤ)
        lemma ()
relationDecidable {u = refl u} {s v} = inr lemma
  where lemma : ¬ (refl u ⊑ s v)
        lemma ()
relationDecidable {u = refl u} {ℕ} = inr lemma
  where lemma : ¬ (refl u ⊑ ℕ)
        lemma ()
relationDecidable {u = refl u} {F f} = inr lemma
  where lemma : ¬ (refl u ⊑ F f)
        lemma ()
relationDecidable {u = refl u} {refl v}
  with (relationDecidable {u = u} {v})
... | inl u⊑v = inl (⊑-rfl u⊑v)
... | inr ¬u⊑v = inr lemma
  where lemma : ¬ (refl u ⊑ refl v)
        lemma (⊑-rfl u⊑v) = ¬u⊑v u⊑v
relationDecidable {u = refl u} {I U v v′} = inr lemma
  where lemma : ¬ (refl u ⊑ I U v v′)
        lemma ()
relationDecidable {u = refl u} {Π U f} = inr lemma
  where lemma : ¬ (refl u ⊑ Π U f)
        lemma ()
relationDecidable {u = refl u} {𝒰} = inr lemma
  where lemma : ¬ (refl u ⊑ 𝒰)
        lemma ()
relationDecidable {u = refl u} {incons} = inr lemma
  where lemma : ¬ (refl u ⊑ incons)
        lemma ()
relationDecidable {u = I U u u′} {⊥} = inr lemma
  where lemma : ¬ (I U u u′ ⊑ ⊥)
        lemma ()
relationDecidable {u = I U u u′} {0ᵤ} = inr lemma
  where lemma : ¬ (I U u u′ ⊑ 0ᵤ)
        lemma ()
relationDecidable {u = I U u u′} {s v} = inr lemma
  where lemma : ¬ (I U u u′ ⊑ s v)
        lemma ()
relationDecidable {u = I U u u′} {ℕ} = inr lemma
  where lemma : ¬ (I U u u′ ⊑ ℕ)
        lemma ()
relationDecidable {u = I U u u′} {F f} = inr lemma
  where lemma : ¬ (I U u u′ ⊑ F f)
        lemma ()
relationDecidable {u = I U u u′} {refl v} = inr lemma
  where lemma : ¬ (I U u u′ ⊑ refl v)
        lemma ()
relationDecidable {u = I U u u′} {I V v v′}
  with (relationDecidable {u = U} {V}) | relationDecidable {u = u} {v} | relationDecidable {u = u′} {v′}
... | inl U⊑V | inl u⊑v | inl u′⊑v′ = inl (⊑-I U⊑V u⊑v u′⊑v′)
... | inl U⊑V | inl u⊑v | inr ¬u′⊑v′ = inr lemma
  where lemma : ¬ (I U u u′ ⊑ I V v v′)
        lemma (⊑-I _ _ u′⊑v′) = ¬u′⊑v′ u′⊑v′
... | inl U⊑V | inr ¬u⊑v | _ = inr lemma
  where lemma : ¬ (I U u u′ ⊑ I V v v′)
        lemma (⊑-I _ u⊑v _) = ¬u⊑v u⊑v
... | inr ¬U⊑V | _ | _ = inr lemma
  where lemma : ¬ (I U u u′ ⊑ I V v v′)
        lemma (⊑-I U⊑V _ _) = ¬U⊑V U⊑V
relationDecidable {u = I U u u′} {Π V f} = inr lemma
  where lemma : ¬ (I U u u′ ⊑ Π V f)
        lemma ()
relationDecidable {u = I U u u′} {𝒰} = inr lemma
  where lemma : ¬ (I U u u′ ⊑ 𝒰)
        lemma ()
relationDecidable {u = I U u u′} {incons} = inr lemma
  where lemma : ¬ (I U u u′ ⊑ incons)
        lemma ()
relationDecidable {u = Π U f} {⊥} = inr lemma
  where lemma : ¬ (Π U f ⊑ ⊥)
        lemma ()
relationDecidable {u = Π U f} {0ᵤ} = inr lemma
  where lemma : ¬ (Π U f ⊑ 0ᵤ)
        lemma ()
relationDecidable {u = Π U f} {s v} = inr lemma
  where lemma : ¬ (Π U f ⊑ s v)
        lemma ()
relationDecidable {u = Π U f} {ℕ} = inr lemma
  where lemma : ¬ (Π U f ⊑ ℕ)
        lemma ()
relationDecidable {u = Π U f} {F g} = inr lemma
  where lemma : ¬ (Π U f ⊑ F g)
        lemma ()
relationDecidable {u = Π U f} {refl v} = inr lemma
  where lemma : ¬ (Π U f ⊑ refl v)
        lemma ()
relationDecidable {u = Π U f} {I V u v} = inr lemma
  where lemma : ¬ (Π U f ⊑ I V u v)
        lemma ()
relationDecidable {u = Π U f} {Π V g}
  with (relationDecidable {u = U} {V}) | FrelationDecidable {f = f} {g} (λ {u} {v} → relationDecidable {u = u} {v})
... | inl U⊑V | inl f⊑g = inl (⊑-Π U⊑V f⊑g)
... | inl U⊑V | inr ¬f⊑g = inr lemma
  where lemma : ¬ (Π U f ⊑ Π V g)
        lemma (⊑-Π _ f⊑g) = ¬f⊑g f⊑g
... | inr ¬U⊑V | _ = inr lemma
  where lemma : ¬ (Π U f ⊑ Π V g)
        lemma (⊑-Π U⊑V _) = ¬U⊑V U⊑V
relationDecidable {u = Π U f} {𝒰} = inr lemma
  where lemma : ¬ (Π U f ⊑ 𝒰)
        lemma ()
relationDecidable {u = Π U f} {incons} = inr lemma
  where lemma : ¬ (Π U f ⊑ incons)
        lemma ()
relationDecidable {u = 𝒰} {v} = 𝒰relationDecidable
relationDecidable {u = incons} {v} = inr lemma
  where lemma : ¬ (incons ⊑ v)
        lemma ()
