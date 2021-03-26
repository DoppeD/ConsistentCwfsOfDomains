{-# OPTIONS --safe --sized-types #-}

module Cwf.DomainCwf.UniType.Decidable.TypingAlgorithmDecidable where

open import Base.Core
open import Cwf.DomainCwf.UniType.Decidable.EqualityDecidable
open import Cwf.DomainCwf.UniType.Definition
open import Cwf.DomainCwf.UniType.FinFun
open import Cwf.DomainCwf.UniType.Relation
open import Cwf.DomainCwf.UniType.TypingAlgorithm

open import Agda.Builtin.Equality

0OfTypeIsDecidable : ∀ {i} → {U : Nbh {i}} → Decidable (0ᵤ ˸ U)
0OfTypeIsDecidable {U = ⊥} = inr lemma
  where lemma : ¬ (0ᵤ ˸ ⊥)
        lemma ()
0OfTypeIsDecidable {U = 0ᵤ} = inr lemma
  where lemma : ¬ (0ᵤ ˸ 0ᵤ)
        lemma ()
0OfTypeIsDecidable {U = s u} = inr lemma
  where lemma : ¬ (0ᵤ ˸ s u)
        lemma ()
0OfTypeIsDecidable {U = ℕ} = inl 0:ℕ
0OfTypeIsDecidable {U = F f} = inr lemma
  where lemma : ¬ (0ᵤ ˸ F f)
        lemma ()
0OfTypeIsDecidable {U = refl u} = inr lemma
  where lemma : ¬ (0ᵤ ˸ refl u)
        lemma ()
0OfTypeIsDecidable {U = I U u v} = inr lemma
  where lemma : ¬ (0ᵤ ˸ I U u v)
        lemma ()
0OfTypeIsDecidable {U = Π U f} = inr lemma
  where lemma : ¬ (0ᵤ ˸ Π U f)
        lemma ()
0OfTypeIsDecidable {U = 𝒰} = inr lemma
  where lemma : ¬ (0ᵤ ˸ 𝒰)
        lemma ()
0OfTypeIsDecidable {U = incons} = inr lemma
  where lemma : ¬ (0ᵤ ˸ incons)
        lemma ()

sOfTypeIsDecidable : ∀ {i} → {u U : Nbh {i}} → Decidable (u ˸ U) → Decidable (s u ˸ U)
sOfTypeIsDecidable {u = u} {⊥} _ = inr lemma
  where lemma : ¬ (s u ˸ ⊥)
        lemma ()
sOfTypeIsDecidable {u = u} {0ᵤ} _ = inr lemma
  where lemma : ¬ (s u ˸ 0ᵤ)
        lemma ()
sOfTypeIsDecidable {u = u} {s U} _ = inr lemma
  where lemma : ¬ (s u ˸ s U)
        lemma ()
sOfTypeIsDecidable {u = u} {ℕ} (inl u:N) = inl (s:N u:N)
sOfTypeIsDecidable {u = u} {ℕ} (inr ¬u:N) = inr lemma
  where lemma : ¬ (s u ˸ ℕ)
        lemma (s:N u:N) = ¬u:N u:N
sOfTypeIsDecidable {u = u} {F f} _ = inr lemma
  where lemma : ¬ (s u ˸ F f)
        lemma ()
sOfTypeIsDecidable {u = u} {refl U} _ = inr lemma
  where lemma : ¬ (s u ˸ refl U)
        lemma ()
sOfTypeIsDecidable {u = u} {I U v v′} _ = inr lemma
  where lemma : ¬ (s u ˸ I U v v′)
        lemma ()
sOfTypeIsDecidable {u = u} {Π U f} _ = inr lemma
  where lemma : ¬ (s u ˸ Π U f)
        lemma ()
sOfTypeIsDecidable {u = u} {𝒰} _ = inr lemma
  where lemma : ¬ (s u ˸ 𝒰)
        lemma ()
sOfTypeIsDecidable {u = u} {incons} _ = inr lemma
  where lemma : ¬ (s u ˸ incons)
        lemma ()

ℕOfTypeIsDecidable : ∀ {i} → {U : Nbh {i}} → Decidable (ℕ ˸ U)
ℕOfTypeIsDecidable {U = ⊥} = inr lemma
  where lemma : ¬ (ℕ ˸ ⊥)
        lemma ()
ℕOfTypeIsDecidable {U = 0ᵤ} = inr lemma
  where lemma : ¬ (ℕ ˸ 0ᵤ)
        lemma ()
ℕOfTypeIsDecidable {U = s u} = inr lemma
  where lemma : ¬ (ℕ ˸ s u)
        lemma ()
ℕOfTypeIsDecidable {U = ℕ} = inr lemma
  where lemma : ¬ (ℕ ˸ ℕ)
        lemma ()
ℕOfTypeIsDecidable {U = F f} = inr lemma
  where lemma : ¬ (ℕ ˸ F f)
        lemma ()
ℕOfTypeIsDecidable {U = refl u} = inr lemma
  where lemma : ¬ (ℕ ˸ refl u)
        lemma ()
ℕOfTypeIsDecidable {U = I U u v} = inr lemma
  where lemma : ¬ (ℕ ˸ I U u v)
        lemma ()
ℕOfTypeIsDecidable {U = Π U f} = inr lemma
  where lemma : ¬ (ℕ ˸ Π U f)
        lemma ()
ℕOfTypeIsDecidable {U = 𝒰} = inl ℕ:𝒰
ℕOfTypeIsDecidable {U = incons} = inr lemma
  where lemma : ¬ (ℕ ˸ incons)
        lemma ()

FOfTypeIsDecidable₁ : ∀ {i} → {f : FinFun {i}} → {U : Nbh {i}} →
                      ({u v : Nbh {i}} → Decidable (u ˸ v)) →
                      Decidable (∀ {u v} → (u , v) ∈ f → u ˸ U)
FOfTypeIsDecidable₁ {f = ∅} _ = inl xy∈∅-abs
FOfTypeIsDecidable₁ {f = (u , v) ∷ f′} {U} p
  with (p {u = u} {U}) | FOfTypeIsDecidable₁ {f = f′} {U} p
... | inl u:U | inl rest:U = inl lemma
  where lemma : ∀ {u′ v′} → (u′ , v′) ∈ ((u , v) ∷ f′) → u′ ˸ U
        lemma here = u:U
        lemma (there u′v′∈f′) = rest:U u′v′∈f′
... | inl u:U | inr ¬rest:U = inr λ allu:U → ¬rest:U (λ u′v′∈f′ → allu:U (there u′v′∈f′))
... | inr ¬u:U | _ = inr λ allu:U → ¬u:U (allu:U here)

FOfTypeIsDecidable₂ : ∀ {i} → {f : FinFun {i}} → {U : Nbh {i}} → {g : FinFun {i}} →
                      ({u v : Nbh {i}} → Decidable (u ˸ v)) →
                      Decidable (∀ {u v} → (u , v) ∈ f → v ˸ ap g u)
FOfTypeIsDecidable₂ {f = ∅} _ = inl xy∈∅-abs
FOfTypeIsDecidable₂ {f = (u , v) ∷ f′} {U} {g} p
  with (p {u = v} {ap g u}) | FOfTypeIsDecidable₂ {f = f′} {U} {g} p
... | inl v:apgu | inl rest:apgu = inl lemma
  where lemma : ∀ {u′ v′} → (u′ , v′) ∈ ((u , v) ∷ f′) → v′ ˸ ap g u′
        lemma here = v:apgu
        lemma (there u′v′∈f′) = rest:apgu u′v′∈f′
... | inl v:apgu | inr ¬rest:apgu = inr λ allv:apgu → ¬rest:apgu (λ u′v′∈f′ → allv:apgu (there u′v′∈f′))
... | inr ¬v:apgu | _ = inr λ allv:apgu → ¬v:apgu (allv:apgu here)

IOfTypeIsDecidable : ∀ {i} → {U u v U′ : Nbh {i}} →
                     Decidable (U ˸ 𝒰) → Decidable (u ˸ U) → Decidable (v ˸ U) →
                     Decidable (I U u v ˸ U′)
IOfTypeIsDecidable {U = U} {u} {v} {⊥} _ _ _ = inr lemma
  where lemma : ¬ (I U u v  ˸ ⊥)
        lemma ()
IOfTypeIsDecidable {U = U} {u} {v} {0ᵤ} _ _ _ = inr lemma
  where lemma : ¬ (I U u v  ˸ 0ᵤ)
        lemma ()
IOfTypeIsDecidable {U = U} {u} {v} {ℕ} _ _ _ = inr lemma
  where lemma : ¬ (I U u v  ˸ ℕ)
        lemma ()
IOfTypeIsDecidable {U = U} {u} {v} {s U′} _ _ _ = inr lemma
  where lemma : ¬ (I U u v  ˸ s U′)
        lemma ()
IOfTypeIsDecidable {U = U} {u} {v} {F f} _ _ _ = inr lemma
  where lemma : ¬ (I U u v  ˸ F f)
        lemma ()
IOfTypeIsDecidable {U = U} {u} {v} {refl U′} _ _ _ = inr lemma
  where lemma : ¬ (I U u v  ˸ refl U′)
        lemma ()
IOfTypeIsDecidable {U = U} {u} {v} {I U′ u′ v′} _ _ _ = inr lemma
  where lemma : ¬ (I U u v  ˸ I U′ u′ v′)
        lemma ()
IOfTypeIsDecidable {U = U} {u} {v} {Π U′ f} _ _ _ = inr lemma
  where lemma : ¬ (I U u v  ˸ Π U′ f)
        lemma ()
IOfTypeIsDecidable {U′ = 𝒰} (inl U:𝒰) (inl u:U) (inl v:U) = inl (I:𝒰 U:𝒰 u:U v:U)
IOfTypeIsDecidable {U = U} {u} {v} {𝒰} (inl U:𝒰) (inl u:U) (inr ¬v:U) = inr lemma
  where lemma : ¬ (I U u v ˸ 𝒰)
        lemma (I:𝒰 _ _ v:U) = ¬v:U v:U
IOfTypeIsDecidable {U = U} {u} {v} {𝒰} (inl ¬U:𝒰) (inr ¬u:U) _ = inr lemma
  where lemma : ¬ (I U u v ˸ 𝒰)
        lemma (I:𝒰 _ u:U _) = ¬u:U u:U
IOfTypeIsDecidable {U = U} {u} {v} {𝒰} (inr ¬U:𝒰) _ _ = inr lemma
  where lemma : ¬ (I U u v ˸ 𝒰)
        lemma (I:𝒰 U:𝒰 _ _) = ¬U:𝒰 U:𝒰
IOfTypeIsDecidable {U = U} {u} {v} {incons} _ _ _ = inr lemma
  where lemma : ¬ (I U u v  ˸ incons)
        lemma ()

IsTypeIsDecidable : ∀ {i} → {U : Nbh {i}} → (U Type) ∨ ¬ (U Type)
IsTypeIsDecidable' : ∀ {i} → {U : Nbh {i}} → {f : FinFun {i}} →
                     Decidable (∀ {u V} → (u , V) ∈ f → (u ˸ U) ⊠ (V Type))
OfTypeIsDecidable : ∀ {i} → {u U : Nbh {i}} → (u ˸ U) ∨ ¬ (u ˸ U)
OfTypeIsDecidable' : ∀ {i} → {U : Nbh {i}} → {f : FinFun {i}} →
                     Decidable (∀ {u V} → (u , V) ∈ f → (u ˸ U) ⊠ (V ˸ 𝒰))

IsTypeIsDecidable {U = ⊥} = inr lemma
  where lemma : ¬ (⊥ Type)
        lemma ()
IsTypeIsDecidable {U = 0ᵤ} = inr lemma
  where lemma : ¬ (0ᵤ Type)
        lemma ()
IsTypeIsDecidable {U = s u} = inr lemma
  where lemma : ¬ ((s u) Type)
        lemma ()
IsTypeIsDecidable {U = ℕ} = inl isType-ℕ
IsTypeIsDecidable {U = F f} = inr lemma
  where lemma : ¬ ((F f) Type)
        lemma ()
IsTypeIsDecidable {U = refl u} = inr lemma
  where lemma : ¬ ((refl u) Type)
        lemma ()
IsTypeIsDecidable {U = I U u v}
  with (IsTypeIsDecidable {U = U}) | OfTypeIsDecidable {u = u} {U} | OfTypeIsDecidable {u = v} {U}
... | inl UType | inl u:U | inl v:U = inl (isType-I UType u:U v:U)
... | inl _ | inl _ | inr ¬v:U = inr lemma
  where lemma : ¬ ((I U u v) Type)
        lemma (isType-I _ _ v:U) = ¬v:U v:U
... | inl _ | inr ¬u:U | _ = inr lemma
  where lemma : ¬ ((I U u v) Type)
        lemma (isType-I _ u:U _) = ¬u:U u:U
... | inr ¬UType | _ | _ = inr lemma
  where lemma : ¬ ((I U u v) Type)
        lemma (isType-I UType _ _) = ¬UType UType
IsTypeIsDecidable {U = Π U f} with (IsTypeIsDecidable {U = U}) | IsTypeIsDecidable' {U = U} {f}
... | inl UType | inl p = inl (isType-Π UType p)
... | inl UType | inr ¬p = inr lemma
  where lemma : ¬ ((Π U f) Type)
        lemma (isType-Π _ p) = ¬p p
... | inr ¬UType | _  = inr lemma
  where lemma : ¬ ((Π U f) Type)
        lemma (isType-Π UType _) = ¬UType UType
IsTypeIsDecidable {U = 𝒰} = inl isType-𝒰
IsTypeIsDecidable {U = incons} = inr lemma
  where lemma : ¬ (incons Type)
        lemma ()

IsTypeIsDecidable' {U = U} {∅} = inl xy∈∅-abs
IsTypeIsDecidable' {U = U} {(u , V) ∷ f′}
  with (OfTypeIsDecidable {u = u} {U}) | IsTypeIsDecidable {U = V} | IsTypeIsDecidable' {U = U} {f′}
... | inl u:U | inl VType | inl p = inl (lemma u:U VType p)
  where lemma : u ˸ U → V Type → (∀ {u′ V′} → (u′ , V′) ∈ f′ → (u′ ˸ U) ⊠ (V′ Type)) →
                ∀ {u′ V′} → (u′ , V′) ∈ ((u , V) ∷ f′) → (u′ ˸ U) ⊠ (V′ Type)
        lemma u:U VType _ here = u:U , VType
        lemma _ _ p (there u′V′∈f′) = p u′V′∈f′
... | inl u:U | inl VType | inr ¬p = inr lemma
  where lemma : ¬ (∀ {u′ V′} → (u′ , V′) ∈ ((u , V) ∷ f′) → (u′ ˸ U) ⊠ (V′ Type))
        lemma p = ¬p (λ u′V′∈f′ → p (there u′V′∈f′))
... | inl _ | inr ¬VType | _ = inr lemma
  where lemma : ¬ (∀ {u′ V′} → (u′ , V′) ∈ ((u , V) ∷ f′) → (u′ ˸ U) ⊠ (V′ Type))
        lemma p = ¬VType (⊠-snd (p here))
... | inr ¬u:U | _ | _ = inr lemma
  where lemma : ¬ (∀ {u′ V′} → (u′ , V′) ∈ ((u , V) ∷ f′) → (u′ ˸ U) ⊠ (V′ Type))
        lemma p = ¬u:U (⊠-fst (p here))

OfTypeIsDecidable {u = ⊥} {U} with (IsTypeIsDecidable {U = U})
... | inl UType = inl (⊥:U UType)
... | inr ¬UType = inr lemma
  where lemma : ¬ (⊥ ˸ U)
        lemma (⊥:U UType) = ¬UType UType
OfTypeIsDecidable {u = 0ᵤ} {U} = 0OfTypeIsDecidable
OfTypeIsDecidable {u = s u} {U} = sOfTypeIsDecidable (OfTypeIsDecidable {u = u} {U})
OfTypeIsDecidable {u = ℕ} {U} = ℕOfTypeIsDecidable

OfTypeIsDecidable {u = F f} {⊥} = inr lemma
  where lemma : ¬ (F f ˸ ⊥)
        lemma ()
OfTypeIsDecidable {u = F f} {0ᵤ} = inr lemma
  where lemma : ¬ (F f ˸ 0ᵤ)
        lemma ()
OfTypeIsDecidable {u = F f} {s U} = inr lemma
  where lemma : ¬ (F f ˸ s U)
        lemma ()
OfTypeIsDecidable {u = F f} {ℕ} = inr lemma
  where lemma : ¬ (F f ˸ ℕ)
        lemma ()
OfTypeIsDecidable {u = F f} {F g} = inr lemma
  where lemma : ¬ (F f ˸ F g)
        lemma ()
OfTypeIsDecidable {u = F f} {refl U} = inr lemma
  where lemma : ¬ (F f ˸ refl U)
        lemma ()
OfTypeIsDecidable {u = F f} {I U u v} = inr lemma
  where lemma : ¬ (F f ˸ I U u v)
        lemma ()
OfTypeIsDecidable {u = F f} {Π U g}
  with (FOfTypeIsDecidable₁ {f = f} {U} λ {u} {v} → OfTypeIsDecidable {u = u} {v}) |
       (FOfTypeIsDecidable₂ {f = f} {U} {g} λ {u} {v} → OfTypeIsDecidable {u = u} {v})
... | inl allu:U | inl allv:apgu = inl (F:Π (λ uv∈f → (allu:U uv∈f) , allv:apgu uv∈f))
... | inl allu:U | inr ¬allv:apgu = inr lemma
  where lemma : ¬ (F f ˸ Π U g)
        lemma (F:Π p) = ¬allv:apgu (λ uv∈f → ⊠-snd (p uv∈f))
... | inr ¬allu:U | _ = inr lemma
  where lemma : ¬ (F f ˸ Π U g)
        lemma (F:Π p) = ¬allu:U (λ uv∈f → ⊠-fst (p uv∈f))
OfTypeIsDecidable {u = F f} {𝒰} = inr lemma
  where lemma : ¬ (F f ˸ 𝒰)
        lemma ()
OfTypeIsDecidable {u = F f} {incons} = inr lemma
  where lemma : ¬ (F f ˸ incons)
        lemma ()
OfTypeIsDecidable {u = refl u} {⊥} = inr lemma
  where lemma : ¬ (refl u ˸ ⊥)
        lemma ()
OfTypeIsDecidable {u = refl u} {0ᵤ} = inr lemma
  where lemma : ¬ (refl u ˸ 0ᵤ)
        lemma ()
OfTypeIsDecidable {u = refl u} {s U} = inr lemma
  where lemma : ¬ (refl u ˸ s U)
        lemma ()
OfTypeIsDecidable {u = refl u} {ℕ} = inr lemma
  where lemma : ¬ (refl u ˸ ℕ)
        lemma ()
OfTypeIsDecidable {u = refl u} {F f} = inr lemma
  where lemma : ¬ (refl u ˸ F f)
        lemma ()
OfTypeIsDecidable {u = refl u} {refl U} = inr lemma
  where lemma : ¬ (refl u ˸ refl U)
        lemma ()
OfTypeIsDecidable {u = refl u} {I U v v′}
  with (IsTypeIsDecidable {U = U}) | OfTypeIsDecidable {u = u} {U} |
        equalityDecidable {u = u} {v} | equalityDecidable {u = u} {v′}
... | inl UType | inl u:U | inl refl | inl refl = inl (refl:I UType u:U)
... | inl _ | inl _ | inl refl | inr ¬u≡v′ = inr lemma
  where lemma : ¬ (refl u ˸ I U v v′)
        lemma (refl:I UType u:U) = ¬u≡v′ refl
... | inl UType | inl u:U | inr ¬u≡v | _ = inr lemma
  where lemma : ¬ (refl u ˸ I U v v′)
        lemma (refl:I UType u:U) = ¬u≡v refl
... | inl UType | inr ¬u:U | _ | _ = inr lemma
  where lemma : ¬ (refl u ˸ I U v v′)
        lemma (refl:I UType u:U) = ¬u:U u:U
... | inr ¬UType | _ | _ | _ = inr lemma
  where lemma : ¬ (refl u ˸ I U v v′)
        lemma (refl:I UType u:U) = ¬UType UType
OfTypeIsDecidable {u = refl u} {Π U f} = inr lemma
  where lemma : ¬ (refl u ˸ Π U f)
        lemma ()
OfTypeIsDecidable {u = refl u} {𝒰} = inr lemma
  where lemma : ¬ (refl u ˸ 𝒰)
        lemma ()
OfTypeIsDecidable {u = refl u} {incons} = inr lemma
  where lemma : ¬ (refl u ˸ incons)
        lemma ()
OfTypeIsDecidable {u = I U u v} {U′}
  = IOfTypeIsDecidable (OfTypeIsDecidable {u = U} {𝒰}) (OfTypeIsDecidable {u = u} {U}) (OfTypeIsDecidable {u = v} {U})
OfTypeIsDecidable {u = Π U f} {⊥} = inr lemma
  where lemma : ¬ (Π U f ˸ ⊥)
        lemma ()
OfTypeIsDecidable {u = Π U f} {0ᵤ} = inr lemma
  where lemma : ¬ (Π U f ˸ 0ᵤ)
        lemma ()
OfTypeIsDecidable {u = Π U f} {s U′} = inr lemma
  where lemma : ¬ (Π U f ˸ s U′)
        lemma ()
OfTypeIsDecidable {u = Π U f} {ℕ} = inr lemma
  where lemma : ¬ (Π U f ˸ ℕ)
        lemma ()
OfTypeIsDecidable {u = Π U f} {F g} = inr lemma
  where lemma : ¬ (Π U f ˸ F g)
        lemma ()
OfTypeIsDecidable {u = Π U f} {refl U′} = inr lemma
  where lemma : ¬ (Π U f ˸ refl U′)
        lemma ()
OfTypeIsDecidable {u = Π U f} {I U′ u v} = inr lemma
  where lemma : ¬ (Π U f ˸ I U′ u v)
        lemma ()
OfTypeIsDecidable {u = Π U f} {Π U′ g} = inr lemma
  where lemma : ¬ (Π U f ˸ Π U′ g)
        lemma ()
OfTypeIsDecidable {u = Π U f} {𝒰}
  with (OfTypeIsDecidable {u = U} {𝒰}) | OfTypeIsDecidable' {U = U} {f}
... | inl U:𝒰 | inl p = inl (Π:𝒰 U:𝒰 p)
... | inl U:𝒰 | inr ¬p = inr lemma
  where lemma : ¬ (Π U f ˸ 𝒰)
        lemma (Π:𝒰 _ p) = ¬p p
... | inr ¬U:𝒰 | _ = inr lemma
  where lemma : ¬ (Π U f ˸ 𝒰)
        lemma (Π:𝒰 U:𝒰 _) = ¬U:𝒰 U:𝒰
OfTypeIsDecidable {u = Π U f} {incons} = inr lemma
  where lemma : ¬ (Π U f ˸ incons)
        lemma ()
OfTypeIsDecidable {u = 𝒰} {U} = inr lemma
  where lemma : ¬ (𝒰 ˸ U)
        lemma ()
OfTypeIsDecidable {u = incons} {U} = inr lemma
  where lemma : ¬ (incons ˸ U)
        lemma ()

OfTypeIsDecidable' {U = U} {∅} = inl xy∈∅-abs
OfTypeIsDecidable' {U = U} {(u , V) ∷ f′}
  with (OfTypeIsDecidable {u = u} {U}) | OfTypeIsDecidable {u = V} {𝒰} | OfTypeIsDecidable' {U = U} {f′}
... | inl u:U | inl V:𝒰 | inl p = inl (lemma u:U V:𝒰 p)
  where lemma : u ˸ U → V ˸ 𝒰 → (∀ {u′ V′} → (u′ , V′) ∈ f′ → (u′ ˸ U) ⊠ (V′ ˸ 𝒰)) →
                ∀ {u′ V′} → (u′ , V′) ∈ ((u , V) ∷ f′) → (u′ ˸ U) ⊠ (V′ ˸ 𝒰)
        lemma u:U V:𝒰 _ here = u:U , V:𝒰
        lemma _ _ p (there u′V′∈f′) = p u′V′∈f′
... | inl u:U | inl V:𝒰 | inr ¬p = inr lemma
  where lemma : ¬ (∀ {u′ V′} → (u′ , V′) ∈ ((u , V) ∷ f′) → (u′ ˸ U) ⊠ (V′ ˸ 𝒰))
        lemma p = ¬p (λ u′V′∈f′ → p (there u′V′∈f′))
... | inl u:U | inr ¬V:𝒰 | _ = inr lemma
  where lemma : ¬ (∀ {u′ V′} → (u′ , V′) ∈ ((u , V) ∷ f′) → (u′ ˸ U) ⊠ (V′ ˸ 𝒰))
        lemma p = ¬V:𝒰 (⊠-snd (p here))
... | inr ¬u:U | _ | _ = inr lemma
  where lemma : ¬ (∀ {u′ V′} → (u′ , V′) ∈ ((u , V) ∷ f′) → (u′ ˸ U) ⊠ (V′ ˸ 𝒰))
        lemma p = ¬u:U (⊠-fst (p here))
