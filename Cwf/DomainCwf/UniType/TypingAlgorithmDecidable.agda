module Cwf.DomainCwf.UniType.TypingAlgorithmDecidable where

open import Base.Core
open import Cwf.DomainCwf.UniType.Definition
open import Cwf.DomainCwf.UniType.FinFun
open import Cwf.DomainCwf.UniType.TypingAlgorithm

0OfTypeIsDecidable : ∀ {i} → {U : Nbh {i}} → (0ᵤ ˸ U) ∨ ¬ (0ᵤ ˸ U)
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

sOfTypeIsDecidable : ∀ {i} → {u U : Nbh {i}} → (u ˸ U) ∨ ¬ (u ˸ U) → (s u ˸ U) ∨ ¬ (s u ˸ U)
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

ℕOfTypeIsDecidable : ∀ {i} → {U : Nbh {i}} → (ℕ ˸ U) ∨ ¬ (ℕ ˸ U)
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

reflOfTypeIsDecidable : ∀ {i} → {u U : Nbh {i}} → (u ˸ U) ∨ ¬ (u ˸ U) → (refl u ˸ U) ∨ ¬ (refl u ˸ U)
reflOfTypeIsDecidable {u = u} {⊥} _ = inr lemma
  where lemma : ¬ (refl u ˸ ⊥)
        lemma ()
reflOfTypeIsDecidable {u = u} {0ᵤ} _ = inr lemma
  where lemma : ¬ (refl u ˸ 0ᵤ)
        lemma ()
reflOfTypeIsDecidable {u = u} {s U} _ = inr lemma
  where lemma : ¬ (refl u ˸ s U)
        lemma ()
reflOfTypeIsDecidable {u = u} {ℕ} _ = inr lemma
  where lemma : ¬ (refl u ˸ ℕ)
        lemma ()
reflOfTypeIsDecidable {u = u} {F f} _ = inr lemma
  where lemma : ¬ (refl u ˸ F f)
        lemma ()
reflOfTypeIsDecidable {u = u} {refl U} _ = inr lemma
  where lemma : ¬ (refl u ˸ refl U)
        lemma ()
reflOfTypeIsDecidable {u = u} {I U v v′} (inl u:IUvv′) = inl {!!}
reflOfTypeIsDecidable {u = u} {I U v v′} (inr ¬u:IUvv′) = {!!}
reflOfTypeIsDecidable {u = u} {Π U f} _ = inr lemma
  where lemma : ¬ (refl u ˸ Π U f)
        lemma ()
reflOfTypeIsDecidable {u = u} {𝒰} _ = inr lemma
  where lemma : ¬ (refl u ˸ 𝒰)
        lemma ()
reflOfTypeIsDecidable {u = u} {incons} _ = inr lemma
  where lemma : ¬ (refl u ˸ incons)
        lemma ()

IsTypeIsDecidable : ∀ {i} → {U : Nbh {i}} → (U Type) ∨ ¬ (U Type)
IsTypeIsDecidable' : ∀ {i} → {U : Nbh {i}} → {f : FinFun {i}} →
                     (∀ {u V} → (u , V) ∈ f → (u ˸ U) ⊠ (V Type)) ∨ ¬ (∀ {u V} → (u , V) ∈ f → (u ˸ U) ⊠ (V Type))
OfTypeIsDecidable : ∀ {i} → {u U : Nbh {i}} → (u ˸ U) ∨ ¬ (u ˸ U)

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
OfTypeIsDecidable {u = F f} {U} = {!!}
OfTypeIsDecidable {u = refl u} {U} = reflOfTypeIsDecidable (OfTypeIsDecidable {u = u} {U})
OfTypeIsDecidable {u = I U u v} {U′} = {!!}
OfTypeIsDecidable {u = Π u f} {U} = {!!}
OfTypeIsDecidable {u = 𝒰} {U} = inr lemma
  where lemma : ¬ (𝒰 ˸ U)
        lemma ()
OfTypeIsDecidable {u = incons} {U} = inr lemma
  where lemma : ¬ (incons ˸ U)
        lemma ()
