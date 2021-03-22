module Cwf.DomainCwf.UniType.TypingAlgorithm where

open import Base.Core
open import Cwf.DomainCwf.UniType.Consistency
open import Cwf.DomainCwf.UniType.ConsistencyLemmata
open import Cwf.DomainCwf.UniType.FinFun
open import Cwf.DomainCwf.UniType.Definition
open import Cwf.DomainCwf.UniType.Relation

open import Agda.Builtin.Sigma
open import Agda.Builtin.Size

record apSet {i : Size} (f : FinFun {i}) (u : Nbh {i}) : Set where
  field
    ⊑proof : ⊑-proof f u ⊥
    isLargest : {⊑proof′ : ⊑-proof f u ⊥} → pre (⊑-proof.sub ⊑proof′) ⊑ pre (⊑-proof.sub ⊑proof)

data _Type : ∀ {i} → Nbh {i} → Set
data _˸_ : ∀ {i} → Nbh {i} → Nbh {i} → Set

data _Type where
  isType-I : ∀ {i} → {U u u′ : Nbh {i}} → U Type → u ˸ U → u′ ˸ U → (I U u u′) Type
  isType-ℕ : ∀ {i} → ℕ {i} Type
  isType-𝒰 : ∀ {i} → 𝒰 {i} Type
  isType-Π : ∀ {i} → {U : Nbh {i}} → {f : FinFun {i}} → U Type →
             (∀ {u V} → (u , V) ∈ f → (u ˸ U) ⊠ (V Type)) →
             (Π U f) Type

data _˸_ where
  ⊥:U : ∀ {i} → {U : Nbh {i}} → U Type → ⊥ ˸ U
  0:ℕ : 0ᵤ ˸ ℕ
  s:N : ∀ {u} → u ˸ ℕ → s u ˸ ℕ
  F:Π : ∀ {U g f} →
        (∀ {u v} → (u , v) ∈ f → u ˸ U) →
        (∀ {u v} → (u , v) ∈ f → (apset : apSet g u) → v ˸ post (⊑-proof.sub (apSet.⊑proof apset))) →
        (F f) ˸ (Π U g)
  refl:I : ∀ {U u} → U Type → u ˸ U → refl u ˸ I U u u
  Π:𝒰 : ∀ {U f} → U ˸ 𝒰 →
        (∀ {u V} → (u , V) ∈ f → (u ˸ U) ∧ (V ˸ 𝒰)) →
        (Π U f) ˸ 𝒰
  ℕ:𝒰 : ℕ ˸ 𝒰

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
OfTypeIsDecidable {u = 0ᵤ} {U} = {!!}
OfTypeIsDecidable {u = s u} {U} = {!!}
OfTypeIsDecidable {u = ℕ} {U} = {!!}
OfTypeIsDecidable {u = F f} {U} = {!!}
OfTypeIsDecidable {u = refl u} {U} = {!!}
OfTypeIsDecidable {u = I U u v} {U′} = {!!}
OfTypeIsDecidable {u = Π u f} {U} = {!!}
OfTypeIsDecidable {u = 𝒰} {U} = inr lemma
  where lemma : ¬ (𝒰 ˸ U)
        lemma ()
OfTypeIsDecidable {u = incons} {U} = inr lemma
  where lemma : ¬ (incons ˸ U)
        lemma ()
