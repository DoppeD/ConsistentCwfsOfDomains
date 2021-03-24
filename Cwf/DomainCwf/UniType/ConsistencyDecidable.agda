{-# OPTIONS --safe --sized-types #-}

module Cwf.DomainCwf.UniType.ConsistencyDecidable where

open import Base.Core
open import Cwf.DomainCwf.UniType.Consistency
open import Cwf.DomainCwf.UniType.ConsistencyLemmata
open import Cwf.DomainCwf.UniType.Definition
open import Cwf.DomainCwf.UniType.FinFun

private
  conElems : ∀ {i} → FinFun {i} → Set
  conElems f = ∀ {u v} → (u , v) ∈ f → con u ⊠ con v

  conPairs : ∀ {i} → FinFun {i} → Set
  conPairs f = ∀ {u v u′ v′} → (u , v) ∈ f → (u′ , v′) ∈ f → con (u ⊔ u′) → con (v ⊔ v′)

conElemsSub : ∀ {i} → {f g : FinFun {i}} → f ⊆ g → conElems g → conElems f
conElemsSub f⊆g conElemsg uv∈f = conElemsg (f⊆g uv∈f)

conPairsDecidable : ∀ {i} → {f : FinFun {i}} → conElems f →
                    (∀ {u v u′ v′} → (u , v) ∈ f → (u′ , v′) ∈ f → Decidable (con (u ⊔ u′))) →
                    (∀ {u v u′ v′} → (u , v) ∈ f → (u′ , v′) ∈ f → Decidable (con (v ⊔ v′))) →
                    Decidable (conPairs f)
conPairsDecidable {f = ∅} _ _ _ = inl (λ uv∈∅ _ _ → xy∈∅-abs uv∈∅)
conPairsDecidable {f = (u , v) ∷ ∅} _ decidableFst decidableSnd
  with (decidableFst here here) | decidableSnd here here
... | inl conuu′ | inl convv′ = inl lemma
  where lemma : ∀ {u′ v′ u″ v″} → (u′ , v′) ∈ ((u , v) ∷ ∅) →
                (u″ , v″) ∈ ((u , v) ∷ ∅) → con (u′ ⊔ u″) → con (v′ ⊔ v″)
        lemma here here _ = convv′
... | inl conuu′ | inr ¬convv′ = inr lemma
  where lemma : ¬ (∀ {u′ v′ u″ v″} → (u′ , v′) ∈ ((u , v) ∷ ∅) →
                  (u″ , v″) ∈ ((u , v) ∷ ∅) → con (u′ ⊔ u″) → con (v′ ⊔ v″))
        lemma p = ¬convv′ (p here here conuu′)
... | inr ¬conuu′ | _ = inl lemma
  where lemma : (∀ {u′ v′ u″ v″} → (u′ , v′) ∈ ((u , v) ∷ ∅) →
                (u″ , v″) ∈ ((u , v) ∷ ∅) → con (u′ ⊔ u″) → con (v′ ⊔ v″))
        lemma here here conuu′ = ¬-elim (¬conuu′ conuu′)
conPairsDecidable {f = (u , v) ∷ ((u′ , v′) ∷ f′)} conElems decidableFst decidableSnd
  with (decidableFst here (there here)) | decidableSnd here (there here) |
       conPairsDecidable {f = (u , v) ∷ f′} (conElemsSub ⊆-lemma₆ conElems)
                         (λ uv∈ u′v′∈ → decidableFst (⊆-lemma₆ uv∈) (⊆-lemma₆ u′v′∈))
                         (λ uv∈uvf′ u′v′∈uvf′ → decidableSnd (⊆-lemma₆ uv∈uvf′) (⊆-lemma₆ u′v′∈uvf′)) |
       conPairsDecidable {f = (u′ , v′) ∷ f′} (conElemsSub ⊆-lemma₃ conElems)
                         (λ uv∈ u′v′∈ → decidableFst (⊆-lemma₃ uv∈) (⊆-lemma₃ u′v′∈))
                         (λ uv∈ u′v′∈ → decidableSnd (⊆-lemma₃ uv∈) (⊆-lemma₃ u′v′∈))
... | _ | _ | inl conuvf′ | inr ¬conu′v′f′ = inr lemma
  where lemma : ¬ (conPairs ((u , v) ∷ ((u′ , v′) ∷ f′)))
        lemma conPairs = ¬conu′v′f′ λ uv∈ u′v′∈ → conPairs (there uv∈) (there u′v′∈)
... | _ | _ | inr ¬conuvf′ | _ = inr lemma
  where lemma : ¬ (conPairs ((u , v) ∷ ((u′ , v′) ∷ f′)))
        lemma conPairs = ¬conuvf′ (λ uv∈ u′v′∈ → conPairs (⊆-lemma₆ uv∈) (⊆-lemma₆ u′v′∈))
... | inl conuu′ | inr ¬convv′ | inl _ | inl _ = inr lemma
  where lemma : ¬ (conPairs ((u , v) ∷ ((u′ , v′) ∷ f′)))
        lemma conPairs = ¬convv′ (conPairs here (there here) conuu′)
... | inr ¬conuu′ | _ | inl conuvf′ | inl conu′v′f′ = inl lemma
  where lemma : conPairs ((u , v) ∷ ((u′ , v′) ∷ f′))
        lemma here here conuu′ = conLemma₃ {u = v} (⊠-snd (conElems here))
        lemma here (there here) conuu′ = ¬-elim (¬conuu′ conuu′)
        lemma here (there (there u′v′∈)) conuu′ = conuvf′ here (there (u′v′∈)) conuu′
        lemma (there here) here conuu′ = ¬-elim (¬conuu′ (conSym {u = u′} conuu′))
        lemma (there (there uv∈)) here conuu′ = conSym {u = v} (conuvf′ here (there uv∈) (conSym {v = u} conuu′))
        lemma (there here) (there here) conuu′ = conLemma₃ {u = v′} (⊠-snd (conElems (there here)))
        lemma (there here) (there (there u′v′∈)) conuu′ = conu′v′f′ here (there u′v′∈) conuu′
        lemma (there (there uv∈)) (there here) conuu′ = conSym {u = v′} (conu′v′f′ here (there uv∈) (conSym {v = u′} conuu′))
        lemma (there (there uv∈)) (there (there u′v′∈)) conuu′ = conu′v′f′ (there uv∈) (there u′v′∈) conuu′
... | inl conuu′ | inl convv′ | inl conuvf′ | inl conu′v′f′ = inl lemma
  where lemma : conPairs ((u , v) ∷ ((u′ , v′) ∷ f′))
        lemma here here conuu′ = conLemma₃ {u = v} (⊠-snd (conElems here))
        lemma here (there here) conuu′ = convv′
        lemma here (there (there u′v′∈)) conuu′ = conuvf′ here (there (u′v′∈)) conuu′
        lemma (there here) here conuu′ = conSym {u = v} convv′
        lemma (there (there uv∈)) here conuu′ = conSym {u = v} (conuvf′ here (there uv∈) (conSym {v = u} conuu′))
        lemma (there here) (there here) conuu′ = conLemma₃ {u = v′} (⊠-snd (conElems (there here)))
        lemma (there here) (there (there u′v′∈)) conuu′ = conu′v′f′ here (there u′v′∈) conuu′
        lemma (there (there uv∈)) (there here) conuu′ = conSym {u = v′} (conu′v′f′ here (there uv∈) (conSym {v = u′} conuu′))
        lemma (there (there uv∈)) (there (there u′v′∈)) conuu′ = conu′v′f′ (there uv∈) (there u′v′∈) conuu′

consistencyDecidable : ∀ {i} → {u : Nbh {i}} → Decidable (con u)
conElemsDecidable : ∀ {i} → {f : FinFun {i}} → Decidable (conElems f)

consistencyDecidable {u = ⊥} = inl *
consistencyDecidable {u = 0ᵤ} = inl *
consistencyDecidable {u = s u} = consistencyDecidable {u = u}
consistencyDecidable {u = ℕ} = inl *
consistencyDecidable {u = F f} with (conElemsDecidable {f = f})
consistencyDecidable {u = F f} | inl conElems
  with conPairsDecidable {f = f} conElems
       (\{u} {v} {u′} _ _ → consistencyDecidable {u = u ⊔ u′})
       (\{_} {v} {_} {v′} _ _ → consistencyDecidable {u = v ⊔ v′})
consistencyDecidable {u = F f} | inl conElems | inl conPairs = inl (conPairs , conElems)
consistencyDecidable {u = F f} | inl conElems | inr ¬conPairs = inr lemma
  where lemma : ¬ (con (F f))
        lemma (conPairs , _) = ¬conPairs conPairs
consistencyDecidable {u = F f} | inr ¬conElems = inr lemma
  where lemma : ¬ (con (F f))
        lemma (_ , conElems) = ¬conElems conElems
consistencyDecidable {u = refl u} = consistencyDecidable {u = u}
consistencyDecidable {u = I U u v}
  with (consistencyDecidable {u = U}) | consistencyDecidable {u = u} | consistencyDecidable {u = v}
... | inl conU | inl conu | inl conv = inl (conU , (conu , conv))
... | inl conU | inl conu | inr ¬conv = inr (λ conUuv → ¬conv (⊠-snd (⊠-snd conUuv)))
... | inl conU | inr ¬conu | _ = inr (λ conUuv → ¬conu (⊠-fst (⊠-snd conUuv)))
... | inr ¬conU | _ | _ = inr (λ conUuv → ¬conU (⊠-fst conUuv))
consistencyDecidable {u = Π U f}
  with (consistencyDecidable {u = U}) | conElemsDecidable {f = f}
consistencyDecidable {u = Π U f} | inl conU | inl conElems
  with conPairsDecidable {f = f} conElems
       (\{u} {v} {u′} _ _ → consistencyDecidable {u = u ⊔ u′})
       (\{_} {v} {_} {v′} _ _ → consistencyDecidable {u = v ⊔ v′})
consistencyDecidable {u = Π U f} | inl conU | inl conElems | inl conPairs
  = inl (conU , (conPairs , conElems))
consistencyDecidable {u = Π U f} | inl conU | inl conElems | inr ¬conPairs = inr lemma
  where lemma : ¬ (con (Π U f))
        lemma (_ , (conPairs , _)) = ¬conPairs conPairs
consistencyDecidable {u = Π U f} | inl conU | inr ¬conElems = inr lemma
  where lemma : ¬ (con (Π U f))
        lemma (_ , (_ , conElems)) = ¬conElems conElems
consistencyDecidable {u = Π U f} | inr ¬conU | _ = inr lemma
  where lemma : ¬ (con (Π U f))
        lemma (conU , _) = ¬conU conU
consistencyDecidable {u = 𝒰} = inl *
consistencyDecidable {u = incons} = inr (λ x → x)

conElemsDecidable {f = ∅} = inl xy∈∅-abs
conElemsDecidable {f = (u , v) ∷ f′}
  with (consistencyDecidable {u = u}) | consistencyDecidable {u = v} | conElemsDecidable {f = f′}
... | inl conu | inl conv | inl conf′ = inl lemma
  where lemma : ∀ {u′ v′} → (u′ , v′) ∈ ((u , v) ∷ f′) →  con u′ ⊠ con v′
        lemma here = conu , conv
        lemma (there u′v′∈f′) = conf′ u′v′∈f′
... | inl conu | inl conv | inr ¬conf′ = inr (λ p → ¬conf′ (λ u′v′∈f′ → p (there u′v′∈f′)))
... | inl conu | inr ¬conv | _ = inr (λ p → ¬conv (⊠-snd (p here)))
... | inr ¬conu | _ | _ = inr (λ p → ¬conu (⊠-fst (p here)))
