module Cwf.DomainCwf.UniType.Decidable.ConsistencyDecidable where

open import Base.Core
open import Base.FinFun
open import Cwf.DomainCwf.UniType.Consistency
open import Cwf.DomainCwf.UniType.ConsistencyLemmata
open import Cwf.DomainCwf.UniType.Definition

private
  conElems : FinFun Nbh Nbh → Set
  conElems f = ∀ {u v} → (u , v) ∈ f → con u ⊠ con v

  conPairs : FinFun Nbh Nbh → Set
  conPairs f = ∀ {u v u′ v′} → (u , v) ∈ f → (u′ , v′) ∈ f → con (u ⊔ u′) → con (v ⊔ v′)

conElemsSub : ∀ {f g} → f ⊆ g → conElems g → conElems f
conElemsSub f⊆g conElemsg uv∈f = conElemsg (f⊆g uv∈f)

conPairsDecidable : ∀ {f} → conElems f →
                    (∀ {u v u′ v′} → (u , v) ∈ f → (u′ , v′) ∈ f → Decidable (con (u ⊔ u′))) →
                    (∀ {u v u′ v′} → (u , v) ∈ f → (u′ , v′) ∈ f → Decidable (con (v ⊔ v′))) →
                    Decidable (conPairs f)
conPairsDecidable {∅} _ _ _ = inl (λ uv∈∅ _ _ → xy∈∅-abs uv∈∅)
conPairsDecidable {(u , v) ∷ ∅} _ decidableFst decidableSnd
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
conPairsDecidable {(u , v) ∷ ((u′ , v′) ∷ f′)} conElems decidableFst decidableSnd
  with (decidableFst here (there here)) | decidableSnd here (there here) |
       conPairsDecidable {(u , v) ∷ f′} (conElemsSub ⊆-lemma₆ conElems)
                         (λ uv∈ u′v′∈ → decidableFst (⊆-lemma₆ uv∈) (⊆-lemma₆ u′v′∈))
                         (λ uv∈uvf′ u′v′∈uvf′ → decidableSnd (⊆-lemma₆ uv∈uvf′) (⊆-lemma₆ u′v′∈uvf′)) |
       conPairsDecidable {(u′ , v′) ∷ f′} (conElemsSub ⊆-lemma₃ conElems)
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
        lemma here here conuu′ = conLemma₃ {v} (⊠-snd (conElems here))
        lemma here (there here) conuu′ = ¬-elim (¬conuu′ conuu′)
        lemma here (there (there u′v′∈)) conuu′ = conuvf′ here (there (u′v′∈)) conuu′
        lemma (there here) here conuu′ = ¬-elim (¬conuu′ (conSym {u′} conuu′))
        lemma (there (there uv∈)) here conuu′ = conSym {v} (conuvf′ here (there uv∈) (conSym {v = u} conuu′))
        lemma (there here) (there here) conuu′ = conLemma₃ {v′} (⊠-snd (conElems (there here)))
        lemma (there here) (there (there u′v′∈)) conuu′ = conu′v′f′ here (there u′v′∈) conuu′
        lemma (there (there uv∈)) (there here) conuu′ = conSym {v′} (conu′v′f′ here (there uv∈) (conSym {v = u′} conuu′))
        lemma (there (there uv∈)) (there (there u′v′∈)) conuu′ = conu′v′f′ (there uv∈) (there u′v′∈) conuu′
... | inl conuu′ | inl convv′ | inl conuvf′ | inl conu′v′f′ = inl lemma
  where lemma : conPairs ((u , v) ∷ ((u′ , v′) ∷ f′))
        lemma here here conuu′ = conLemma₃ {v} (⊠-snd (conElems here))
        lemma here (there here) conuu′ = convv′
        lemma here (there (there u′v′∈)) conuu′ = conuvf′ here (there (u′v′∈)) conuu′
        lemma (there here) here conuu′ = conSym {v} convv′
        lemma (there (there uv∈)) here conuu′ = conSym {v} (conuvf′ here (there uv∈) (conSym {v = u} conuu′))
        lemma (there here) (there here) conuu′ = conLemma₃ {v′} (⊠-snd (conElems (there here)))
        lemma (there here) (there (there u′v′∈)) conuu′ = conu′v′f′ here (there u′v′∈) conuu′
        lemma (there (there uv∈)) (there here) conuu′ = conSym {v′} (conu′v′f′ here (there uv∈) (conSym {v = u′} conuu′))
        lemma (there (there uv∈)) (there (there u′v′∈)) conuu′ = conu′v′f′ (there uv∈) (there u′v′∈) conuu′

consistencyDecidable : ∀ {u} → Decidable (con u)
conElemsDecidable : ∀ {f} → Decidable (conElems f)

consistencyDecidable {⊥} = inl *
consistencyDecidable {0ᵤ} = inl *
consistencyDecidable {s u} = consistencyDecidable {u}
consistencyDecidable {ℕ} = inl *
consistencyDecidable {F f} with (conElemsDecidable {f = f})
consistencyDecidable {F f} | inl conElems
  with conPairsDecidable {f = f} conElems
       (\{u} {v} {u′} _ _ → consistencyDecidable {u ⊔ u′})
       (\{_} {v} {_} {v′} _ _ → consistencyDecidable {v ⊔ v′})
consistencyDecidable {F f} | inl conElems | inl conPairs = inl (conPairs , conElems)
consistencyDecidable {F f} | inl conElems | inr ¬conPairs = inr lemma
  where lemma : ¬ (con (F f))
        lemma (conPairs , _) = ¬conPairs conPairs
consistencyDecidable {F f} | inr ¬conElems = inr lemma
  where lemma : ¬ (con (F f))
        lemma (_ , conElems) = ¬conElems conElems
consistencyDecidable {refl u} = consistencyDecidable {u}
consistencyDecidable {I U u v}
  with (consistencyDecidable {U}) | consistencyDecidable {u} | consistencyDecidable {v}
... | inl conU | inl conu | inl conv = inl (conU , (conu , conv))
... | inl conU | inl conu | inr ¬conv = inr (λ conUuv → ¬conv (⊠-snd (⊠-snd conUuv)))
... | inl conU | inr ¬conu | _ = inr (λ conUuv → ¬conu (⊠-fst (⊠-snd conUuv)))
... | inr ¬conU | _ | _ = inr (λ conUuv → ¬conU (⊠-fst conUuv))
consistencyDecidable {Π U f}
  with (consistencyDecidable {U}) | conElemsDecidable {f = f}
consistencyDecidable {Π U f} | inl conU | inl conElems
  with conPairsDecidable {f = f} conElems
       (\{u} {v} {u′} _ _ → consistencyDecidable {u ⊔ u′})
       (\{_} {v} {_} {v′} _ _ → consistencyDecidable {v ⊔ v′})
consistencyDecidable {Π U f} | inl conU | inl conElems | inl conPairs
  = inl (conU , (conPairs , conElems))
consistencyDecidable {Π U f} | inl conU | inl conElems | inr ¬conPairs = inr lemma
  where lemma : ¬ (con (Π U f))
        lemma (_ , (conPairs , _)) = ¬conPairs conPairs
consistencyDecidable {Π U f} | inl conU | inr ¬conElems = inr lemma
  where lemma : ¬ (con (Π U f))
        lemma (_ , (_ , conElems)) = ¬conElems conElems
consistencyDecidable {Π U f} | inr ¬conU | _ = inr lemma
  where lemma : ¬ (con (Π U f))
        lemma (conU , _) = ¬conU conU
consistencyDecidable {𝒰} = inl *
consistencyDecidable {incons} = inr (λ x → x)

conElemsDecidable {f = ∅} = inl xy∈∅-abs
conElemsDecidable {f = (u , v) ∷ f′}
  with (consistencyDecidable {u}) | consistencyDecidable {v} | conElemsDecidable {f = f′}
... | inl conu | inl conv | inl conf′ = inl lemma
  where lemma : ∀ {u′ v′} → (u′ , v′) ∈ ((u , v) ∷ f′) →  con u′ ⊠ con v′
        lemma here = conu , conv
        lemma (there u′v′∈f′) = conf′ u′v′∈f′
... | inl conu | inl conv | inr ¬conf′ = inr (λ p → ¬conf′ (λ u′v′∈f′ → p (there u′v′∈f′)))
... | inl conu | inr ¬conv | _ = inr (λ p → ¬conv (⊠-snd (p here)))
... | inr ¬conu | _ | _ = inr (λ p → ¬conu (⊠-fst (p here)))
