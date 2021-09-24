{-# OPTIONS --safe #-}

module Cwf.DomainCwf.UniType.Decidable.EqualityDecidable where

open import Base.Core
open import Base.FinFun
open import Cwf.DomainCwf.UniType.Definition

open import Agda.Builtin.Equality

¬eqSym : {u v : Nbh} → ¬ (u ≡ v) → ¬ (v ≡ u)
¬eqSym ¬u≡v refl = ¬u≡v refl

¬⊥≡0 : ¬ (⊥ ≡ 0ᵤ)
¬⊥≡0 ()

¬⊥≡s : ∀ {v} → ¬ (⊥ ≡ s v)
¬⊥≡s ()

¬⊥≡ℕ : ¬ (⊥ ≡ ℕ)
¬⊥≡ℕ ()

¬⊥≡F : ∀ {f} → ¬ (⊥ ≡ F f)
¬⊥≡F ()

¬⊥≡refl : ∀ {v} → ¬ (⊥ ≡ refl v)
¬⊥≡refl ()

¬⊥≡I : ∀ {U u v} → ¬ (⊥ ≡ I U u v)
¬⊥≡I ()

¬⊥≡Π : ∀ {U f} → ¬ (⊥ ≡ Π U f)
¬⊥≡Π ()

¬⊥≡𝒰 : ¬ (⊥ ≡ 𝒰)
¬⊥≡𝒰 ()

¬⊥≡incons : ¬ (⊥ ≡ incons)
¬⊥≡incons ()

¬0≡s : ∀ {v} → ¬ (0ᵤ ≡ s v)
¬0≡s ()

¬0≡ℕ : ¬ (0ᵤ ≡ ℕ)
¬0≡ℕ ()

¬0≡F : ∀ {f} → ¬ (0ᵤ ≡ F f)
¬0≡F ()

¬0≡refl : ∀ {v} → ¬ (0ᵤ ≡ refl v)
¬0≡refl ()

¬0≡I : ∀ {U u v} → ¬ (0ᵤ ≡ I U u v)
¬0≡I ()

¬0≡Π : ∀ {U f} → ¬ (0ᵤ ≡ Π U f)
¬0≡Π ()

¬0≡𝒰 : ¬ (0ᵤ ≡ 𝒰)
¬0≡𝒰 ()

¬0≡incons : ¬ (0ᵤ ≡ incons)
¬0≡incons ()

¬ℕ≡F : ∀ {f} → ¬ (ℕ ≡ F f)
¬ℕ≡F ()

¬ℕ≡refl : ∀ {v} → ¬ (ℕ ≡ refl v)
¬ℕ≡refl ()

¬ℕ≡I : ∀ {U u v} → ¬ (ℕ ≡ I U u v)
¬ℕ≡I ()

¬ℕ≡Π : ∀ {U f} → ¬ (ℕ ≡ Π U f)
¬ℕ≡Π ()

¬ℕ≡𝒰 : ¬ (ℕ ≡ 𝒰)
¬ℕ≡𝒰 ()

¬ℕ≡incons : ¬ (ℕ ≡ incons)
¬ℕ≡incons ()

¬s≡ℕ : ∀ {u} → ¬ (s u ≡ ℕ)
¬s≡ℕ ()

¬s≡F : ∀ {u f} → ¬ (s u ≡ F f)
¬s≡F ()

¬s≡refl : ∀ {u v} → ¬ (s u ≡ refl v)
¬s≡refl ()

¬s≡I : ∀ {u U v v′} → ¬ (s u ≡ I U v v′)
¬s≡I ()

¬s≡Π : ∀ {u U f} → ¬ (s u ≡ Π U f)
¬s≡Π ()

¬s≡𝒰 : ∀ {u} → ¬ (s u ≡ 𝒰)
¬s≡𝒰 ()

¬s≡incons : ∀ {u} → ¬ (s u ≡ incons)
¬s≡incons ()

¬F≡refl : ∀ {f v} → ¬ (F f ≡ refl v)
¬F≡refl ()

¬F≡I : ∀ {f U u v} → ¬ (F f ≡ I U u v)
¬F≡I ()

¬F≡Π : ∀ {f U g} → ¬ (F f ≡ Π U g)
¬F≡Π ()

¬F≡𝒰 : ∀ {f} → ¬ (F f ≡ 𝒰)
¬F≡𝒰 ()

¬F≡incons : ∀ {f} → ¬ (F f ≡ incons)
¬F≡incons ()

¬refl≡I : ∀ {u U v v′} → ¬ (refl u ≡ I U v v′)
¬refl≡I ()

¬refl≡Π : ∀ {u U f} → ¬ (refl u ≡ Π U f)
¬refl≡Π ()

¬refl≡𝒰 : ∀ {u} → ¬ (refl u ≡ 𝒰)
¬refl≡𝒰 ()

¬refl≡incons : ∀ {u} → ¬ (refl u ≡ incons)
¬refl≡incons ()

¬I≡Π : ∀ {U u v V f} → ¬ (I U u v ≡ Π V f)
¬I≡Π ()

¬I≡𝒰 : ∀ {U u v} → ¬ (I U u v ≡ 𝒰)
¬I≡𝒰 ()

¬I≡incons : ∀ {U u v} → ¬ (I U u v ≡ incons)
¬I≡incons ()

¬Π≡𝒰 : ∀ {U f} → ¬ (Π U f ≡ 𝒰)
¬Π≡𝒰 ()

¬Π≡incons : ∀ {U f} → ¬ (Π U f ≡ incons)
¬Π≡incons ()

¬𝒰≡incons : ¬ (𝒰 ≡ incons)
¬𝒰≡incons ()

⊥equalityDecidable : ∀ {v} → Decidable (⊥ ≡ v)
⊥equalityDecidable {⊥} = inl refl
⊥equalityDecidable {0ᵤ} = inr ¬⊥≡0
⊥equalityDecidable {s _} = inr ¬⊥≡s
⊥equalityDecidable {ℕ} = inr ¬⊥≡ℕ
⊥equalityDecidable {F _} = inr ¬⊥≡F
⊥equalityDecidable {refl _} = inr ¬⊥≡refl
⊥equalityDecidable {I _ _ _} = inr ¬⊥≡I
⊥equalityDecidable {Π _ _} = inr ¬⊥≡Π
⊥equalityDecidable {𝒰} = inr ¬⊥≡𝒰
⊥equalityDecidable {incons} = inr ¬⊥≡incons

0equalityDecidable : ∀ {v} → Decidable (0ᵤ ≡ v)
0equalityDecidable {⊥} = inr (¬eqSym ¬⊥≡0)
0equalityDecidable {0ᵤ} = inl refl
0equalityDecidable {s _} = inr ¬0≡s
0equalityDecidable {ℕ} = inr ¬0≡ℕ
0equalityDecidable {F _} = inr ¬0≡F
0equalityDecidable {refl _} = inr ¬0≡refl
0equalityDecidable {I _ _ _} = inr ¬0≡I
0equalityDecidable {Π _ _} = inr ¬0≡Π
0equalityDecidable {𝒰} = inr ¬0≡𝒰
0equalityDecidable {incons} = inr ¬0≡incons

ℕequalityDecidable : ∀ {v} → Decidable (ℕ ≡ v)
ℕequalityDecidable {⊥} = inr (¬eqSym ¬⊥≡ℕ)
ℕequalityDecidable {0ᵤ} = inr (¬eqSym ¬0≡ℕ)
ℕequalityDecidable {s _} = inr (¬eqSym ¬s≡ℕ)
ℕequalityDecidable {ℕ} = inl refl
ℕequalityDecidable {F _} = inr ¬ℕ≡F
ℕequalityDecidable {refl _} = inr ¬ℕ≡refl
ℕequalityDecidable {I _ _ _} = inr ¬ℕ≡I
ℕequalityDecidable {Π _ _} = inr ¬ℕ≡Π
ℕequalityDecidable {𝒰} = inr ¬ℕ≡𝒰
ℕequalityDecidable {incons} = inr ¬ℕ≡incons

𝒰equalityDecidable : ∀ {v} → Decidable (𝒰 ≡ v)
𝒰equalityDecidable {⊥} = inr (¬eqSym ¬⊥≡𝒰)
𝒰equalityDecidable {0ᵤ} = inr (¬eqSym ¬0≡𝒰)
𝒰equalityDecidable {s _} = inr (¬eqSym ¬s≡𝒰)
𝒰equalityDecidable {ℕ} = inr (¬eqSym ¬ℕ≡𝒰)
𝒰equalityDecidable {F _} = inr (¬eqSym ¬F≡𝒰)
𝒰equalityDecidable {refl _} = inr (¬eqSym ¬refl≡𝒰)
𝒰equalityDecidable {I _ _ _} = inr (¬eqSym ¬I≡𝒰)
𝒰equalityDecidable {Π _ _} = inr (¬eqSym ¬Π≡𝒰)
𝒰equalityDecidable {𝒰} = inl refl
𝒰equalityDecidable {incons} = inr ¬𝒰≡incons

inconsEqualityDecidable : ∀ {v} → Decidable (incons ≡ v)
inconsEqualityDecidable {⊥} = inr (¬eqSym ¬⊥≡incons)
inconsEqualityDecidable {0ᵤ} = inr (¬eqSym ¬0≡incons)
inconsEqualityDecidable {s _} = inr (¬eqSym ¬s≡incons)
inconsEqualityDecidable {ℕ} = inr (¬eqSym ¬ℕ≡incons)
inconsEqualityDecidable {F _} = inr (¬eqSym ¬F≡incons)
inconsEqualityDecidable {refl _} = inr (¬eqSym ¬refl≡incons)
inconsEqualityDecidable {I _ _ _} = inr (¬eqSym ¬I≡incons)
inconsEqualityDecidable {Π _ _} = inr (¬eqSym ¬Π≡incons)
inconsEqualityDecidable {𝒰} = inr (¬eqSym ¬𝒰≡incons)
inconsEqualityDecidable {incons} = inl refl

equalityDecidable : {u v : Nbh} → Decidable (u ≡ v)
equalityDecidableFinFun : {f g : FinFun Nbh Nbh} → Decidable (f ≡ g)

equalityDecidable {⊥} = ⊥equalityDecidable
equalityDecidable {0ᵤ} = 0equalityDecidable
equalityDecidable {s _} {v = ⊥} = inr (¬eqSym ¬⊥≡s)
equalityDecidable {s _} {v = 0ᵤ} = inr (¬eqSym ¬0≡s)
equalityDecidable {s u} {v = s v} with (equalityDecidable {u} {v})
... | inl refl = inl refl
... | inr ¬u≡v = inr lemma
  where lemma : ¬ (s u ≡ s v)
        lemma refl = ¬u≡v refl
equalityDecidable {s _} {v = ℕ} = inr ¬s≡ℕ
equalityDecidable {s _} {v = F _} = inr ¬s≡F
equalityDecidable {s _} {v = refl _} = inr ¬s≡refl
equalityDecidable {s _} {v = I _ _ _} = inr ¬s≡I
equalityDecidable {s _} {v = Π _ _} = inr ¬s≡Π
equalityDecidable {s _} {v = 𝒰} = inr ¬s≡𝒰
equalityDecidable {s _} {v = incons} = inr ¬s≡incons
equalityDecidable {ℕ} = ℕequalityDecidable
equalityDecidable {F _} {⊥} = inr (¬eqSym ¬⊥≡F)
equalityDecidable {F _} {0ᵤ} = inr (¬eqSym ¬0≡F)
equalityDecidable {F _} {s _} = inr (¬eqSym ¬s≡F)
equalityDecidable {F _} {ℕ} = inr (¬eqSym ¬ℕ≡F)
equalityDecidable {F f} {F g} with (equalityDecidableFinFun {f = f} {g})
... | inl refl = inl refl
... | inr ¬f≡g = inr lemma
  where lemma : ¬ (F f ≡ F g)
        lemma refl = ¬f≡g refl
equalityDecidable {F _} {refl _} = inr ¬F≡refl
equalityDecidable {F _} {I _ _ _} = inr ¬F≡I
equalityDecidable {F _} {Π _ _} = inr ¬F≡Π
equalityDecidable {F _} {𝒰} = inr ¬F≡𝒰
equalityDecidable {F _} {incons} = inr ¬F≡incons
equalityDecidable {refl _} {⊥} = inr (¬eqSym ¬⊥≡refl)
equalityDecidable {refl _} {0ᵤ} = inr (¬eqSym ¬0≡refl)
equalityDecidable {refl _} {s _} = inr (¬eqSym ¬s≡refl)
equalityDecidable {refl _} {ℕ} = inr (¬eqSym ¬ℕ≡refl)
equalityDecidable {refl _} {F _} = inr (¬eqSym ¬F≡refl)
equalityDecidable {refl u} {refl v} with (equalityDecidable {u} {v})
... | inl refl = inl refl
... | inr ¬u≡v = inr lemma
  where lemma : ¬ (refl u ≡ refl v)
        lemma refl = ¬u≡v refl
equalityDecidable {refl _} {I _ _ _} = inr ¬refl≡I
equalityDecidable {refl _} {Π _ _} = inr ¬refl≡Π
equalityDecidable {refl _} {𝒰} = inr ¬refl≡𝒰
equalityDecidable {refl _} {incons} = inr ¬refl≡incons
equalityDecidable {I _ _ _} {⊥} = inr (¬eqSym ¬⊥≡I)
equalityDecidable {I _ _ _} {0ᵤ} = inr (¬eqSym ¬0≡I)
equalityDecidable {I _ _ _} {s _} = inr (¬eqSym ¬s≡I)
equalityDecidable {I _ _ _} {ℕ} = inr (¬eqSym ¬ℕ≡I)
equalityDecidable {I _ _ _} {F _} = inr (¬eqSym ¬F≡I)
equalityDecidable {I _ _ _} {refl _} = inr (¬eqSym ¬refl≡I)
equalityDecidable {I U u v} {I U′ u′ v′ }
  with (equalityDecidable {U} {U′}) | equalityDecidable {u} {u′} | equalityDecidable {v} {v′}
... | inl refl | inl refl | inl refl = inl refl
... | inl refl | inl refl | inr ¬v≡v′ = inr lemma
  where lemma : ¬ (I U u v ≡ I U′ u′ v′)
        lemma refl = ¬v≡v′ refl
... | inl refl | inr ¬u≡u′ | _ = inr lemma
  where lemma : ¬ (I U u v ≡ I U′ u′ v′)
        lemma refl = ¬u≡u′ refl
... | inr ¬U≡U′ | _ | _ = inr lemma
  where lemma : ¬ (I U u v ≡ I U′ u′ v′)
        lemma refl = ¬U≡U′ refl
equalityDecidable {I _ _ _} {Π _ _} = inr ¬I≡Π
equalityDecidable {I _ _ _} {𝒰} = inr ¬I≡𝒰
equalityDecidable {I _ _ _} {incons} = inr ¬I≡incons
equalityDecidable {Π _ _} {⊥} = inr (¬eqSym ¬⊥≡Π)
equalityDecidable {Π _ _} {0ᵤ} = inr (¬eqSym ¬0≡Π)
equalityDecidable {Π _ _} {s _} = inr (¬eqSym ¬s≡Π)
equalityDecidable {Π _ _} {ℕ} = inr (¬eqSym ¬ℕ≡Π)
equalityDecidable {Π _ _} {F _} = inr (¬eqSym ¬F≡Π)
equalityDecidable {Π _ _} {refl _} = inr (¬eqSym ¬refl≡Π)
equalityDecidable {Π _ _} {I _ _ _} = inr (¬eqSym ¬I≡Π)
equalityDecidable {Π U f} {Π V g}
  with (equalityDecidable {U} {V}) | equalityDecidableFinFun {f = f} {g}
... | inl refl | inl refl = inl refl
... | inl refl | inr ¬g≡g = inr lemma
  where lemma : ¬ (Π U f ≡ Π V g)
        lemma refl = ¬g≡g refl
... | inr ¬f≡f | _ = inr lemma
  where lemma : ¬ (Π U f ≡ Π V g)
        lemma refl = ¬f≡f refl
equalityDecidable {Π _ _} {𝒰} = inr ¬Π≡𝒰
equalityDecidable {Π _ _} {incons} = inr ¬Π≡incons
equalityDecidable {𝒰} {v} = 𝒰equalityDecidable
equalityDecidable {incons} {v} = inconsEqualityDecidable

equalityDecidableFinFun {∅} {∅} = inl refl
equalityDecidableFinFun {∅} {(u′ , v′) ∷ g′} = inr lemma
  where lemma : ¬ (∅ ≡ (u′ , v′) ∷ g′)
        lemma ()
equalityDecidableFinFun {(u , v) ∷ f′} {∅} = inr lemma
  where lemma : ¬ ((u , v) ∷ f′ ≡ ∅)
        lemma ()
equalityDecidableFinFun {(u , v) ∷ f′} {(u′ , v′) ∷ g′}
  with (equalityDecidable {u} {u′}) | equalityDecidable {v} {v′} | equalityDecidableFinFun {f′} {g′}
... | inl refl | inl refl | inl refl = inl refl
... | inl refl | inl refl | inr ¬f′≡g′ = inr lemma
  where lemma : ¬ (((u , v) ∷ f′) ≡ ((u′ , v′) ∷ g′))
        lemma refl = ¬f′≡g′ refl
... | inl refl | inr ¬v≡v′ | _ = inr lemma
  where lemma : ¬ (((u , v) ∷ f′) ≡ ((u′ , v′) ∷ g′))
        lemma refl = ¬v≡v′ refl
... | inr ¬u≡u′ | _ | _ = inr lemma
  where lemma : ¬ (((u , v) ∷ f′) ≡ ((u′ , v′) ∷ g′))
        lemma refl = ¬u≡u′ refl
