{-# OPTIONS --safe --sized-types #-}

module Cwf.DomainCwf.UniType.DecidableEquality where

open import Base.Core
open import Cwf.DomainCwf.UniType.Definition

open import Agda.Builtin.Equality
open import Agda.Builtin.Size

¬eqSym : ∀ {i} → {u v : Nbh {i}} → ¬ (u ≡ v) → ¬ (v ≡ u)
¬eqSym ¬u≡v refl = ¬u≡v refl

¬⊥≡0 : ∀ {i} → ¬ (⊥ {i} ≡ 0ᵤ)
¬⊥≡0 ()

¬⊥≡s : ∀ {i} → {v : Nbh {i}} → ¬ (⊥ {i} ≡ s v)
¬⊥≡s ()

¬⊥≡ℕ : ∀ {i} → ¬ (⊥ {i} ≡ ℕ)
¬⊥≡ℕ ()

¬⊥≡F : ∀ {i} → {f : FinFun {i}} → ¬ (⊥ {↑ i} ≡ F f)
¬⊥≡F ()

¬⊥≡refl : ∀ {i} → {v : Nbh {i}} → ¬ (⊥ {i} ≡ refl v)
¬⊥≡refl ()

¬⊥≡I : ∀ {i} → {U u v : Nbh {i}} → ¬ (⊥ {i} ≡ I U u v)
¬⊥≡I ()

¬⊥≡Π : ∀ {i} → {U : Nbh {i}} → {f : FinFun {i}} → ¬ (⊥ {↑ i} ≡ Π U f)
¬⊥≡Π ()

¬⊥≡𝒰 : ∀ {i} → ¬ (⊥ {i} ≡ 𝒰)
¬⊥≡𝒰 ()

¬⊥≡incons : ∀ {i} → ¬ (⊥ {i} ≡ incons)
¬⊥≡incons ()

¬0≡s : ∀ {i} → {v : Nbh {i}} → ¬ (0ᵤ {i} ≡ s v)
¬0≡s ()

¬0≡ℕ : ∀ {i} → ¬ (0ᵤ {i} ≡ ℕ)
¬0≡ℕ ()

¬0≡F : ∀ {i} → {f : FinFun {i}} → ¬ (0ᵤ {↑ i} ≡ F f)
¬0≡F ()

¬0≡refl : ∀ {i} → {v : Nbh {i}} → ¬ (0ᵤ {i} ≡ refl v)
¬0≡refl ()

¬0≡I : ∀ {i} → {U u v : Nbh {i}} → ¬ (0ᵤ {i} ≡ I U u v)
¬0≡I ()

¬0≡Π : ∀ {i} → {U : Nbh {i}} → {f : FinFun {i}} → ¬ (0ᵤ {↑ i} ≡ Π U f)
¬0≡Π ()

¬0≡𝒰 : ∀ {i} → ¬ (0ᵤ {i} ≡ 𝒰)
¬0≡𝒰 ()

¬0≡incons : ∀ {i} → ¬ (0ᵤ {i} ≡ incons)
¬0≡incons ()

¬ℕ≡F : ∀ {i} → {f : FinFun {i}} → ¬ (ℕ {↑ i} ≡ F f)
¬ℕ≡F ()

¬ℕ≡refl : ∀ {i} → {v : Nbh {i}} → ¬ (ℕ {i} ≡ refl v)
¬ℕ≡refl ()

¬ℕ≡I : ∀ {i} → {U u v : Nbh {i}} → ¬ (ℕ {i} ≡ I U u v)
¬ℕ≡I ()

¬ℕ≡Π : ∀ {i} → {U : Nbh {i}} → {f : FinFun {i}} → ¬ (ℕ {↑ i} ≡ Π U f)
¬ℕ≡Π ()

¬ℕ≡𝒰 : ∀ {i} → ¬ (ℕ {i} ≡ 𝒰)
¬ℕ≡𝒰 ()

¬ℕ≡incons : ∀ {i} → ¬ (ℕ {i} ≡ incons)
¬ℕ≡incons ()

¬s≡ℕ : ∀ {i} → {u : Nbh {i}} → ¬ (s u ≡ ℕ)
¬s≡ℕ ()

¬s≡F : ∀ {i} → {u : Nbh {↑ i}} → {f : FinFun {i}} → ¬ (s u ≡ F f)
¬s≡F ()

¬s≡refl : ∀ {i} → {u v : Nbh {i}} → ¬ (s u ≡ refl v)
¬s≡refl ()

¬s≡I : ∀ {i} → {u U v v′ : Nbh {i}} → ¬ (s u ≡ I U v v′)
¬s≡I ()

¬s≡Π : ∀ {i} → {u U : Nbh {i}} → {f : FinFun {i}} → ¬ (s u ≡ Π U f)
¬s≡Π ()

¬s≡𝒰 : ∀ {i} → {u : Nbh {i}} → ¬ (s u ≡ 𝒰)
¬s≡𝒰 ()

¬s≡incons : ∀ {i} → {u : Nbh {i}} → ¬ (s u ≡ incons)
¬s≡incons ()

¬F≡refl : ∀ {i} → {f : FinFun {i}} → {v : Nbh {i}} → ¬ (F f ≡ refl v)
¬F≡refl ()

¬F≡I : ∀ {i} → {f : FinFun {i}} → {U u v : Nbh {i}} → ¬ (F f ≡ I U u v)
¬F≡I ()

¬F≡Π : ∀ {i} → {f : FinFun {i}} → {U : Nbh {i}} → {g : FinFun {i}} → ¬ (F f ≡ Π U g)
¬F≡Π ()

¬F≡𝒰 : ∀ {i} → {f : FinFun {i}} → ¬ (F f ≡ 𝒰)
¬F≡𝒰 ()

¬F≡incons : ∀ {i} → {f : FinFun {i}} → ¬ (F f ≡ incons)
¬F≡incons ()

¬refl≡I : ∀ {i} → {u U v v′ : Nbh {i}} → ¬ (refl u ≡ I U v v′)
¬refl≡I ()

¬refl≡Π : ∀ {i} → {u U : Nbh {i}} → {f : FinFun {i}} → ¬ (refl u ≡ Π U f)
¬refl≡Π ()

¬refl≡𝒰 : ∀ {i} → {u : Nbh {i}} → ¬ (refl u ≡ 𝒰)
¬refl≡𝒰 ()

¬refl≡incons : ∀ {i} → {u : Nbh {i}} → ¬ (refl u ≡ incons)
¬refl≡incons ()

¬I≡Π : ∀ {i} → {U u v V : Nbh {i}} → {f : FinFun {i}} → ¬ (I U u v ≡ Π V f)
¬I≡Π ()

¬I≡𝒰 : ∀ {i} → {U u v : Nbh {i}} → ¬ (I U u v ≡ 𝒰)
¬I≡𝒰 ()

¬I≡incons : ∀ {i} → {U u v : Nbh {i}} → ¬ (I U u v ≡ incons)
¬I≡incons ()

¬Π≡𝒰 : ∀ {i} → {U : Nbh {i}} → {f : FinFun {i}} → ¬ (Π U f ≡ 𝒰)
¬Π≡𝒰 ()

¬Π≡incons : ∀ {i} → {U : Nbh {i}} → {f : FinFun {i}} → ¬ (Π U f ≡ incons)
¬Π≡incons ()

¬𝒰≡incons : ∀ {i} → ¬ (𝒰 {i} ≡ incons)
¬𝒰≡incons ()

⊥decidableEquality : ∀ {i} → {v : Nbh {i}} → Decidable (⊥ ≡ v)
⊥decidableEquality {v = ⊥} = inl refl
⊥decidableEquality {v = 0ᵤ} = inr ¬⊥≡0
⊥decidableEquality {v = s _} = inr ¬⊥≡s
⊥decidableEquality {v = ℕ} = inr ¬⊥≡ℕ
⊥decidableEquality {v = F _} = inr ¬⊥≡F
⊥decidableEquality {v = refl _} = inr ¬⊥≡refl
⊥decidableEquality {v = I _ _ _} = inr ¬⊥≡I
⊥decidableEquality {v = Π _ _} = inr ¬⊥≡Π
⊥decidableEquality {v = 𝒰} = inr ¬⊥≡𝒰
⊥decidableEquality {v = incons} = inr ¬⊥≡incons

0decidableEquality : ∀ {i} → {v : Nbh {i}} → Decidable (0ᵤ ≡ v)
0decidableEquality {v = ⊥} = inr (¬eqSym ¬⊥≡0)
0decidableEquality {v = 0ᵤ} = inl refl
0decidableEquality {v = s _} = inr ¬0≡s
0decidableEquality {v = ℕ} = inr ¬0≡ℕ
0decidableEquality {v = F _} = inr ¬0≡F
0decidableEquality {v = refl _} = inr ¬0≡refl
0decidableEquality {v = I _ _ _} = inr ¬0≡I
0decidableEquality {v = Π _ _} = inr ¬0≡Π
0decidableEquality {v = 𝒰} = inr ¬0≡𝒰
0decidableEquality {v = incons} = inr ¬0≡incons

ℕdecidableEquality : ∀ {i} → {v : Nbh {i}} → Decidable (ℕ ≡ v)
ℕdecidableEquality {v = ⊥} = inr (¬eqSym ¬⊥≡ℕ)
ℕdecidableEquality {v = 0ᵤ} = inr (¬eqSym ¬0≡ℕ)
ℕdecidableEquality {v = s _} = inr (¬eqSym ¬s≡ℕ)
ℕdecidableEquality {v = ℕ} = inl refl
ℕdecidableEquality {v = F _} = inr ¬ℕ≡F
ℕdecidableEquality {v = refl _} = inr ¬ℕ≡refl
ℕdecidableEquality {v = I _ _ _} = inr ¬ℕ≡I
ℕdecidableEquality {v = Π _ _} = inr ¬ℕ≡Π
ℕdecidableEquality {v = 𝒰} = inr ¬ℕ≡𝒰
ℕdecidableEquality {v = incons} = inr ¬ℕ≡incons

𝒰decidableEquality : ∀ {i} → {v : Nbh {i}} → Decidable (𝒰 ≡ v)
𝒰decidableEquality {v = ⊥} = inr (¬eqSym ¬⊥≡𝒰)
𝒰decidableEquality {v = 0ᵤ} = inr (¬eqSym ¬0≡𝒰)
𝒰decidableEquality {v = s _} = inr (¬eqSym ¬s≡𝒰)
𝒰decidableEquality {v = ℕ} = inr (¬eqSym ¬ℕ≡𝒰)
𝒰decidableEquality {v = F _} = inr (¬eqSym ¬F≡𝒰)
𝒰decidableEquality {v = refl _} = inr (¬eqSym ¬refl≡𝒰)
𝒰decidableEquality {v = I _ _ _} = inr (¬eqSym ¬I≡𝒰)
𝒰decidableEquality {v = Π _ _} = inr (¬eqSym ¬Π≡𝒰)
𝒰decidableEquality {v = 𝒰} = inl refl
𝒰decidableEquality {v = incons} = inr ¬𝒰≡incons

inconsDecidableEquality : ∀ {i} → {v : Nbh {i}} → Decidable (incons ≡ v)
inconsDecidableEquality {v = ⊥} = inr (¬eqSym ¬⊥≡incons)
inconsDecidableEquality {v = 0ᵤ} = inr (¬eqSym ¬0≡incons)
inconsDecidableEquality {v = s _} = inr (¬eqSym ¬s≡incons)
inconsDecidableEquality {v = ℕ} = inr (¬eqSym ¬ℕ≡incons)
inconsDecidableEquality {v = F _} = inr (¬eqSym ¬F≡incons)
inconsDecidableEquality {v = refl _} = inr (¬eqSym ¬refl≡incons)
inconsDecidableEquality {v = I _ _ _} = inr (¬eqSym ¬I≡incons)
inconsDecidableEquality {v = Π _ _} = inr (¬eqSym ¬Π≡incons)
inconsDecidableEquality {v = 𝒰} = inr (¬eqSym ¬𝒰≡incons)
inconsDecidableEquality {v = incons} = inl refl

decidableEquality : ∀ {i} → {u v : Nbh {i}} → Decidable (u ≡ v)
decidableEqualityFinFun : ∀ {i} → {f g : FinFun {i}} → Decidable (f ≡ g)

decidableEquality {u = ⊥} = ⊥decidableEquality
decidableEquality {u = 0ᵤ} = 0decidableEquality
decidableEquality {u = s _} {v = ⊥} = inr (¬eqSym ¬⊥≡s)
decidableEquality {u = s _} {v = 0ᵤ} = inr (¬eqSym ¬0≡s)
decidableEquality {u = s u} {v = s v} with (decidableEquality {u = u} {v})
... | inl refl = inl refl
... | inr ¬u≡v = inr lemma
  where lemma : ¬ (s u ≡ s v)
        lemma refl = ¬u≡v refl
decidableEquality {u = s _} {v = ℕ} = inr ¬s≡ℕ
decidableEquality {u = s _} {v = F _} = inr ¬s≡F
decidableEquality {u = s _} {v = refl _} = inr ¬s≡refl
decidableEquality {u = s _} {v = I _ _ _} = inr ¬s≡I
decidableEquality {u = s _} {v = Π _ _} = inr ¬s≡Π
decidableEquality {u = s _} {v = 𝒰} = inr ¬s≡𝒰
decidableEquality {u = s _} {v = incons} = inr ¬s≡incons
decidableEquality {u = ℕ} = ℕdecidableEquality
decidableEquality {u = F _} {⊥} = inr (¬eqSym ¬⊥≡F)
decidableEquality {u = F _} {0ᵤ} = inr (¬eqSym ¬0≡F)
decidableEquality {u = F _} {s _} = inr (¬eqSym ¬s≡F)
decidableEquality {u = F _} {ℕ} = inr (¬eqSym ¬ℕ≡F)
decidableEquality {u = F f} {F g} with (decidableEqualityFinFun {f = f} {g})
... | inl refl = inl refl
... | inr ¬f≡g = inr lemma
  where lemma : ¬ (F f ≡ F g)
        lemma refl = ¬f≡g refl
decidableEquality {u = F _} {refl _} = inr ¬F≡refl
decidableEquality {u = F _} {I _ _ _} = inr ¬F≡I
decidableEquality {u = F _} {Π _ _} = inr ¬F≡Π
decidableEquality {u = F _} {𝒰} = inr ¬F≡𝒰
decidableEquality {u = F _} {incons} = inr ¬F≡incons
decidableEquality {u = refl _} {⊥} = inr (¬eqSym ¬⊥≡refl)
decidableEquality {u = refl _} {0ᵤ} = inr (¬eqSym ¬0≡refl)
decidableEquality {u = refl _} {s _} = inr (¬eqSym ¬s≡refl)
decidableEquality {u = refl _} {ℕ} = inr (¬eqSym ¬ℕ≡refl)
decidableEquality {u = refl _} {F _} = inr (¬eqSym ¬F≡refl)
decidableEquality {u = refl u} {refl v} with (decidableEquality {u = u} {v})
... | inl refl = inl refl
... | inr ¬u≡v = inr lemma
  where lemma : ¬ (refl u ≡ refl v)
        lemma refl = ¬u≡v refl
decidableEquality {u = refl _} {I _ _ _} = inr ¬refl≡I
decidableEquality {u = refl _} {Π _ _} = inr ¬refl≡Π
decidableEquality {u = refl _} {𝒰} = inr ¬refl≡𝒰
decidableEquality {u = refl _} {incons} = inr ¬refl≡incons
decidableEquality {u = I _ _ _} {⊥} = inr (¬eqSym ¬⊥≡I)
decidableEquality {u = I _ _ _} {0ᵤ} = inr (¬eqSym ¬0≡I)
decidableEquality {u = I _ _ _} {s _} = inr (¬eqSym ¬s≡I)
decidableEquality {u = I _ _ _} {ℕ} = inr (¬eqSym ¬ℕ≡I)
decidableEquality {u = I _ _ _} {F _} = inr (¬eqSym ¬F≡I)
decidableEquality {u = I _ _ _} {refl _} = inr (¬eqSym ¬refl≡I)
decidableEquality {u = I U u v} {I U′ u′ v′ }
  with (decidableEquality {u = U} {U′}) | decidableEquality {u = u} {u′} | decidableEquality {u = v} {v′}
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
decidableEquality {u = I _ _ _} {Π _ _} = inr ¬I≡Π
decidableEquality {u = I _ _ _} {𝒰} = inr ¬I≡𝒰
decidableEquality {u = I _ _ _} {incons} = inr ¬I≡incons
decidableEquality {u = Π _ _} {⊥} = inr (¬eqSym ¬⊥≡Π)
decidableEquality {u = Π _ _} {0ᵤ} = inr (¬eqSym ¬0≡Π)
decidableEquality {u = Π _ _} {s _} = inr (¬eqSym ¬s≡Π)
decidableEquality {u = Π _ _} {ℕ} = inr (¬eqSym ¬ℕ≡Π)
decidableEquality {u = Π _ _} {F _} = inr (¬eqSym ¬F≡Π)
decidableEquality {u = Π _ _} {refl _} = inr (¬eqSym ¬refl≡Π)
decidableEquality {u = Π _ _} {I _ _ _} = inr (¬eqSym ¬I≡Π)
decidableEquality {u = Π U f} {Π V g}
  with (decidableEquality {u = U} {V}) | decidableEqualityFinFun {f = f} {g}
... | inl refl | inl refl = inl refl
... | inl refl | inr ¬g≡g = inr lemma
  where lemma : ¬ (Π U f ≡ Π V g)
        lemma refl = ¬g≡g refl
... | inr ¬f≡f | _ = inr lemma
  where lemma : ¬ (Π U f ≡ Π V g)
        lemma refl = ¬f≡f refl
decidableEquality {u = Π _ _} {𝒰} = inr ¬Π≡𝒰
decidableEquality {u = Π _ _} {incons} = inr ¬Π≡incons
decidableEquality {u = 𝒰} {v} = 𝒰decidableEquality
decidableEquality {u = incons} {v} = inconsDecidableEquality

decidableEqualityFinFun {f = ∅} {∅} = inl refl
decidableEqualityFinFun {f = ∅} {(u′ , v′) ∷ g′} = inr lemma
  where lemma : ¬ (∅ ≡ (u′ , v′) ∷ g′)
        lemma ()
decidableEqualityFinFun {f = (u , v) ∷ f′} {∅} = inr lemma
  where lemma : ¬ ((u , v) ∷ f′ ≡ ∅)
        lemma ()
decidableEqualityFinFun {f = (u , v) ∷ f′} {(u′ , v′) ∷ g′}
  with (decidableEquality {u = u} {u′}) | decidableEquality {u = v} {v′} | decidableEqualityFinFun {f = f′} {g′}
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
