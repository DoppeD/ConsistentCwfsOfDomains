module Cwf.Nbh where

open import Base.Core hiding (_∨_)
open import Base.FinFun
open import Cwf.DavidBool

open import Agda.Builtin.Equality
open import Agda.Builtin.Size

data UniNbh : Size → Set where
  ⊥ : ∀ {i} → UniNbh i
  λᵤ : ∀ {i} → FinFun (UniNbh i) (UniNbh i) → UniNbh (↑ i)
  Π : ∀ {i} → UniNbh i → FinFun (UniNbh i) (UniNbh i) → UniNbh (↑ i)
  0ᵤ : ∀ {i} → UniNbh i
  s : ∀ {i} → UniNbh i → UniNbh i
  N : ∀ {i} → UniNbh i
  refl : ∀ {i} → UniNbh i → UniNbh i
  I : ∀ {i} → UniNbh i → UniNbh i → UniNbh i → UniNbh i
  𝔘₀ : ∀ {i} → UniNbh i

-- Identity of elements of u as a function.
_≈ᵤ_ : ∀ {i} → UniNbh i → UniNbh i → Bool
equalFun : ∀ {i} → FinFun (UniNbh i) (UniNbh i) → FinFun (UniNbh i) (UniNbh i) → Bool

⊥ ≈ᵤ ⊥ = true
(λᵤ f) ≈ᵤ (λᵤ g) = equalFun f g
(Π u f) ≈ᵤ (Π u′ g) = u ≈ᵤ u′ ∧ equalFun f g
0ᵤ ≈ᵤ 0ᵤ = true
(s u) ≈ᵤ (s u′) = u ≈ᵤ u′
N ≈ᵤ N = true
(refl u) ≈ᵤ (refl u′) = u ≈ᵤ u′
(I U u u′) ≈ᵤ (I V v v′)
  = U ≈ᵤ V ∧ u ≈ᵤ v ∧ u′ ≈ᵤ v′
𝔘₀ ≈ᵤ 𝔘₀ = true
u ≈ᵤ u′ = false

equalFun ∅ ∅ = true
equalFun ∅ (_ ∷ _) = false
equalFun (_ ∷ _) ∅ = false
equalFun ((u , v) ∷ fs) ((u′ , v′) ∷ gs)
  = u ≈ᵤ v ∧ v ≈ᵤ v′ ∧ equalFun fs gs

-- An algorithm that determines whether two elements are consistent...
areCons : ∀ {i} → UniNbh i → UniNbh i → Bool

-- ...mutually defined with one that determines whether a finite function
-- is consistent.
isConsFun : ∀ {i} → FinFun (UniNbh i) (UniNbh i) → Bool

areCons ⊥ u = true
areCons u ⊥ = true
areCons (λᵤ f) (λᵤ g) = isConsFun (f ∪ g)
areCons (Π u f) (Π u′ g) = areCons u u′ ∧ isConsFun (f ∪ g)
areCons (s m) (s n) = areCons m n
areCons (refl u) (refl u′) = areCons u u′
areCons (I U u u′) (I V v v′)
  = areCons U V ∧ areCons u v ∧ areCons u′ v′
-- If none of the above apply, then the elements are consistent
-- iff they are equal. We should check and make sure that
-- nothing slips by here.
areCons u v = u ≈ᵤ v

isConsFun ∅ = true
isConsFun ((_ , _) ∷ ∅) = true
isConsFun ((u , v) ∷ ((u′ , v′) ∷ xs))
  = isConsFun ((u′ , v′) ∷ xs) ∧
    isConsFun ((u , v) ∷ xs) ∧
    (not (areCons u u′) ∨ areCons v v′)

-- If we remove the first element from a consistent finite function, what remains
-- is also a consistent finite function.
consFunLemma₁ : ∀ {i} → (f : (UniNbh i) ⊠ (UniNbh i)) →
                (fs : FinFun (UniNbh i) (UniNbh i)) →
                isConsFun (f ∷ fs) ≡ true →
                isConsFun fs ≡ true
consFunLemma₁ f ∅ _ = refl
consFunLemma₁ (u , v) ((u′ , v′) ∷ fs) p = ∧-lemma₁ (∧-lemma₁ p)

sup : ∀ {i} → (u v : UniNbh i) → areCons u v ≡ true → UniNbh i
sup ⊥ v _ = v
sup u ⊥ _ = u
sup (λᵤ f) (λᵤ g) _ = λᵤ (f ∪ g)
sup (Π u f) (Π u′ g) p = Π (sup u u′ (∧-lemma₁ p)) (f ∪ g)
sup 0ᵤ 0ᵤ _ = 0ᵤ
sup N N _ = N
sup (refl u) (refl v) p = refl (sup u v p)
sup (s u) (s v) p = s (sup u v p)
sup (I U u u′) (I V v v′) p
  = I (sup U V (∧-lemma₁ (∧-lemma₁ p)))
      (sup u v (∧-lemma₂ {p = areCons U V} (∧-lemma₁ {q = areCons u′ v′} p)))
      (sup u′ v′ (∧-lemma₂ p))
sup 𝔘₀ 𝔘₀ _ = 𝔘₀
