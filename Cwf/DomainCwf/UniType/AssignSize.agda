{-# OPTIONS --safe #-}

module Cwf.DomainCwf.UniType.AssignSize where

open import Base.Core
open import Base.FinFun
open import Cwf.DomainCwf.UniType.Definition

open import Data.Nat.Base renaming (_⊔_ to max ; ℕ to Nat)
open import Data.Nat.Induction
open import Data.Nat.Properties
open import Induction.WellFounded

-- We assign to each neighborhood a natural number, which corresponds to
-- the maximum nesting depth of constructors. For finite functions, we take
-- the maximum of the sizes assigned to its elements. For example, for a finite function
-- (u , v) ∷ (u′ , v′) ∷ ∅, its size is the maximum of the sizes of u, v, u′, and v′.
assignSize : Nbh → Nat
assignSizeFun : FinFun Nbh Nbh → Nat

assignSize ⊥ = 0
assignSize 0ᵤ = 0
assignSize (s u) = suc (assignSize u)
assignSize ℕ = 0
assignSize (F f) = suc (assignSizeFun f)
assignSize (refl u) = suc (assignSize u)
assignSize (I U u v) = suc (max (max (assignSize U) (assignSize u)) (assignSize v))
assignSize (Π U f) = suc (max (assignSize U) (suc (assignSizeFun f)))
assignSize 𝒰 = 0
assignSize incons = 0

assignSizeFun ∅ = 0
assignSizeFun ((u , v) ∷ f) =
  max (max (assignSize u) (assignSize v)) (assignSizeFun f)

maxLemma : ∀ {m n o p} → m ≤ o → n ≤ p → (max m n) ≤ (max o p)
maxLemma m≤o n≤p = ⊔-lub (m≤n⇒m≤n⊔o _ m≤o) (m≤n⇒m≤o⊔n _ n≤p)

uv∈f⇒u≤f : ∀ f u v → (u , v) ∈ f → assignSize u ≤ assignSizeFun f
uv∈f⇒u≤f ((u , v) ∷ f) _ _ here
  = ≤-trans (m≤m⊔n (assignSize u) (assignSize v)) (m≤m⊔n (max (assignSize u) (assignSize v)) (assignSizeFun f))
uv∈f⇒u≤f ((u , v) ∷ f) u′ v′ (there u′v′∈f)
  = ≤-trans (uv∈f⇒u≤f f u′ v′ u′v′∈f) (m≤n⊔m (max (assignSize u) (assignSize v)) (assignSizeFun f))

uv∈f⇒v≤f : ∀ f u v → (u , v) ∈ f → assignSize v ≤ assignSizeFun f
uv∈f⇒v≤f ((u , v) ∷ f) _ _ here
  = ≤-trans (m≤n⊔m (assignSize u) (assignSize v)) (m≤m⊔n (max (assignSize u) (assignSize v)) (assignSizeFun f))
uv∈f⇒v≤f ((u , v) ∷ f) u′ v′ (there u′v′∈f)
  = ≤-trans (uv∈f⇒v≤f f u′ v′ u′v′∈f) (m≤n⊔m (max (assignSize u) (assignSize v)) (assignSizeFun f))

u⊔v≤maxuv : ∀ u v → assignSize (u ⊔ v) ≤ (max (assignSize u) (assignSize v))
f∪g≤maxfg : ∀ f g → assignSizeFun (f ∪ g) ≤ max (assignSizeFun f) (assignSizeFun g)

u⊔v≤maxuv ⊥ ⊥ = z≤n
u⊔v≤maxuv ⊥ 0ᵤ = z≤n
u⊔v≤maxuv ⊥ (s _) = ≤-refl
u⊔v≤maxuv ⊥ ℕ = ≤-refl
u⊔v≤maxuv ⊥ (F _) = s≤s ≤-refl
u⊔v≤maxuv ⊥ (refl _) = ≤-refl
u⊔v≤maxuv ⊥ (I _ _ _) = ≤-refl
u⊔v≤maxuv ⊥ (Π _ _) = ≤-refl
u⊔v≤maxuv ⊥ 𝒰 = ≤-refl
u⊔v≤maxuv ⊥ incons = z≤n
u⊔v≤maxuv 0ᵤ ⊥ = z≤n
u⊔v≤maxuv 0ᵤ 0ᵤ = z≤n
u⊔v≤maxuv 0ᵤ (s _) = z≤n
u⊔v≤maxuv 0ᵤ ℕ = z≤n
u⊔v≤maxuv 0ᵤ (F _) = z≤n
u⊔v≤maxuv 0ᵤ (refl _) = z≤n
u⊔v≤maxuv 0ᵤ (I _ _ _) = z≤n
u⊔v≤maxuv 0ᵤ (Π _ _) = z≤n
u⊔v≤maxuv 0ᵤ 𝒰 = z≤n
u⊔v≤maxuv 0ᵤ incons = z≤n
u⊔v≤maxuv (s _) ⊥ = ≤-refl
u⊔v≤maxuv (s _) 0ᵤ = z≤n
u⊔v≤maxuv (s u) (s v) = s≤s (u⊔v≤maxuv u v)
u⊔v≤maxuv (s _) ℕ = z≤n
u⊔v≤maxuv (s _) (F _) = z≤n
u⊔v≤maxuv (s _) (refl _) = z≤n
u⊔v≤maxuv (s _) (I _ _ _) = z≤n
u⊔v≤maxuv (s _) (Π _ _) = z≤n
u⊔v≤maxuv (s _) 𝒰 = z≤n
u⊔v≤maxuv (s _) incons = z≤n
u⊔v≤maxuv ℕ ⊥ = z≤n
u⊔v≤maxuv ℕ 0ᵤ = z≤n
u⊔v≤maxuv ℕ (s _) = z≤n
u⊔v≤maxuv ℕ ℕ = z≤n
u⊔v≤maxuv ℕ (F _) = z≤n
u⊔v≤maxuv ℕ (refl _) = z≤n
u⊔v≤maxuv ℕ (I _ _ _) = z≤n
u⊔v≤maxuv ℕ (Π _ _) = z≤n
u⊔v≤maxuv ℕ 𝒰 = z≤n
u⊔v≤maxuv ℕ incons = z≤n
u⊔v≤maxuv (F _) ⊥ = s≤s ≤-refl
u⊔v≤maxuv (F _) 0ᵤ = z≤n
u⊔v≤maxuv (F _) (s _) = z≤n
u⊔v≤maxuv (F _) ℕ = z≤n
u⊔v≤maxuv (F f) (F g) = s≤s (f∪g≤maxfg f g)
u⊔v≤maxuv (F _) (refl _) = z≤n
u⊔v≤maxuv (F _) (I _ _ _) = z≤n
u⊔v≤maxuv (F _) (Π _ _) = z≤n
u⊔v≤maxuv (F _) 𝒰 = z≤n
u⊔v≤maxuv (F _) incons = z≤n
u⊔v≤maxuv (refl _) ⊥ = ≤-refl
u⊔v≤maxuv (refl _) 0ᵤ = z≤n
u⊔v≤maxuv (refl _) (s _) = z≤n
u⊔v≤maxuv (refl _) ℕ = z≤n
u⊔v≤maxuv (refl _) (F _) = z≤n
u⊔v≤maxuv (refl u) (refl v) = s≤s (u⊔v≤maxuv u v)
u⊔v≤maxuv (refl _) (I _ _ _) = z≤n
u⊔v≤maxuv (refl _) (Π _ _) = z≤n
u⊔v≤maxuv (refl _) 𝒰 = z≤n
u⊔v≤maxuv (refl _) incons = z≤n
u⊔v≤maxuv (I _ _ _) ⊥ = s≤s ≤-refl
u⊔v≤maxuv (I _ _ _) 0ᵤ = z≤n
u⊔v≤maxuv (I _ _ _) (s _) = z≤n
u⊔v≤maxuv (I _ _ _) ℕ = z≤n
u⊔v≤maxuv (I _ _ _) (F _) = z≤n
u⊔v≤maxuv (I _ _ _) (refl _) = z≤n
u⊔v≤maxuv (I U u u′) (I V v v′)
  = s≤s (⊔-lub a b)
  where asU : Nat
        asU = assignSize U
        asu : Nat
        asu = assignSize u
        asu′ : Nat
        asu′ = assignSize u′
        asV : Nat
        asV = assignSize V
        asv : Nat
        asv = assignSize v
        asv′ : Nat
        asv′ = assignSize v′
        uBound : Nat
        uBound = max (max (max asU asu) asu′) (max (max asV asv) asv′)
        c : max asU asV ≤ uBound
        c = maxLemma {asU} (≤-trans (m≤m⊔n _ _) (m≤m⊔n _ _)) (≤-trans (m≤m⊔n _ _) (m≤m⊔n _ _))
        d : max asu asv ≤ uBound
        d = maxLemma (≤-trans {asu} {max asU asu} (m≤n⊔m _ _)
            (m≤m⊔n (max asU asu) asu′)) (≤-trans {asv} {max asV asv}
            (m≤n⊔m _ _) (m≤m⊔n _ _))
        a : max (assignSize (U ⊔ V)) (assignSize (u ⊔ v)) ≤ uBound
        a = ⊔-lub (≤-trans (u⊔v≤maxuv U V) c) (≤-trans (u⊔v≤maxuv u v) d)
        b : assignSize (u′ ⊔ v′) ≤ uBound
        b = ≤-trans (u⊔v≤maxuv u′ v′) (maxLemma {asu′} {asv′} {max (max asU asu) asu′} (m≤n⊔m _ _) (m≤n⊔m _ _))
u⊔v≤maxuv (I _ _ _) (Π _ _) = z≤n
u⊔v≤maxuv (I _ _ _) 𝒰 = z≤n
u⊔v≤maxuv (I _ _ _) incons = z≤n
u⊔v≤maxuv (Π _ _) ⊥ = s≤s ≤-refl
u⊔v≤maxuv (Π _ _) 0ᵤ = z≤n
u⊔v≤maxuv (Π _ _) (s _) = z≤n
u⊔v≤maxuv (Π _ _) ℕ = z≤n
u⊔v≤maxuv (Π _ _) (F _) = z≤n
u⊔v≤maxuv (Π _ _) (refl _) = z≤n
u⊔v≤maxuv (Π _ _) (I _ _ _) = z≤n
u⊔v≤maxuv (Π U f) (Π V g) = s≤s (⊔-lub a b)
  where c : ∀ {u v} → max (assignSize U) (assignSize V) ≤ max (max (assignSize U) u) (max (assignSize V) v)
        c = maxLemma (m≤m⊔n (assignSize U) _) (m≤m⊔n (assignSize V) _)
        a : ∀ {u v} → assignSize (U ⊔ V) ≤ max (max (assignSize U) u) (max (assignSize V) v)
        a = ≤-trans (u⊔v≤maxuv U V) c
        b : ∀ {v} → suc (assignSizeFun (f ∪ g)) ≤ max (max (assignSize U) (suc (assignSizeFun f))) (max v (suc (assignSizeFun g)))
        b = ≤-trans (s≤s (f∪g≤maxfg f g)) (maxLemma (m≤n⊔m (assignSize U) (suc (assignSizeFun f))) (m≤n⊔m _ (suc (assignSizeFun g))))
u⊔v≤maxuv (Π _ _) 𝒰 = z≤n
u⊔v≤maxuv (Π _ _) incons = z≤n
u⊔v≤maxuv 𝒰 ⊥ = z≤n
u⊔v≤maxuv 𝒰 0ᵤ = z≤n
u⊔v≤maxuv 𝒰 (s _) = z≤n
u⊔v≤maxuv 𝒰 ℕ = z≤n
u⊔v≤maxuv 𝒰 (F _) = z≤n
u⊔v≤maxuv 𝒰 (refl _) = z≤n
u⊔v≤maxuv 𝒰 (I _ _ _) = z≤n
u⊔v≤maxuv 𝒰 (Π _ _) = z≤n
u⊔v≤maxuv 𝒰 𝒰 = z≤n
u⊔v≤maxuv 𝒰 incons = z≤n
u⊔v≤maxuv incons _ = z≤n

f∪g≤maxfg ∅ g = ≤-refl
f∪g≤maxfg ((u , v) ∷ f) g
  rewrite (⊔-assoc (max (assignSize u) (assignSize v)) (assignSizeFun f) (assignSizeFun g))
  = maxLemma (≤-refl {max (assignSize u) (assignSize v)}) (f∪g≤maxfg f g)

pref≤f : ∀ f → assignSize (pre f) ≤ assignSizeFun f
pref≤f ∅ = z≤n
pref≤f ((u , v) ∷ f)
  = ≤-trans (u⊔v≤maxuv u (pre f)) (maxLemma (m≤m⊔n _ _) (pref≤f f))

pref<Ff : ∀ f → (assignSize (pre f) < assignSize (F f))
pref<Ff f = <-transʳ (pref≤f f) (n<1+n (assignSizeFun f))

f⊆g⇒f≤g : ∀ f g → f ⊆ g → assignSizeFun f ≤ assignSizeFun g
f⊆g⇒f≤g ∅ _ _ = z≤n
f⊆g⇒f≤g ((u , v) ∷ f) g f⊆g
  = ⊔-lub (⊔-lub (uv∈f⇒u≤f g u v (f⊆g here)) (uv∈f⇒v≤f g u v (f⊆g here))) (f⊆g⇒f≤g f g (λ x∈f → f⊆g (there x∈f)))

f⊆g⇒pref⇐g : ∀ f g → f ⊆ g → (assignSize (pre f) < assignSize (F g))
f⊆g⇒pref⇐g f g f⊆g = <-transˡ (pref<Ff f) (s≤s (f⊆g⇒f≤g f g f⊆g))

uvu′v′∈f⇒u⊔u′≤f : ∀ {u v u′ v′ f} → (u , v) ∈ f → (u′ , v′) ∈ f → assignSize (u ⊔ u′) ≤ assignSizeFun f
uvu′v′∈f⇒u⊔u′≤f {u} {v} {u′} {v′} {f} uv∈f u′v′∈f
  = ≤-trans (u⊔v≤maxuv u u′) (⊔-lub (uv∈f⇒u≤f f u v uv∈f) (uv∈f⇒u≤f f u′ v′ u′v′∈f))

uvu′v′∈f⇒v⊔v′≤f : ∀ {u v u′ v′ f} → (u , v) ∈ f → (u′ , v′) ∈ f → assignSize (v ⊔ v′) ≤ assignSizeFun f
uvu′v′∈f⇒v⊔v′≤f {u} {v} {u′} {v′} {f} uv∈f u′v′∈f
  = ≤-trans (u⊔v≤maxuv v v′) (⊔-lub (uv∈f⇒v≤f f u v uv∈f) (uv∈f⇒v≤f f u′ v′ u′v′∈f))

uv∈f⇒u<ΠUf : ∀ {U f u v} → (u , v) ∈ f → assignSize u < assignSize (Π U f)
uv∈f⇒u<ΠUf {u = u} uv∈f
  = s≤s (≤-trans {assignSize (u)} (≤-trans (uv∈f⇒u≤f _ _ _ uv∈f) (n≤1+n _)) (m≤n⊔m _ _))

uv∈f⇒v<ΠUf : ∀ {U f u v} → (u , v) ∈ f → assignSize v < assignSize (Π U f)
uv∈f⇒v<ΠUf {v = v} uv∈f
  = s≤s (≤-trans {assignSize (v)} (≤-trans (uv∈f⇒v≤f _ _ _ uv∈f) (n≤1+n _)) (m≤n⊔m _ _))

u⊔u′<ΠUf : ∀ {U f u v u′ v′} → (u , v) ∈ f → (u′ , v′) ∈ f → assignSize (u ⊔ u′) < assignSize (Π U f)
u⊔u′<ΠUf {u = u} {u′ = u′} uv∈f u′v′∈f
  = s≤s (≤-trans {assignSize (u ⊔ u′)} (≤-trans (uvu′v′∈f⇒u⊔u′≤f uv∈f u′v′∈f) (n≤1+n _)) (m≤n⊔m _ _))

v⊔v′<ΠUf : ∀ {U f u v u′ v′} → (u , v) ∈ f → (u′ , v′) ∈ f → assignSize (v ⊔ v′) < assignSize (Π U f)
v⊔v′<ΠUf {v = v} {v′ = v′} uv∈f u′v′∈f
  = s≤s (≤-trans {assignSize (v ⊔ v′)} (≤-trans (uvu′v′∈f⇒v⊔v′≤f uv∈f u′v′∈f) (n≤1+n _)) (m≤n⊔m _ _))

U<IUuu′ : ∀ {U u u′} → assignSize U < assignSize (I U u u′)
U<IUuu′ {U} {u} {u′} = s≤s (≤-trans (m≤m⊔n _ _) (m≤m⊔n _ _))

u<IUuu′ : ∀ {U u u′} → assignSize u < assignSize (I U u u′)
u<IUuu′ {U} {u} {u′} = s≤s (≤-trans (m≤n⊔m (assignSize U) _) (m≤m⊔n _ _))

u′<IUuu′ : ∀ {U u u′} → assignSize u′ < assignSize (I U u u′)
u′<IUuu′ {U} {u} {u′} = s≤s (m≤n⊔m _ _)
