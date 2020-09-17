{-# OPTIONS --safe #-}

open import Base.Core

module Base.ConFinFun (𝐴 𝐵 : Ty) where

open import Base.FinFun
open import NbhSys.Definition

-- A predicate describing that γ maps x to y iff either (x, y) ∈ 𝑓
-- or γ : x ↦ y is inductively generated from the approximable mapping
-- axioms.
data InductivelyGenerated (𝑓 : NbhFinFun 𝐴 𝐵) : ∀ x y → Set where
  ig-inset : ∀ x y → < x , y > ∈ 𝑓 →
             InductivelyGenerated 𝑓 x y
  ig-bot  : ∀ x →
            InductivelyGenerated 𝑓 x (NbhSys.⊥ 𝐵)
  ig-mono : ∀ x x′ y → InductivelyGenerated 𝑓 x′ y → [ 𝐴 ] x′ ⊑ x →
            InductivelyGenerated 𝑓 x y
  ig-↓clo : ∀ x y y′ → InductivelyGenerated 𝑓 x y′ → [ 𝐵 ] y ⊑ y′ →
            InductivelyGenerated 𝑓 x y
  ig-↑dir : ∀ x y y′ → InductivelyGenerated 𝑓 x y →
            InductivelyGenerated 𝑓 x y′ → (con : NbhSys.Con 𝐵 y y′) →
            InductivelyGenerated 𝑓 x ([ 𝐵 ] y ⊔ y′ [ con ])

-- A finite function 𝑓 is consistent if, for any (x, y) and
-- and (x′, y′) that can be generated from 𝑓 and the axioms for
-- approximable mappings, if x and x′ are consistent then so are
-- y and y′.
data ConFinFun (𝑓 : FinFun (NbhSys.Nbh 𝐴) (NbhSys.Nbh 𝐵)) : Set where
  cff : (∀ {x y x′ y′} → InductivelyGenerated 𝑓 x y →
        InductivelyGenerated 𝑓 x′ y′ →
        (NbhSys.Con 𝐴 x x′) → (NbhSys.Con 𝐵 y y′)) →
        ConFinFun 𝑓
