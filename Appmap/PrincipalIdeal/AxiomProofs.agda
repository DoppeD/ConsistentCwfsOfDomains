open import Base.Core
open import NbhSys.Definition

module Appmap.PrincipalIdeal.AxiomProofs
  (𝐴 𝐵 : Ty) (gen : NbhSys.Nbh 𝐵) where

open import Appmap.PrincipalIdeal.Relation 𝐴 𝐵 gen

ideal↦-mono : ∀ {x y z} → [ 𝐴 ] x ⊑ y → x ideal↦ z →
              y ideal↦ z
ideal↦-mono _ (ideal↦-intro z⊑t) = ideal↦-intro z⊑t

ideal↦-bottom : ∀ {x} → x ideal↦ (NbhSys.⊥ 𝐵)
ideal↦-bottom = ideal↦-intro (NbhSys.⊑-⊥ 𝐵)

ideal↦-↓closed : ∀ {x y z} → [ 𝐵 ] y ⊑ z →
                 x ideal↦ z → x ideal↦ y
ideal↦-↓closed y⊑z (ideal↦-intro z⊑t)
  = ideal↦-intro (NbhSys.⊑-trans 𝐵 y⊑z z⊑t)

ideal↦-↑directed : ∀ {x y z} → x ideal↦ y →
                   x ideal↦ z → ∀ conyz →
                   x ideal↦ ([ 𝐵 ] y ⊔ z [ conyz ])
ideal↦-↑directed (ideal↦-intro y⊑t) (ideal↦-intro z⊑t) conyz
  = ideal↦-intro (NbhSys.⊑-⊔ 𝐵 y⊑t z⊑t conyz)

ideal↦-con : ∀ {x y x′ y′} →
             x ideal↦ y → x′ ideal↦ y′ →
             NbhSys.Con 𝐴 x x′ → NbhSys.Con 𝐵 y y′
ideal↦-con (ideal↦-intro y⊑t) (ideal↦-intro y′⊑t) _
  = NbhSys.Con-⊔ 𝐵 y⊑t y′⊑t
