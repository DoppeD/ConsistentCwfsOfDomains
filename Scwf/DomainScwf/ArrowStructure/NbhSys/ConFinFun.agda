{-# OPTIONS --safe #-}

open import Base.Core

module Scwf.DomainScwf.ArrowStructure.NbhSys.ConFinFun
  (𝐴 𝐵 : Ty) where

open import Base.FinFun
open import NbhSys.Definition
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Post 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Pre 𝐴 𝐵

open import Agda.Builtin.Equality

-- A finite function 𝑓 is consistent if every preable subset
-- of it is also postable.
data ConFinFun (𝑓 : NbhFinFun 𝐴 𝐵) : Set where
  cff : (∀ {𝑓′} → 𝑓′ ⊆ 𝑓 → Preable 𝑓′ → Postable 𝑓′) →
        ConFinFun 𝑓

subsetIsCon : ∀ {𝑓 𝑓′} → ConFinFun 𝑓′ → 𝑓 ⊆ 𝑓′ → ConFinFun 𝑓
subsetIsCon (cff p) 𝑓⊆𝑓′
  = cff (λ 𝑓″⊆𝑓 preable𝑓″ → p (⊆-trans 𝑓″⊆𝑓 𝑓⊆𝑓′) preable𝑓″)

singletonIsCon'' : ∀ {x y} → {𝑓 : NbhFinFun 𝐴 𝐵} →
                   𝑓 ⊆ ((x , y) ∷ ∅) →
                   ∀ {x′ y′} → (x′ , y′) ∈ 𝑓 →
                   [ 𝐵 ] y′ ⊑ y
singletonIsCon'' 𝑓⊆xy x′y′∈𝑓 with (𝑓⊆xy x′y′∈𝑓)
... | here = NbhSys.⊑-refl 𝐵

singletonIsCon' : ∀ {x y 𝑓} → 𝑓 ⊆ ((x , y) ∷ ∅) →
                  Preable 𝑓 → Postable 𝑓
singletonIsCon' 𝑓⊆xy preable𝑓 = boundedPostable (singletonIsCon'' 𝑓⊆xy)

singletonIsCon : ∀ {x y} → ConFinFun ((x , y) ∷ ∅)
singletonIsCon = cff (singletonIsCon')
