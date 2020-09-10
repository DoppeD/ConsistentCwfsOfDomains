{-# OPTIONS --safe #-}

module Scwf.DomainScwf.PlainInstance where

open import Appmap.Equivalence
open import Base.Core
open import Scwf.Plain
open import Scwf.DomainScwf.Appmap.Definition
open import Scwf.DomainScwf.Appmap.Composition.Instance
open import Scwf.DomainScwf.Appmap.Empty.Instance
open import Scwf.DomainScwf.Appmap.Identity.Instance
open import Scwf.DomainScwf.Comprehension.Morphism.Instance
open import Scwf.DomainScwf.Comprehension.p.Instance
open import Scwf.DomainScwf.Comprehension.q.Instance
open import Scwf.DomainScwf.PlainAxiomProofs

domScwf : Scwf
Scwf.Ty domScwf       = Ty
Scwf.Ctx domScwf      = Ctx
Scwf.Tm domScwf Γ 𝐴   = tAppmap Γ [ 𝐴 ]
Scwf.Sub domScwf      = tAppmap
Scwf._≈_ domScwf      = _≈_
Scwf._≊_ domScwf      = _≈_
Scwf.isEquivT domScwf = ≈IsEquiv
Scwf.isEquivS domScwf = ≈IsEquiv
Scwf.◇ domScwf        = []
Scwf._•_ domScwf Γ 𝐴  = 𝐴 :: Γ
Scwf.q domScwf        = q
Scwf._[_] domScwf     = _∘_
Scwf.id domScwf       = idMap
Scwf._∘_ domScwf      = _∘_
Scwf.⟨⟩ domScwf       = emptyMap
Scwf.⟨_,_⟩ domScwf    = ⟨_,_⟩
Scwf.p domScwf        = p
Scwf.idL domScwf      = idL
Scwf.idR domScwf      = idR
Scwf.subAssoc domScwf = subAssoc
Scwf.idSub domScwf    = idSub
Scwf.compSub domScwf  = compSub
Scwf.id₀ domScwf      = id₀
Scwf.<>-zero domScwf  = <>-zero
Scwf.pCons domScwf    = pCons
Scwf.qCons domScwf    = qCons
Scwf.idExt domScwf    = idExt
Scwf.compExt domScwf  = compExt
Scwf.subCong domScwf  = ∘-cong
Scwf.<,>-cong domScwf = <,>-cong
Scwf.∘-cong domScwf   = ∘-cong
