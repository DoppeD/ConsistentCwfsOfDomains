{-# OPTIONS --safe --sized-types #-}

module Ucwf.DomainUcwf.PlainInstance where

open import Appmap.Equivalence
open import Base.Core
open import Base.FinFun
open import Scwf.DomainScwf.Appmap.Composition.Instance
open import Scwf.DomainScwf.Appmap.Empty.Instance
open import Scwf.DomainScwf.Appmap.Identity.Instance
open import Scwf.DomainScwf.PlainAxiomProofs
open import Scwf.DomainScwf.Comprehension.Morphism.Instance
open import Scwf.DomainScwf.Comprehension.p.Instance
open import Scwf.DomainScwf.Comprehension.q.Instance
open import Ucwf.DomainUcwf.Appmap.Definition
open import Ucwf.DomainUcwf.UniType.Instance
open import Ucwf.Plain

domUcwf : Ucwf
Ucwf.Tm domUcwf n     = uAppmap n 1
Ucwf.Sub domUcwf m n  = uAppmap m n
Ucwf.id domUcwf {n}   = idMap (nToCtx n)
Ucwf._≈_ domUcwf      = _≈_
Ucwf._≊_ domUcwf      = _≈_
Ucwf.isEquivT domUcwf = ≈IsEquiv
Ucwf.isEquivS domUcwf = ≈IsEquiv
Ucwf.q domUcwf {n}    = q (nToCtx n) UniType
Ucwf._[_] domUcwf     = _∘_
Ucwf._∘_ domUcwf      = _∘_
Ucwf.⟨⟩ domUcwf       = emptyMap
Ucwf.⟨_,_⟩ domUcwf    = ⟨_,_⟩
Ucwf.p domUcwf {n}    = p (nToCtx n) UniType
Ucwf.idL domUcwf      = idL
Ucwf.idR domUcwf      = idR
Ucwf.subAssoc domUcwf = subAssoc
Ucwf.idSub domUcwf    = idSub
Ucwf.compSub domUcwf  = compSub
Ucwf.id₀ domUcwf      = id₀
Ucwf.<>-zero domUcwf  = <>-zero
Ucwf.pCons domUcwf    = pCons
Ucwf.qCons domUcwf    = qCons
Ucwf.idExt domUcwf    = idExt
Ucwf.compExt domUcwf  = compExt
Ucwf.subCong domUcwf  = ∘-cong
Ucwf.<,>-cong domUcwf = <,>-cong
Ucwf.∘-cong domUcwf   = ∘-cong
