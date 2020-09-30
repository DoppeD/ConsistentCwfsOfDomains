{-# OPTIONS --safe #-}

module Scwf.DomainScwf.Appmap.Identity.AxiomProofs where

open import Base.Core
open import Base.Variables
open import NbhSys.Definition
open import Scwf.DomainScwf.Appmap.Valuation.AxiomProofs
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Instance
open import Scwf.DomainScwf.Appmap.Valuation.Relation
open import Scwf.DomainScwf.Appmap.Identity.Relation

private
  variable
    𝑥 𝑦 𝑧 𝑤 : Valuation Γ

id↦-mono : ⊑ᵥ Γ 𝑥 𝑦 → 𝑥 id↦ 𝑧 → 𝑦 id↦ 𝑧
id↦-mono {Γ = Γ} {𝑦 = 𝑦} {𝑧} 𝑥⊑𝑦 (id↦-intro 𝑧⊑𝑥)
  = id↦-intro (NbhSys.⊑-trans (ValNbhSys _) 𝑧⊑𝑥 𝑥⊑𝑦)

id↦-bottom : 𝑥 id↦ ⊥ᵥ
id↦-bottom {𝑥 = 𝑥}
  = id↦-intro (NbhSys.⊑-⊥ (ValNbhSys _))

id↦-↓closed : ⊑ᵥ Γ 𝑦 𝑧 → 𝑥 id↦ 𝑧 → 𝑥 id↦ 𝑦
id↦-↓closed {𝑦 = 𝑦} {𝑥 = 𝑥} 𝑦⊑𝑧 (id↦-intro 𝑧⊑𝑥)
  = id↦-intro (NbhSys.⊑-trans (ValNbhSys _) 𝑦⊑𝑧 𝑧⊑𝑥)

id↦-↑directed : 𝑥 id↦ 𝑦 → 𝑥 id↦ 𝑧 → (con : ValCon Γ 𝑦 𝑧) →
                𝑥 id↦ (𝑦 ⊔ᵥ 𝑧 [ con ])
id↦-↑directed {𝑥 = 𝑥} {𝑦} {𝑧} (id↦-intro 𝑦⊑𝑥)
  (id↦-intro 𝑧⊑𝑥) con
  = id↦-intro (NbhSys.⊑-⊔ (ValNbhSys _) 𝑦⊑𝑥 𝑧⊑𝑥 con)

id↦-con : 𝑥 id↦ 𝑧 → 𝑦 id↦ 𝑤 → ValCon Γ 𝑥 𝑦 → ValCon Γ 𝑧 𝑤
id↦-con (id↦-intro 𝑧⊑𝑥) (id↦-intro 𝑤⊑𝑦) con
  = Con-⊔ᵥ 𝑧⊑𝑥⊔𝑦 𝑤⊑𝑥⊔𝑦
  where 𝑧⊑𝑥⊔𝑦 = ⊑ᵥ-trans 𝑧⊑𝑥 (⊑ᵥ-⊔-fst con)
        𝑤⊑𝑥⊔𝑦 = ⊑ᵥ-trans 𝑤⊑𝑦 (⊑ᵥ-⊔-snd con)
