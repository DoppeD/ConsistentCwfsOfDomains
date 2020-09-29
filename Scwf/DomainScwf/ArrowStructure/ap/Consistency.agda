{-# OPTIONS --safe #-}

open import Base.Core
open import Base.Variables using (n)
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Instance
open import Scwf.DomainScwf.Appmap.Definition

module Scwf.DomainScwf.ArrowStructure.ap.Consistency
  {Γ : Ctx n}
  {𝐴 𝐵 : Ty}
  (𝑡 : tAppmap Γ [ ArrNbhSys 𝐴 𝐵 ])
  (𝑢 : tAppmap Γ [ 𝐴 ])
  where

open import Base.FinFun
open import NbhSys.Definition
open import NbhSys.Lemmata
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Instance
open import Scwf.DomainScwf.Appmap.Valuation.Relation
open import Scwf.DomainScwf.ArrowStructure.ap.Relation 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Definition 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.ConFinFun 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Post 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Pre 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Relation 𝐴 𝐵
{-
[ 𝑡 ] 𝑥 ↦ ⟪ 𝐹 𝑓 con𝑓 ⟫
[ 𝑢 ] 𝑥 ↦ ⟪ x ⟫
(𝐹 (< x , y > ∷ ∅)) ⊑ (𝐹 𝑓 con𝑓)

[ 𝑡 ] 𝑥′ ↦ ⟪ 𝐹 𝑓′ con𝑓′ ⟫
[ 𝑢 ] 𝑥′ ↦ ⟪ x′ ⟫
(𝐹 (< x′ , y′ > ∷ ∅)) ⊑ (𝐹 𝑓′ con𝑓′)

𝑥 and 𝑥′ are consistent.
⟪ x ⟫ and ⟪ x′ ⟫ are consistent.
𝑓 and 𝑓′ are consistent.

Take subset sub ⊆ 𝑓 such that pre sub ⊑ x and y ⊑ post sub.
Also subset sub′ ⊆ 𝑓′ such that pre sub′ ⊑ x′ and y′ ⊑ post sub′.
Their union is preable, since bounded by x ⊔ x′.
Hence postable, since 𝑓 and 𝑓′ are consistent (meaning 𝑓 ∪ 𝑓′ is).
-}

ap↦-con : ∀ {𝑥 𝑦 𝑥′ 𝑦′} → [ 𝑡 , 𝑢 ] 𝑥 ap↦ 𝑦 →
          [ 𝑡 , 𝑢 ] 𝑥′ ap↦ 𝑦′ → ValCon _ 𝑥 𝑥′ →
          ValCon _ 𝑦 𝑦′
ap↦-con {𝑦′ = ⟪ y' , ⟪⟫ ⟫} (ap↦-intro₁ y⊑⊥) ap𝑥′↦𝑦′ _
  = NbhSys.Con-⊔ (ValNbhSys [ 𝐵 ]) 𝑦⊑𝑦′ 𝑦′⊑𝑦′
  where 𝑦′⊑𝑦′ = NbhSys.⊑-refl (ValNbhSys _)
        y⊑y′ = NbhSys.⊑-trans 𝐵 y⊑⊥ (NbhSys.⊑-⊥ 𝐵)
        𝑦⊑𝑦′ = ⊑ᵥ-cons _ _ _ y⊑y′ ⊑ᵥ-nil
ap↦-con (ap↦-intro₂ _ _ _ _ _ _ _ _) (ap↦-intro₁ y′⊑⊥) _
  = NbhSys.Con-⊔ (ValNbhSys [ 𝐵 ]) 𝑦⊑𝑦 𝑦′⊑𝑦
  where 𝑦⊑𝑦 = NbhSys.⊑-refl (ValNbhSys _)
        y′⊑y = NbhSys.⊑-trans 𝐵 y′⊑⊥ (NbhSys.⊑-⊥ 𝐵)
        𝑦′⊑𝑦 = ⊑ᵥ-cons _ _ _ y′⊑y ⊑ᵥ-nil
ap↦-con (ap↦-intro₂ x y 𝑓 con𝑓 conxy 𝑡𝑥↦𝑓 𝑢𝑥↦x xy⊑𝑓)
  (ap↦-intro₂ x′ y′ 𝑓′ con𝑓′ conx′y′ 𝑡𝑥′↦𝑓′ 𝑢𝑥′↦x′ x′y′⊑𝑓′)
  con𝑥𝑥′
  = {!!}
