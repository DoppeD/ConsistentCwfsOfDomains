{-# OPTIONS --safe #-}

open import Base.Core
open import Base.Variables
open import Scwf.DomainScwf.Appmap.Definition

module Scwf.DomainScwf.Comprehension.Morphism.AxiomProofs
  (γ : tAppmap Δ Γ) (𝑡 : tAppmap Δ [ 𝐴 ]) where

open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Relation
open import Scwf.DomainScwf.Comprehension.Morphism.Relation

⟨⟩↦-mono : ∀ {𝑥 𝑦 𝑧} → ⊑ᵥ Δ 𝑥 𝑦 → [⟨ γ , 𝑡 ⟩] 𝑥 ↦ 𝑧 →
           [⟨ γ , 𝑡 ⟩] 𝑦 ↦ 𝑧
⟨⟩↦-mono {𝑥 = 𝑥} {𝑦} {⟪ z , 𝑧 ⟫} 𝑥⊑𝑦 (⟨⟩↦-intro _ _ γ𝑥↦𝑧 𝑡𝑥↦z) =
  ⟨⟩↦-intro 𝑦 ⟪ z , 𝑧 ⟫ (Appmap.↦-mono γ 𝑥⊑𝑦 γ𝑥↦𝑧)
  (Appmap.↦-mono 𝑡 𝑥⊑𝑦 𝑡𝑥↦z)

⟨⟩↦-bottom : ∀ {𝑥} → [⟨ γ , 𝑡 ⟩] 𝑥 ↦ ⊥ᵥ
⟨⟩↦-bottom {𝑥} = ⟨⟩↦-intro 𝑥 ⊥ᵥ (Appmap.↦-bottom γ)
                 (Appmap.↦-bottom 𝑡)

⟨⟩↦-↓closed : ∀ {𝑥 𝑦 𝑧} → ⊑ᵥ (𝐴 :: Γ) 𝑦 𝑧 →
              [⟨ γ , 𝑡 ⟩] 𝑥 ↦ 𝑧 → [⟨ γ , 𝑡 ⟩] 𝑥 ↦ 𝑦
⟨⟩↦-↓closed {𝑥 = 𝑥} {⟪ y , 𝑦 ⟫} {⟪ z , 𝑧 ⟫}
  (⊑ᵥ-cons _ _ _ y⊑z 𝑦⊑𝑧) (⟨⟩↦-intro _ _ γ𝑥↦𝑧 𝑡𝑥↦z)
  = ⟨⟩↦-intro 𝑥 ⟪ y , 𝑦 ⟫ γ𝑥↦𝑦 𝑡𝑥↦y
    where γ𝑥↦𝑦 = Appmap.↦-↓closed γ 𝑦⊑𝑧 γ𝑥↦𝑧
          tup-y⊑z = (⊑ᵥ-cons [ 𝐴 ] ⟪ y ⟫ ⟪ z ⟫ y⊑z ⊑ᵥ-nil)
          𝑡𝑥↦y = Appmap.↦-↓closed 𝑡 tup-y⊑z 𝑡𝑥↦z

⟨⟩↦-↑directed : ∀ {𝑥 𝑦 𝑧} → [⟨ γ , 𝑡 ⟩] 𝑥 ↦ 𝑦 →
                [⟨ γ , 𝑡 ⟩] 𝑥 ↦ 𝑧 →
                (con𝑦𝑧 : ValCon _ 𝑦 𝑧) →
                [⟨ γ , 𝑡 ⟩] 𝑥 ↦ (𝑦 ⊔ᵥ 𝑧 [ con𝑦𝑧 ])
⟨⟩↦-↑directed {𝑥 = 𝑥} {⟪ y , 𝑦 ⟫} {⟪ z , 𝑧 ⟫}
  (⟨⟩↦-intro _ _ γ𝑥↦𝑦 𝑡𝑥↦y) (⟨⟩↦-intro _ _ γ𝑥↦𝑧 𝑡𝑥↦z)
  (con-tup conyz con𝑦𝑧)
  = ⟨⟩↦-intro 𝑥 (⟪ y , 𝑦 ⟫ ⊔ᵥ ⟪ z , 𝑧 ⟫ [ _ ]) γ𝑥↦y⊔𝑧 𝑡𝑥↦y⊔z
    where γ𝑥↦y⊔𝑧 = Appmap.↦-↑directed γ γ𝑥↦𝑦 γ𝑥↦𝑧 con𝑦𝑧
          𝑡𝑥↦y⊔z = Appmap.↦-↑directed 𝑡 𝑡𝑥↦y 𝑡𝑥↦z (toValCon conyz)

⟨⟩↦-con : ∀ {𝑥 𝑦 𝑥′ 𝑦′} → [⟨ γ , 𝑡 ⟩] 𝑥 ↦ 𝑦 →
          [⟨ γ , 𝑡 ⟩] 𝑥′ ↦ 𝑦′ → ValCon _ 𝑥 𝑥′ →
          ValCon _ 𝑦 𝑦′
⟨⟩↦-con {𝑦 = ⟪ y , 𝑦 ⟫} {𝑦′ = ⟪ y′ , 𝑦′ ⟫}
  (⟨⟩↦-intro _ _ γ𝑥↦𝑦 𝑡𝑥↦y) (⟨⟩↦-intro _ _ γ𝑥′↦𝑦′ 𝑡𝑥′↦y′) con𝑥𝑥′
  = con-tup conyy′ con𝑦𝑦′
  where conyy′ = fromValCon (Appmap.↦-con 𝑡 𝑡𝑥↦y 𝑡𝑥′↦y′ con𝑥𝑥′)
        con𝑦𝑦′ = Appmap.↦-con γ γ𝑥↦𝑦 γ𝑥′↦𝑦′ con𝑥𝑥′
