{-# OPTIONS --safe #-}

open import Base.Core
open import Scwf.DomainScwf.Appmap.Definition

open import Agda.Builtin.Nat

module Scwf.DomainScwf.ArrowStructure.lam.Lemmata
  (𝐴 𝐵 : Ty)
  {n : Nat}
  {Γ : Ctx n}
  (𝑡 : tAppmap (𝐴 :: Γ) [ 𝐵 ]) where

open import Base.FinFun
open import NbhSys.Definition
open import NbhSys.Lemmata
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Instance
open import Scwf.DomainScwf.Appmap.Valuation.Relation
open import Scwf.DomainScwf.ArrowStructure.lam.Relation 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.ConFinFun 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Definition 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Post 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Pre 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.Variables 𝐴 𝐵

open import Agda.Builtin.Equality

shrinkLam : ∀ {𝑥 con𝑓 con𝑓′} → 𝑓 ⊆ 𝑓′ →
            [ 𝑡 ] 𝑥 lam↦ ⟪ 𝐹 𝑓′ con𝑓′ ⟫ →
            [ 𝑡 ] 𝑥 lam↦ ⟪ 𝐹 𝑓 con𝑓 ⟫
shrinkLam {𝑓 = 𝑓} 𝑓⊆𝑓′ (lam↦-intro₂  _ p)
  = lam↦-intro₂ _ (λ xy∈𝑓 → p (𝑓⊆𝑓′ xy∈𝑓))

-- The first component of any pair in a FinFun 𝑓 is smaller
-- than pre 𝑓.
preBiggest : ∀ {x y 𝑓 preable𝑓} → (x , y) ∈ 𝑓 →
             [ 𝐴 ] x ⊑ pre 𝑓 preable𝑓
preBiggest {preable𝑓 = pre-nil} = xy∈∅-abs
preBiggest {preable𝑓 = pre-cons preable𝑓 conx′pre𝑓} here
  = NbhSys.⊑-⊔-fst 𝐴 conx′pre𝑓
preBiggest {preable𝑓 = pre-cons preable𝑓 conx′pre𝑓} (there xy∈𝑓)
  with (preBiggest {preable𝑓 = preable𝑓} xy∈𝑓)
... | x⊑pre𝑓 = ⊑-⊔-lemma₅ 𝐴 x⊑pre𝑓 conx′pre𝑓

↓closedLemma' : {𝑥 : Valuation Γ} → ∀ con𝑓 preable𝑓 →
                [ 𝑡 ] 𝑥 lam↦ ⟪ 𝐹 𝑓 con𝑓 ⟫ →
                ∀ x y → (x , y) ∈ 𝑓 →
                [ 𝑡 ] ⟪ pre 𝑓 preable𝑓 ,, 𝑥 ⟫ ↦ ⟪ y ⟫
↓closedLemma'  {𝑓 = (x ∷ 𝑓′)} {𝑥 = 𝑥} _ preable
  (lam↦-intro₂ _ p) x′ y′ x′y′∈𝑓
  = Appmap.↦-mono 𝑡 a𝑥⊑p𝑓𝑥 (p x′y′∈𝑓)
  where a⊑p𝑓 = preBiggest x′y′∈𝑓
        a𝑥⊑p𝑓𝑥 = ⊑ᵥ-cons (𝐴 :: Γ) a⊑p𝑓
                 (NbhSys.⊑-refl (ValNbhSys _))

↓closedLemma : {𝑥 : Valuation Γ} →
               ∀ con𝑓 preable𝑓 postable𝑓 →
               [ 𝑡 ] 𝑥 lam↦ ⟪ 𝐹 𝑓 con𝑓 ⟫ →
               [ 𝑡 ] ⟪ pre 𝑓 preable𝑓 ,, 𝑥 ⟫ ↦ ⟪ post 𝑓 postable𝑓 ⟫
↓closedLemma {𝑓 = ∅} _ _ _ _ = Appmap.↦-bottom 𝑡
↓closedLemma {𝑓 = ((x , y) ∷ 𝑓′)} {𝑥 = 𝑥}
  con𝑓 (pre-cons preable𝑓′ conxpre𝑓′)
  (post-cons postable𝑓′ conypost𝑓′) lam𝑡𝑥↦𝑓
  = Appmap.↦-↑directed 𝑡 𝑡pre𝑓'↦y 𝑡𝑓𝑥↦p𝑓′
    (con-tup _ con-nil)
  where 𝑓' = (x , y) ∷ 𝑓′
        𝑡pre𝑓'↦y = ↓closedLemma' _ (pre-cons preable𝑓′ conxpre𝑓′)
                  lam𝑡𝑥↦𝑓 x y here
        p𝑓′⊑p𝑓 = NbhSys.⊑-⊔-snd 𝐴 conxpre𝑓′
        p𝑓′𝑥⊑p𝑓𝑥 = ⊑ᵥ-cons (𝐴 :: Γ) p𝑓′⊑p𝑓
                  (NbhSys.⊑-refl (ValNbhSys _))
        𝑡p𝑓′𝑥↦p𝑓′ = ↓closedLemma (subsetIsCon con𝑓 ⊆-lemma₃)
                   preable𝑓′ postable𝑓′
                   (shrinkLam (λ 𝑦∈𝑓′ → there 𝑦∈𝑓′) lam𝑡𝑥↦𝑓)
        𝑡𝑓𝑥↦p𝑓′ = Appmap.↦-mono 𝑡 p𝑓′𝑥⊑p𝑓𝑥 𝑡p𝑓′𝑥↦p𝑓′

⊥⊔x≡x : ∀ x → ∀ {con⊥x} →
        ⊥ₑ ⊔ₑ x [ con⊥x ] ≡ x
⊥⊔x≡x ⊥ₑ = refl
⊥⊔x≡x (𝐹 𝑓 _) = refl

x⊔⊥≡x : ∀ x → ∀ {conx⊥} →
        x ⊔ₑ ⊥ₑ [ conx⊥ ] ≡ x
x⊔⊥≡x ⊥ₑ = refl
x⊔⊥≡x (𝐹 𝑓 _ ) = refl
