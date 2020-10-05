{-# OPTIONS --safe #-}

open import Base.Core
open import Base.Variables using (n)
open import Scwf.DomainScwf.Appmap.Definition

module Scwf.DomainScwf.ArrowStructure.lam.Consistency
  {𝐴 𝐵 : Ty}
  {Γ : Ctx n}
  (𝑡 : Term (𝐴 :: Γ) 𝐵) where

open import Base.FinFun
open import NbhSys.Definition
open import Scwf.DomainScwf.Appmap.Valuation.AxiomProofs
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Lemmata
open import Scwf.DomainScwf.Appmap.Valuation.Instance
open import Scwf.DomainScwf.Appmap.Valuation.Relation
open import Scwf.DomainScwf.ArrowStructure.lam.Relation 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.ConFinFun 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Definition 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Instance
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Post 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Pre 𝐴 𝐵

lamPrePost : ∀ {x y 𝑓 𝑥} →
             ∀ preable𝑓 conxpre𝑓 postable𝑓 conypost𝑓 →
             [ 𝑡 ] ⟪ x ,, 𝑥 ⟫ ↦ y →
             [ 𝑡 ] ⟪ pre 𝑓 preable𝑓 ,, 𝑥 ⟫ ↦ (post 𝑓 postable𝑓) →
             [ 𝑡 ] ⟪ pre ((x , y) ∷ 𝑓)
                     (pre-cons preable𝑓 conxpre𝑓) ,, 𝑥 ⟫ ↦
                   (post ((x , y) ∷ 𝑓)
                     (post-cons postable𝑓 conypost𝑓))
lamPrePost {x} {y} {𝑓} {𝑥}
  preable𝑓 conxpre𝑓 postable𝑓 conypost𝑓 𝑡x𝑥↦y 𝑡x𝑥↦post𝑓
  = Appmap.↦-↑directed 𝑡 𝑡x⊔pre𝑓𝑥↦y 𝑡x⊔pre𝑓𝑥↦post𝑓 conypost𝑓
  where x𝑥⊑prexy𝑓𝑥 = ⊑ᵥ-cons _ (NbhSys.⊑-⊔-fst 𝐴 conxpre𝑓)
                     ⊑ᵥ-refl
        𝑡x⊔pre𝑓𝑥↦y = Appmap.↦-mono 𝑡 x𝑥⊑prexy𝑓𝑥 𝑡x𝑥↦y
        pre𝑓𝑥⊑prexy𝑓𝑥 = ⊑ᵥ-cons _ (NbhSys.⊑-⊔-snd 𝐴 conxpre𝑓)
                        ⊑ᵥ-refl
        𝑡x⊔pre𝑓𝑥↦post𝑓 = Appmap.↦-mono 𝑡 pre𝑓𝑥⊑prexy𝑓𝑥 𝑡x𝑥↦post𝑓

record ⊑ₑ-proof₄ (𝑓 : NbhFinFun 𝐴 𝐵) (preable𝑓 : Preable 𝑓)
                 (𝑥 : Valuation Γ) : Set where
  field
    postable𝑓 : Postable 𝑓
    𝑡pre↦post : [ 𝑡 ] ⟪ pre 𝑓 preable𝑓 ,, 𝑥 ⟫ ↦ (post 𝑓 postable𝑓)

lam↦-con'' : ∀ {𝑓 𝑥} →
             (∀ {x y} → (x , y) ∈ 𝑓 → [ 𝑡 ] ⟪ x ,, 𝑥 ⟫ ↦ y) →
             (preable𝑓 : Preable 𝑓) →
             ⊑ₑ-proof₄ 𝑓 preable𝑓 𝑥
lam↦-con'' _ pre-nil
  = record { postable𝑓 = post-nil
           ; 𝑡pre↦post = Appmap.↦-bottom 𝑡
           }
lam↦-con'' {𝑓 = (x , y) ∷ 𝑓}
  p (pre-cons preable𝑓 conxpre𝑓)
  = record { postable𝑓 = postablexy𝑓
           ; 𝑡pre↦post = lamPrePost preable𝑓 _ recpostable𝑓 _
                         (p here) rec𝑡pre↦post
           }
  where rec = lam↦-con'' (λ x′y′∈𝑓 → p (there x′y′∈𝑓)) preable𝑓
        recpostable𝑓 = ⊑ₑ-proof₄.postable𝑓 rec
        rec𝑡pre↦post = ⊑ₑ-proof₄.𝑡pre↦post rec
        conypost𝑓 = Appmap.↦-con 𝑡 (p here) rec𝑡pre↦post
                    (con-tup conxpre𝑓 valConRefl)
        postablexy𝑓 = post-cons recpostable𝑓 conypost𝑓

lam↦-con' : ∀ {𝑓 𝑓′ 𝑥 𝑥′ con𝑥𝑥′} →
            (∀ {x y} → (x , y) ∈ 𝑓 → [ 𝑡 ] ⟪ x ,, 𝑥 ⟫ ↦ y) →
            (∀ {x y} → (x , y) ∈ 𝑓′ → [ 𝑡 ] ⟪ x ,, 𝑥′ ⟫ ↦ y) →
            ∀ {x y} → (x , y) ∈ (𝑓 ∪ 𝑓′) →
            [ 𝑡 ] ⟪ x ,, 𝑥 ⊔ᵥ 𝑥′ [ con𝑥𝑥′ ] ⟫ ↦ y
lam↦-con' {𝑓} {con𝑥𝑥′ = con𝑥𝑥′} p₁ p₂ xy∈∪
  with (∪-lemma₂ {𝑓 = 𝑓} xy∈∪)
... | inl xy∈𝑓 = Appmap.↦-mono 𝑡 x𝑥⊑x𝑥⊔𝑥′ (p₁ xy∈𝑓)
  where 𝑥⊑𝑥⊔𝑥′ = NbhSys.⊑-⊔-fst (ValNbhSys Γ) con𝑥𝑥′
        x𝑥⊑x𝑥⊔𝑥′ = ⊑ᵥ-cons _ (NbhSys.⊑-refl 𝐴) 𝑥⊑𝑥⊔𝑥′
... | inr xy∈𝑓′ = Appmap.↦-mono 𝑡 x𝑥′⊑x𝑥⊔𝑥′ (p₂ xy∈𝑓′)
  where 𝑥′⊑𝑥⊔𝑥′ = NbhSys.⊑-⊔-snd (ValNbhSys Γ) con𝑥𝑥′
        x𝑥′⊑x𝑥⊔𝑥′ = ⊑ᵥ-cons _ (NbhSys.⊑-refl 𝐴) 𝑥′⊑𝑥⊔𝑥′

from⊑ₑ-proof₄ : ∀ {𝑓 𝑓′ 𝑥 𝑥′ sub} →
               (∀ {x y} → (x , y) ∈ 𝑓 → [ 𝑡 ] ⟪ x ,, 𝑥 ⟫ ↦ y) →
               (∀ {x y} → (x , y) ∈ 𝑓′ → [ 𝑡 ] ⟪ x ,, 𝑥′ ⟫ ↦ y) →
               ValCon _ 𝑥 𝑥′ →
               sub ⊆ (𝑓 ∪ 𝑓′) → Preable sub →
               Postable sub
from⊑ₑ-proof₄ p₁ p₂ con𝑥𝑥′ sub⊆∪ preablesub
  = ⊑ₑ-proof₄.postable𝑓 (lam↦-con'' (λ xy∈sub →
    lam↦-con' {con𝑥𝑥′ = con𝑥𝑥′} p₁ p₂ (sub⊆∪ xy∈sub)) preablesub)

lam↦-con : ∀ {𝑥 y 𝑥′ y′} → [ 𝑡 ] 𝑥 lam↦ y →
           [ 𝑡 ] 𝑥′ lam↦ y′ → ValCon _ 𝑥 𝑥′ →
           NbhSys.Con (𝐴 ⇒ 𝐵) y y′
lam↦-con lam↦-intro₁ lam↦-intro₁ _
  = conₑ-⊥₂
lam↦-con lam↦-intro₁ (lam↦-intro₂ _ _) _
  = conₑ-⊥₂
lam↦-con (lam↦-intro₂ _ _) lam↦-intro₁ _
  = conₑ-⊥₁
lam↦-con (lam↦-intro₂ con𝑓 p₁)
  (lam↦-intro₂ con𝑓′ p₂) con𝑥𝑥′
  = con-∪ _ _ con𝑓∪𝑓′
  where con𝑓∪𝑓′ = cff (from⊑ₑ-proof₄ p₁ p₂ con𝑥𝑥′)
