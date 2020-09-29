{-# OPTIONS --safe #-}

open import Base.Core
open import Base.Variables using (n)
open import Scwf.DomainScwf.Appmap.Definition

module Scwf.DomainScwf.ArrowStructure.lam.Consistency
  {𝐴 𝐵 : Ty}
  {Γ : Ctx n}
  (𝑡 : tAppmap (𝐴 :: Γ) [ 𝐵 ]) where

open import Base.FinFun
open import NbhSys.Definition
open import Scwf.DomainScwf.Appmap.Valuation.AxiomProofs
open import Scwf.DomainScwf.Appmap.Valuation.Definition
open import Scwf.DomainScwf.Appmap.Valuation.Lemmata
open import Scwf.DomainScwf.Appmap.Valuation.Instance
open import Scwf.DomainScwf.Appmap.Valuation.Relation
open import Scwf.DomainScwf.ArrowStructure.lam.Relation 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Definition 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Post 𝐴 𝐵
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Pre 𝐴 𝐵

lamPrePost : ∀ {x y 𝑓 𝑥} →
             ∀ preable𝑓 conxpre𝑓 postable𝑓 conypost𝑓 →
             [ 𝑡 ] ⟪ x , 𝑥 ⟫ ↦ ⟪ y ⟫ →
             [ 𝑡 ] ⟪ pre 𝑓 preable𝑓 , 𝑥 ⟫ ↦ ⟪ post 𝑓 postable𝑓 ⟫ →
             [ 𝑡 ] ⟪ pre (< x , y > ∷ 𝑓)
                     (pre-cons preable𝑓 conxpre𝑓) , 𝑥 ⟫ ↦
                   ⟪ post (< x , y > ∷ 𝑓)
                     (post-cons postable𝑓 conypost𝑓) ⟫
lamPrePost {x} {y} {𝑥 = 𝑥} preable𝑓 conxpre𝑓 postable𝑓 conypost𝑓 𝑡x𝑥↦y 𝑡x𝑥↦post𝑓
  = Appmap.↦-mono 𝑡 x𝑥⊑pre𝑓𝑥 𝑡x𝑥↦postxy𝑓
  where x𝑥⊑pre𝑓𝑥 = ⊑ᵥ-cons _ ⟪ x , 𝑥 ⟫ _ (NbhSys.⊑-⊔-fst 𝐴 conxpre𝑓)
                   ⊑ᵥ-refl
        𝑡x𝑥↦postxy𝑓 = Appmap.↦-↑directed 𝑡 𝑡x𝑥↦y {!!}
                      (toValCon conypost𝑓)
{-
lamPrePost {x} {y} {𝑥 = 𝑥}
  (pre-cons a conypre𝑓) postable𝑓 conypost𝑓 𝑡x𝑥↦y 𝑡x𝑥↦post𝑓
  = Appmap.↦-mono 𝑡 x𝑥⊑pre𝑓𝑥 𝑡x𝑥↦postxy𝑓
  where x𝑥⊑pre𝑓𝑥 = ⊑ᵥ-cons _ ⟪ x , 𝑥 ⟫ _ (NbhSys.⊑-⊔-fst 𝐴 conypre𝑓)
                   ⊑ᵥ-refl
        𝑡x𝑥↦postxy𝑓 = Appmap.↦-↑directed 𝑡 𝑡x𝑥↦y ?
                      (toValCon conypost𝑓)
-}

record ⊑ₑ-proof₄ (𝑓 : NbhFinFun 𝐴 𝐵) (preable𝑓 : Preable 𝑓)
                 (𝑥 : Valuation Γ) : Set where
  field
    postable𝑓 : Postable 𝑓
    𝑡pre↦post : [ 𝑡 ] ⟪ pre 𝑓 preable𝑓 , 𝑥 ⟫ ↦ ⟪ post 𝑓 postable𝑓 ⟫

lam↦-con'' : ∀ {𝑓 𝑥} →
             (∀ x y → < x , y > ∈ 𝑓 → [ 𝑡 ] ⟪ x , 𝑥 ⟫ ↦ ⟪ y ⟫) →
             (preable𝑓 : Preable 𝑓) →
             ⊑ₑ-proof₄ 𝑓 preable𝑓 𝑥
lam↦-con'' _ pre-nil
  = record { postable𝑓 = post-nil
           ; 𝑡pre↦post = Appmap.↦-bottom 𝑡
           }
lam↦-con'' {𝑓 = < x , y > ∷ 𝑓}
  p (pre-cons preable𝑓 conxpre𝑓)
  = record { postable𝑓 = postablexy𝑓
           ; 𝑡pre↦post = lamPrePost preable𝑓 _ recpostable𝑓 _ (p _ _ here) rec𝑡pre↦post
           }
  where rec = lam↦-con'' (λ x′ y′ x′y′∈𝑓 → p x′ y′
              (there x′y′∈𝑓)) preable𝑓
        recpostable𝑓 = ⊑ₑ-proof₄.postable𝑓 rec
        rec𝑡pre↦post = ⊑ₑ-proof₄.𝑡pre↦post rec
        conypost𝑓 = fromValCon (Appmap.↦-con 𝑡
                      (p x y here) rec𝑡pre↦post
                      (con-tup _ _ conxpre𝑓 _ _ valConRefl))
        postablexy𝑓 = post-cons recpostable𝑓 conypost𝑓

lam↦-con' : ∀ {𝑓 𝑓′ 𝑥 𝑥′ con𝑥𝑥′} →
            (∀ x y → < x , y > ∈ 𝑓 → [ 𝑡 ] ⟪ x , 𝑥 ⟫ ↦ ⟪ y ⟫) →
            (∀ x y → < x , y > ∈ 𝑓′ → [ 𝑡 ] ⟪ x , 𝑥′ ⟫ ↦ ⟪ y ⟫) →
            ∀ x y → < x , y > ∈ (𝑓 ∪ 𝑓′) →
            [ 𝑡 ] ⟪ x , [ ValNbhSys Γ ] 𝑥 ⊔ 𝑥′ [ con𝑥𝑥′ ] ⟫ ↦ ⟪ y ⟫
lam↦-con' {𝑓} {con𝑥𝑥′ = con𝑥𝑥′} p₁ p₂ x y xy∈∪
  with (∪-lemma₂ {𝑓 = 𝑓} < x , y > xy∈∪)
... | inl xy∈𝑓 = Appmap.↦-mono 𝑡 x𝑥⊑x𝑥⊔𝑥′ (p₁ x y xy∈𝑓)
  where 𝑥⊑𝑥⊔𝑥′ = NbhSys.⊑-⊔-fst (ValNbhSys Γ) con𝑥𝑥′
        x𝑥⊑x𝑥⊔𝑥′ = ⊑ᵥ-cons _ _ _ (NbhSys.⊑-refl 𝐴) 𝑥⊑𝑥⊔𝑥′
... | inr xy∈𝑓′ = Appmap.↦-mono 𝑡 x𝑥′⊑x𝑥⊔𝑥′ (p₂ x y xy∈𝑓′)
  where 𝑥′⊑𝑥⊔𝑥′ = NbhSys.⊑-⊔-snd (ValNbhSys Γ) con𝑥𝑥′
        x𝑥′⊑x𝑥⊔𝑥′ = ⊑ᵥ-cons _ _ _ (NbhSys.⊑-refl 𝐴) 𝑥′⊑𝑥⊔𝑥′

lam↦-con : ∀ {𝑥 𝑦 𝑥′ 𝑦′} → [ 𝑡 ] 𝑥 lam↦ 𝑦 →
           [ 𝑡 ] 𝑥′ lam↦ 𝑦′ → ValCon _ 𝑥 𝑥′ →
           ValCon _ 𝑦 𝑦′
lam↦-con lam↦-intro₁ lam↦-intro₁ _
  = toValCon conₑ-⊥₂
lam↦-con lam↦-intro₁ (lam↦-intro₂ _ _ _ _) _
  = toValCon conₑ-⊥₂
lam↦-con (lam↦-intro₂ _ _ _ _) lam↦-intro₁ _
  = toValCon conₑ-⊥₁
lam↦-con (lam↦-intro₂ _ 𝑓 con𝑓 p₁) (lam↦-intro₂ _ 𝑓′ con𝑓′ p₂)
  con𝑥𝑥′
  = {!⊑ₑ-proof₄!}
