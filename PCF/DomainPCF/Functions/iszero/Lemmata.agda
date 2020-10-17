{-# OPTIONS --safe #-}

module PCF.DomainPCF.Functions.iszero.Lemmata where

open import Base.Core
open import Base.FinFun
open import NbhSys.Definition
open import NbhSys.Lemmata
open import PCF.DomainPCF.Functions.iszero.Relation
open import PCF.DomainPCF.Nat.NbhSys.Instance
open import PCF.DomainPCF.Bool.NbhSys.Instance
open import PCF.DomainPCF.Bool.NbhSys.Relation
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Post Nat Bool
open import Scwf.DomainScwf.ArrowStructure.NbhSys.Pre Nat Bool

iszeroLemma : ∀ {sub preable postable} →
              (∀ {x y} → (x , y) ∈ sub → iszeroprop x y) →
              iszeroprop (pre sub preable) (post sub postable)
iszeroLemma {∅} _ = izprop₁ ⊑b-intro₁
iszeroLemma {(x , y) ∷ sub} {pre-cons preable conxpresub}
  {post-cons postable conypostsub} p
  with (p here) | iszeroLemma {preable = preable} {postable}
  (λ xy∈sub → p (there xy∈sub))
... | _ | izprop₂ 0⊑pre t⊑post
  = izprop₂ 0⊑x⊔pre t⊑y⊔post
  where 0⊑x⊔pre = ⊑-⊔-lemma₅ Nat 0⊑pre conxpresub
        t⊑y⊔post = ⊑-⊔-lemma₅ Bool t⊑post conypostsub
... | _ | izprop₃ s⊥⊑pre f⊑post
  = izprop₃ s⊥⊑x⊔pre f⊑y⊔post
  where s⊥⊑x⊔pre = ⊑-⊔-lemma₅ Nat s⊥⊑pre conxpresub
        f⊑y⊔post = ⊑-⊔-lemma₅ Bool f⊑post conypostsub
... | izprop₁ y⊑⊥ | izprop₁ post⊑⊥
  = izprop₁ (NbhSys.⊑-⊔ Bool y⊑⊥ post⊑⊥ conypostsub)
... | izprop₂ 0⊑x t⊑y | izprop₁ _
  = izprop₂ 0⊑x⊔pre t⊑y⊔post
  where 0⊑x⊔pre = ⊑-⊔-lemma₄ Nat 0⊑x conxpresub
        t⊑y⊔post = ⊑-⊔-lemma₄ Bool t⊑y conypostsub
... | izprop₃ s⊥⊑x f⊑y | izprop₁ _
  = izprop₃ s⊥⊑x⊔pre f⊑y⊔post
  where s⊥⊑x⊔pre = ⊑-⊔-lemma₄ Nat s⊥⊑x conxpresub
        f⊑y⊔post = ⊑-⊔-lemma₄ Bool f⊑y conypostsub
