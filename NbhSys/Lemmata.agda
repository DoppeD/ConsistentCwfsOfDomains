{-# OPTIONS --safe #-}

open import NbhSys.Definition

module NbhSys.Lemmata (𝒟 : NbhSys) where

private
  variable
    x y z w : NbhSys.Nbh 𝒟

conRefl : ∀ {x} → NbhSys.Con 𝒟 x x
conRefl = NbhSys.Con-⊔ 𝒟 (NbhSys.⊑-refl 𝒟) (NbhSys.⊑-refl 𝒟)

⊑-⊔-lemma₁ : (con : NbhSys.Con 𝒟 y z) → [ 𝒟 ] ([ 𝒟 ] y ⊔ z [ con ]) ⊑ x →
             [ 𝒟 ] y ⊑ x
⊑-⊔-lemma₁ con y⊔z⊑x =
  NbhSys.⊑-trans 𝒟 (NbhSys.⊑-⊔-fst 𝒟 con) y⊔z⊑x

⊑-⊔-lemma₂ : (con : NbhSys.Con 𝒟 y z) → [ 𝒟 ] ([ 𝒟 ] y ⊔ z [ con ]) ⊑ x →
             [ 𝒟 ] z ⊑ x
⊑-⊔-lemma₂ con y⊔z⊑x =
  NbhSys.⊑-trans 𝒟 (NbhSys.⊑-⊔-snd 𝒟 con) y⊔z⊑x

⊑-⊔-lemma₃ : (conxy : NbhSys.Con 𝒟 x y) → (conzw : NbhSys.Con 𝒟 z w) →
             [ 𝒟 ] x ⊑ z → [ 𝒟 ] y ⊑ w →
             [ 𝒟 ] ([ 𝒟 ] x ⊔ y [ conxy ]) ⊑ ([ 𝒟 ] z ⊔ w [ conzw ])
⊑-⊔-lemma₃ conxy conzw x⊑z y⊑w = NbhSys.⊑-⊔ 𝒟 x⊑z⊔w y⊑z⊔w conxy
  where x⊑z⊔w = NbhSys.⊑-trans 𝒟 x⊑z (NbhSys.⊑-⊔-fst 𝒟 conzw)
        y⊑z⊔w = NbhSys.⊑-trans 𝒟 y⊑w (NbhSys.⊑-⊔-snd 𝒟 conzw)

⊑-⊔-lemma₄ : [ 𝒟 ] x ⊑ y → (con : NbhSys.Con 𝒟 y z) →
             [ 𝒟 ] x ⊑ ([ 𝒟 ] y ⊔ z [ con ])
⊑-⊔-lemma₄ x⊑y con = NbhSys.⊑-trans 𝒟 x⊑y (NbhSys.⊑-⊔-fst 𝒟 con)

⊑-⊔-lemma₅ : [ 𝒟 ] x ⊑ z → (con : NbhSys.Con 𝒟 y z) →
             [ 𝒟 ] x ⊑ ([ 𝒟 ] y ⊔ z [ con ])
⊑-⊔-lemma₅ x⊑z con = NbhSys.⊑-trans 𝒟 x⊑z (NbhSys.⊑-⊔-snd 𝒟 con)
{-
⊔-ass₁ : [ 𝒟 ] ([ 𝒟 ] x ⊔ ([ 𝒟 ] y ⊔ z)) ⊑ w →
         [ 𝒟 ] [ 𝒟 ] ([ 𝒟 ] x ⊔ y) ⊔ z ⊑ w
⊔-ass₁ p = NbhSys.⊑-⊔ 𝒟
           (NbhSys.⊑-⊔ 𝒟 (⊑-⊔-lemma₁ p)
           (⊑-⊔-lemma₁ (⊑-⊔-lemma₂ p)))
           (⊑-⊔-lemma₂ (⊑-⊔-lemma₂ p))

⊔-ass₂ : [ 𝒟 ] [ 𝒟 ] ([ 𝒟 ] x ⊔ y) ⊔ z ⊑ w →
         [ 𝒟 ] ([ 𝒟 ] x ⊔ ([ 𝒟 ] y ⊔ z)) ⊑ w
⊔-ass₂ p = NbhSys.⊑-⊔ 𝒟
           (⊑-⊔-lemma₁ (⊑-⊔-lemma₁ p))
           (NbhSys.⊑-⊔ 𝒟 (⊑-⊔-lemma₂
           (⊑-⊔-lemma₁ p)) (⊑-⊔-lemma₂ p))
-}
