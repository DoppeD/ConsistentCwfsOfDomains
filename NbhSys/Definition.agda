{-# OPTIONS --safe #-}

module NbhSys.Definition where

record NbhSys : Set₁ where
  field
    Nbh : Set
    _⊑_ : Nbh → Nbh → Set
    Con : Nbh → Nbh → Set
    _⊔_[_] : (x y : Nbh) → Con x y → Nbh
    ⊥   : Nbh

    Con-⊔ : ∀ {x y z} → x ⊑ z → y ⊑ z → Con x y

    ⊑-refl  : ∀ {x} → x ⊑ x
    ⊑-trans : ∀ {x y z} → x ⊑ y → y ⊑ z → x ⊑ z
    ⊑-⊥     : ∀ {x} → ⊥ ⊑ x
    ⊑-⊔     : ∀ {x y z} → y ⊑ x → z ⊑ x → (con : Con y z) →
              (y ⊔ z [ con ]) ⊑ x
    ⊑-⊔-fst : ∀ {x y} → (con : Con x y) → x ⊑ (x ⊔ y [ con ])
    ⊑-⊔-snd : ∀ {x y} → (con : Con x y) → y ⊑ (x ⊔ y [ con ])


-- Some simplifying syntax.
[_]_⊑_ : (𝒟 : NbhSys) → (x y : NbhSys.Nbh 𝒟) → Set
[ A ] x ⊑ y = NbhSys._⊑_ A x y

[_]_⊔_[_] : (𝒟 : NbhSys) → (x y : NbhSys.Nbh 𝒟) → NbhSys.Con 𝒟 x y →
            NbhSys.Nbh 𝒟
[ A ] x ⊔ y [ con ] = NbhSys._⊔_[_] A x y con
