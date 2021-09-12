{-# OPTIONS --safe #-}

module Cwf.DomainCwf.UniType.ConsistencyLemmata where

open import Base.Core
open import Base.FinFun
open import Cwf.DomainCwf.UniType.Consistency
open import Cwf.DomainCwf.UniType.Definition

open import Data.Nat.Induction

conLemma₁ : ∀ {u v p} → con' (u ⊔ v) p → con u
conLemma₁ {⊥} _ = *
conLemma₁ {0ᵤ} _ = *
conLemma₁ {s u} {⊥} {acc rs} conuv = wfIrrelevant {u} conuv
conLemma₁ {s u} {s v} {acc rs} conuv
  = wfIrrelevant {u} (conLemma₁ {u} conuv)
conLemma₁ {ℕ} _ = *
conLemma₁ {F f} {⊥} {acc rs} (conPairsf , conElemsf)
  = (λ uv∈f u′v′∈f → wfIrrelevantPairs uv∈f u′v′∈f (conPairsf uv∈f u′v′∈f))
  , λ uv∈f → wfIrrelevantElems uv∈f (conElemsf uv∈f)
conLemma₁ {F f} {F g} {acc rs} (conPairs , conElems)
  = (λ uv∈f u′v′∈f → wfIrrelevantPairs uv∈f u′v′∈f (conPairs (∪-lemma₃ uv∈f) (∪-lemma₃ u′v′∈f)))
  , λ uv∈f → wfIrrelevantElems uv∈f (conElems (∪-lemma₃ uv∈f))
conLemma₁ {refl u} {⊥} {acc rs} conuv = wfIrrelevant {u} conuv
conLemma₁ {refl u} {refl v} {acc rs} conuv
  = wfIrrelevant {u} (conLemma₁ {u} conuv)
conLemma₁ {I U u u′} {⊥} {acc rs} (conU , (conu , conu′))
  = (wfIrrelevant {U} conU) , ((wfIrrelevant {u} conu) , (wfIrrelevant {u′} conu′))
conLemma₁ {I U u u′} {I V v v′} {acc rs} (conUV , (conuv , conu′v′))
  = wfIrrelevant {U} (conLemma₁ {U} conUV)
  , (wfIrrelevant {u} (conLemma₁ {u} conuv)
  , wfIrrelevant {u′} (conLemma₁ {u′} conu′v′)
  )
conLemma₁ {Π U f} {⊥} {acc rs} (conU , (conPairsf , conElemsf))
  = wfIrrelevant {U} conU
  , ((λ uv∈f u′v′∈f → wfIrrelevantPairs uv∈f u′v′∈f (conPairsf uv∈f u′v′∈f))
  , λ uv∈f → wfIrrelevantElems uv∈f (conElemsf uv∈f))
conLemma₁ {Π U f} {Π V g} {acc rs} (conUV , (conPairs , conElems))
  = (wfIrrelevant {U} (conLemma₁ {U} conUV))
  , ((λ uv∈f u′v′∈f → wfIrrelevantPairs uv∈f u′v′∈f (conPairs (∪-lemma₃ uv∈f) (∪-lemma₃ u′v′∈f)))
  , λ uv∈f → wfIrrelevantElems uv∈f (conElems (∪-lemma₃ uv∈f)))
conLemma₁ {𝒰} _ = *
conLemma₁ {incons} ()

conLemma₂ : ∀ {u v p} → con' (u ⊔ v) p → con v
conLemma₂ {v = ⊥} _ = *
conLemma₂ {v = 0ᵤ} _ = *
conLemma₂ {⊥} {s v} {acc rs} conuv = wfIrrelevant {v} conuv
conLemma₂ {s u} {s v} {acc rs} conuv
  = wfIrrelevant {v} (conLemma₂ {u} conuv)
conLemma₂ {v = ℕ} _ = *
conLemma₂ {⊥} {F f} {acc rs} (conPairs , conElems)
  = (λ uv∈f u′v′∈f → wfIrrelevantPairs uv∈f u′v′∈f (conPairs uv∈f u′v′∈f))
  , λ uv∈f → wfIrrelevantElems uv∈f (conElems uv∈f)
conLemma₂ {F f} {F g} {acc rs} (conPairs , conElems)
  = (λ uv∈f u′v′∈f → wfIrrelevantPairs uv∈f u′v′∈f (conPairs (∪-lemma₄ uv∈f) (∪-lemma₄ u′v′∈f)))
  , λ uv∈f → wfIrrelevantElems uv∈f (conElems (∪-lemma₄ uv∈f))
conLemma₂ {⊥} {refl v} {acc rs} conuv = wfIrrelevant {v} conuv
conLemma₂ {refl u} {refl v} {acc rs} conuv
  = wfIrrelevant {v} (conLemma₂ {u} conuv)
conLemma₂ {⊥} {I U u u′} {acc rs} (conU , (conu , conu′))
  = wfIrrelevant {U} conU , (wfIrrelevant {u} conu , wfIrrelevant {u′} conu′)
conLemma₂ {I U u u′} {I V v v′} {acc rs} (conUV , (conuv , conu′v′))
  = (wfIrrelevant {V} (conLemma₂ {U} conUV))
  , (wfIrrelevant {v} (conLemma₂ {u} conuv)
  , wfIrrelevant {v′} (conLemma₂ {u′} conu′v′))
conLemma₂ {⊥} {Π U f} {acc rs} (conU , (conPairsf , conElemsf))
  = wfIrrelevant {U} conU
  , ((λ uv∈f u′v′∈f → wfIrrelevantPairs uv∈f u′v′∈f (conPairsf uv∈f u′v′∈f))
  , λ uv∈f → wfIrrelevantElems uv∈f (conElemsf uv∈f))
conLemma₂ {Π U f} {Π V g} {acc rs} (conUV , (conPairs , conElems))
  = (wfIrrelevant {V} (conLemma₂ {U} conUV))
  , ((λ uv∈f u′v′∈f → wfIrrelevantPairs uv∈f u′v′∈f (conPairs (∪-lemma₄ uv∈f) (∪-lemma₄ u′v′∈f)))
  , λ uv∈f → wfIrrelevantElems uv∈f (conElems (∪-lemma₄ uv∈f)))
conLemma₂ {v = 𝒰} _ = *
conLemma₂ {⊥} {incons} ()
conLemma₂ {0ᵤ} {incons} ()
conLemma₂ {s u} {incons} ()
conLemma₂ {ℕ} {incons} ()
conLemma₂ {F conuv₁} {incons} ()
conLemma₂ {Π u conuv₁} {incons} ()
conLemma₂ {𝒰} {incons} ()
conLemma₂ {u = incons} {incons} ()

{-
conLemma₃' : ∀ {i} → {f : FinFun {i}} → conFinFun f → conFinFun (f ∪ f)
conLemma₃' {f = f} (conPairs , conElems) = lemma₁ , lemma₂
  where lemma₁ : ∀ {u v u′ v′} → (u , v) ∈ (f ∪ f) → (u′ , v′) ∈ (f ∪ f) → con (u ⊔ u′) → con (v ⊔ v′)
        lemma₁ uv∈∪ u′v′∈∪ with (∪-lemma₂ {𝑓 = f} uv∈∪) | ∪-lemma₂ {𝑓 = f} u′v′∈∪
        ... | inl uv∈f | inl u′v′∈f = conPairs uv∈f u′v′∈f
        ... | inl uv∈f | inr u′v′∈f = conPairs uv∈f u′v′∈f
        ... | inr uv∈f | inl u′v′∈f = conPairs uv∈f u′v′∈f
        ... | inr uv∈f | inr u′v′∈f = conPairs uv∈f u′v′∈f
        lemma₂ : ∀ {u v} → (u , v) ∈ (f ∪ f) → con u ⊠ con v
        lemma₂ uv∈∪ with (∪-lemma₂ {𝑓 = f} uv∈∪)
        ... | inl uv∈f = conElems uv∈f
        ... | inr uv∈f = conElems uv∈f

conLemma₃ : ∀ {i} → {u : Nbh {i}} → con u → con (u ⊔ u)
conLemma₃ {u = ⊥} conu = *
conLemma₃ {u = 0ᵤ} conu = *
conLemma₃ {u = s u} conu = conLemma₃ {u = u} conu
conLemma₃ {u = ℕ} conu = *
conLemma₃ {u = F f} conu = conLemma₃' conu
conLemma₃ {u = refl u} conu = conLemma₃ {u = u} conu
conLemma₃ {u = I U u v} (conU , (conu , conv))
  = (conLemma₃ {u = U} conU) , (conLemma₃ {u = u} conu , conLemma₃ {u = v} conv)
conLemma₃ {u = Π U f} (conU , conf) = conLemma₃ {u = U} conU , conLemma₃' {f = f} conf
conLemma₃ {u = 𝒰} conu = *
conLemma₃ {u = incons} conu = conu

conFinFunSym : ∀ {i} → {f g : FinFun {i}} → conFinFun (f ∪ g) → conFinFun (g ∪ f)
conFinFunSym {f = f} (conPairsfg , conElemsfg)
  = (λ uv∈∪ u′v′∈∪ conuu′ → conPairsfg (∪-lemma₆ {𝑓′ = f} uv∈∪) (∪-lemma₆ {𝑓′ = f} u′v′∈∪) conuu′) ,
    (λ uv∈∪ → conElemsfg (∪-lemma₆ {𝑓′ = f} uv∈∪))

conSym : ∀ {i} → {u v : Nbh {i}} → con (u ⊔ v) → con (v ⊔ u)
conSym {u = ⊥} {⊥} _ = *
conSym {u = ⊥} {0ᵤ} _ = *
conSym {u = ⊥} {s _} conuv = conuv
conSym {u = ⊥} {ℕ} _ = *
conSym {u = ⊥} {F _} conuv = conuv
conSym {u = ⊥} {refl _} conuv = conuv
conSym {u = ⊥} {I _ _ _} conuv = conuv
conSym {u = ⊥} {Π _ _} conuv = conuv
conSym {u = ⊥} {𝒰} _ = *
conSym {u = 0ᵤ} {⊥} _ = *
conSym {u = 0ᵤ} {0ᵤ} _ = *
conSym {u = s _} {⊥} conuv = conuv
conSym {u = s u} {s _} conuv = conSym {u = u} conuv
conSym {u = ℕ} {⊥} _ = *
conSym {u = ℕ} {ℕ} _ = *
conSym {u = F _} {⊥} conuv = conuv
conSym {u = F f} {F g} conuv = conFinFunSym {f = f} conuv
conSym {u = refl _} {⊥} conuv = conuv
conSym {u = refl u} {refl v} conuv = conSym {u = u} conuv
conSym {u = I _ _ _} {⊥} conuv = conuv
conSym {u = I U u v} {I U′ u′ v′} (conUU′ , (conuu′ , convv′))
  = (conSym {u = U} conUU′) , (conSym {u = u} conuu′ , conSym {u = v} convv′)
conSym {u = Π _ _} {⊥} conuv = conuv
conSym {u = Π u f} {Π _ _} (conuv , confg) = (conSym {u = u} conuv) , conFinFunSym {f = f} confg
conSym {u = 𝒰} {⊥} _ = *
conSym {u = 𝒰} {𝒰} _ = *

conFinFunAssoc : ∀ {i} → {f g h : FinFun {i}} → conFinFun (f ∪ (g ∪ h)) → conFinFun ((f ∪ g) ∪ h)
conFinFunAssoc {f = f} {g} {h} (conPairsfgh , conElemsfgh)
  = (λ uv∈ u′v′∈ conuu′ → conPairsfgh (∪-lemma₈ {𝑓 = f} uv∈) (∪-lemma₈ {𝑓 = f} u′v′∈) conuu′) ,
    (λ uv∈ → conElemsfgh (∪-lemma₈ {𝑓 = f} uv∈))

conAssoc'' : ∀ {i} → {u v : Nbh {i}} → con (u ⊔ v) → con ((u ⊔ ⊥) ⊔ v)
conAssoc'' {u = ⊥} conuv = conuv
conAssoc'' {u = 0ᵤ} conuv = conuv
conAssoc'' {u = s _} conuv = conuv
conAssoc'' {u = ℕ} conuv = conuv
conAssoc'' {u = F _} conuv = conuv
conAssoc'' {u = refl _} conuv = conuv
conAssoc'' {u = I _ _ _} conuv = conuv
conAssoc'' {u = Π _ _} conuv = conuv
conAssoc'' {u = 𝒰} conuv = conuv

conAssoc' : ∀ {i} → {u : Nbh {i}} → con u → con (u ⊔ ⊥)
conAssoc' {u = ⊥} _ = *
conAssoc' {u = 0ᵤ} _ = *
conAssoc' {u = s _} conu = conu
conAssoc' {u = ℕ} _ = *
conAssoc' {u = F _} conf = conf
conAssoc' {u = refl _} conu = conu
conAssoc' {u = I _ _ _} conu = conu
conAssoc' {u = Π _ _} conu = conu
conAssoc' {u = 𝒰} _ = *

conAssoc₁ : ∀ {i} → {u v w : Nbh {i}} → con (u ⊔ (v ⊔ w)) → con ((u ⊔ v) ⊔ w)
conAssoc₁ {u = u} conuvw with (conLemma₁ {u = u} conuvw) | conLemma₂ {u = u} conuvw
conAssoc₁ {u = u} {v} _ | _ | convw with (conLemma₁ {u = v} convw) |  conLemma₂ {u = v} convw
conAssoc₁ {u = u} {⊥} {w} conuvw | _ | _ | _ | _ = conAssoc'' {u = u} conuvw
conAssoc₁ {u = u} {0ᵤ} {⊥} conuvw | _ | _ | _ | _ = conAssoc' {u = u ⊔ 0ᵤ} conuvw
conAssoc₁ {u = ⊥} {0ᵤ} {0ᵤ} _ | _ | _ | _ | _ = *
conAssoc₁ {u = 0ᵤ} {0ᵤ} {0ᵤ} _ | _ | _ | _ | _ = *
conAssoc₁ {u = u} {s v} {⊥} conuvw | _ | _ | _ | _ = conAssoc' {u = u ⊔ s v} conuvw
conAssoc₁ {u = ⊥} {s _} {s _} conuvw | _ | _ | _ | _ = conuvw
conAssoc₁ {u = s u} {s _} {s _} conuvw | _ | _ | _ | _ = conAssoc₁ {u = u} conuvw
conAssoc₁ {u = u} {ℕ} {⊥} conuvw | _ | _ | _ | _ = conAssoc' {u = u ⊔ ℕ} conuvw
conAssoc₁ {u = ⊥} {ℕ} {ℕ} _ | _ | _ | _ | _ = *
conAssoc₁ {u = ℕ} {ℕ} {ℕ} _ | _ | _ | _ | _ = *
conAssoc₁ {u = u} {F f} {⊥} conuvw | _ | _ | _ | _ = conAssoc' {u = u ⊔ F f} conuvw
conAssoc₁ {u = ⊥} {F _} {F _} conuvw | _ | _ | _ | _ = conuvw
conAssoc₁ {u = F f} {F _} {F _} conuvw | _ | _ | _ | _ = conFinFunAssoc {f = f} conuvw
conAssoc₁ {u = u} {refl v} {⊥} conuvw | _ | _ | _ | _ = conAssoc' {u = u ⊔ refl v} conuvw
conAssoc₁ {u = ⊥} {refl _} {refl _} conuvw | _ | _ | _ | _ = conuvw
conAssoc₁ {u = refl u} {refl _} {refl _} conuvw | _ | _ | _ | _ = conAssoc₁ {u = u} conuvw
conAssoc₁ {u = u} {I U′ u′ v′} {⊥} conuvw | _ | _ | _ | _ = conAssoc' {u = u ⊔ I U′ u′ v′} conuvw
conAssoc₁ {u = ⊥} {I U′ u′ v′} {I U″ u″ v″} conuvw | _ | _ | _ | _ = conuvw
conAssoc₁ {u = I U u v} {I U′ u′ v′} {I U″ u″ v″} (conUs , (conus , convs)) | _ | _ | _ | _
  = conAssoc₁ {u = U} conUs , (conAssoc₁ {u = u} conus , conAssoc₁ {u = v} convs)
conAssoc₁ {u = u} {Π v g} {⊥} conuvw | _ | _ | _ | _ = conAssoc' {u = u ⊔ Π v g} conuvw
conAssoc₁ {u = ⊥} {Π v g} {Π w h} conuvw | _ | _ | _ | _ = conuvw
conAssoc₁ {u = Π u f} {Π v g} {Π w h} (conuvw , confgh) | _ | _ | _ | _
  = conAssoc₁ {u = u} conuvw , conFinFunAssoc {f = f} confgh
conAssoc₁ {u = u} {𝒰} {⊥} conuvw | _ | _ | _ | _ = conAssoc' {u = u ⊔ 𝒰} conuvw
conAssoc₁ {u = ⊥} {𝒰} {𝒰} _ | _ | _ | _ | _ = *
conAssoc₁ {u = 𝒰} {𝒰} {𝒰} _ | _ | _ | _ | _ = *

conAssoc₂ : ∀ {i} → {u v w : Nbh {i}} → con ((u ⊔ v) ⊔ w) → con (u ⊔ (v ⊔ w))
conAssoc₂ {u = u} {v} {w} conuvw = conSym {u = v ⊔ w} {u} convw|u
  where conw|uv = conSym {u = u ⊔ v} {w} conuvw
        conwu|v = conAssoc₁ {u = w} {u} {v} conw|uv
        conv|wu = conSym {u = w ⊔ u} {v} conwu|v
        convw|u = conAssoc₁ {u = v} {w} {u} conv|wu

conTrans : ∀ {i} → {u v w : Nbh {i}} → con (u ⊔ (v ⊔ w)) → con (u ⊔ w)
conTrans {u = u} conuvw with (conLemma₁ {u = u} conuvw) | conLemma₂ {u = u} conuvw
conTrans {u = u} {v} _ | _ | convw with (conLemma₁ {u = v} convw) | conLemma₂ {u = v} convw
conTrans {u = u} {v} {⊥} _ | conu | _ | _ | _ = conSym {u = ⊥} {u} conu
conTrans {u = u} {⊥} {0ᵤ} conuvw | _ | _ | _ | _ = conuvw
conTrans {u = u} {0ᵤ} {0ᵤ} conuvw | _ | _ | _ | _ = conuvw
conTrans {u = u} {⊥} {s _} conuvw | _ | _ | _ | _ = conuvw
conTrans {u = ⊥} {s _} {s _} _ | _ | _ | _ | conw = conw
conTrans {u = s u} {s _} {s _} conuvw | _ | _ | _ | conw = conTrans {u = u} conuvw
conTrans {u = u} {⊥} {ℕ} conuvw | _ | _ | _ | _ = conuvw
conTrans {u = u} {ℕ} {ℕ} conuvw | _ | _ | _ | _ = conuvw
conTrans {u = u} {⊥} {F _} conuvw | _ | _ | _ | _ = conuvw
conTrans {u = ⊥} {F _} {F _} _ | _ | _ | _ | conw = conw
conTrans {u = F f} {F g} {F h} conuvw | _ | _ | _ | _
  = subsetIsCon {g = f ∪ (g ∪ h)} (∪-lemma₇ {𝑓 = f} ∪-lemma₄) conuvw
conTrans {u = u} {⊥} {refl _} conuvw | _ | _ | _ | _ = conuvw
conTrans {u = ⊥} {refl _} {refl _} _ | _ | _ | _ | conw = conw
conTrans {u = refl u} {refl _} {refl _} conuvw | _ | _ | _ | _ = conTrans {u = u} conuvw
conTrans {u = u} {⊥} {I _ _ _} conuvw | _ | _ | _ | _ = conuvw
conTrans {u = ⊥} {I _ _ _} {I _ _ _} _ | _ | _ | _ | conw = conw
conTrans {u = I U u v} {I U′ u′ v′} {I U″ u″ v″} (conUs , (conus , convs)) | _ | _ | _ | _
  = conTrans {u = U} conUs , (conTrans {u = u} conus , conTrans {u = v} convs)
conTrans {u = u} {⊥} {Π _ _} conuvw | _ | _ | _ | _ = conuvw
conTrans {u = ⊥} {Π _ _} {Π _ _} _ | _ | _ | _ | conw = conw
conTrans {u = Π u f} {Π v g} {Π w h} (conuvw , confgh) | _ | _ | _ | _
  = (conTrans {u = u} conuvw) , subsetIsCon {g = f ∪ (g ∪ h)} (∪-lemma₇ {𝑓 = f} ∪-lemma₄) confgh
conTrans {u = u} {⊥} {𝒰} conuvw | _ | _ | _ | _ = conuvw
conTrans {u = ⊥} {𝒰} {𝒰} _ | _ | _ | _ | _ = *
conTrans {u = 𝒰} {𝒰} {𝒰} _ | _ | _ | _ | _ = *
-}
