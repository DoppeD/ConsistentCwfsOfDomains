module Cwf.DomainCwf.UniType.ConsistencyLemmata where

open import Base.Core
open import Base.FinFun
open import Cwf.DomainCwf.UniType.Consistency
open import Cwf.DomainCwf.UniType.Definition

open import Agda.Builtin.Equality

subsetIsCon : ∀ {f g} → f ⊆ g → conFinFun g → conFinFun f
subsetIsCon f⊆g (conPairsg , conElemsg)
  = (λ uv∈f u′v′∈f conuu′ → conPairsg (f⊆g uv∈f) (f⊆g u′v′∈f) conuu′) ,
    (λ uv∈f → conElemsg (f⊆g uv∈f))

conLemma₁ : ∀ {u v} → con (u ⊔ v) → con u
conLemma₁ {⊥} _ = *
conLemma₁ {0ᵤ} _ = *
conLemma₁ {s _} {⊥} conuv = conuv
conLemma₁ {s u} {s _} conuv = conLemma₁ {u} conuv
conLemma₁ {ℕ} _ = *
conLemma₁ {F _} {⊥} conuv = conuv
conLemma₁ {F f} {F g} (conPairsfg , conElemsfg)
  = (λ uv∈f u′v′∈f conuu′ → conPairsfg (∪-lemma₃ uv∈f) (∪-lemma₃ u′v′∈f) conuu′) ,
    (λ uv∈f → conElemsfg (∪-lemma₃ uv∈f))
conLemma₁ {refl _} {⊥} conuv = conuv
conLemma₁ {refl u} {refl v} conuv = conLemma₁ {u} conuv
conLemma₁ {I _ _ _} {⊥} conuv = conuv
conLemma₁ {I U u v} {I U′ u′ v′} (conUU′ , (conuu′ , convv′))
  = (conLemma₁ {U} conUU′) , (conLemma₁ {u} conuu′ , conLemma₁ {v} convv′)
conLemma₁ {Π _ _} {⊥} conuv = conuv
conLemma₁ {Π u f} {Π v g} (conuv , confg)
  = conLemma₁ {u} conuv , subsetIsCon (∪-lemma₃ {𝑓′ = g}) confg
conLemma₁ {𝒰} _ = *

conLemma₂ : ∀ {u v} → con (u ⊔ v) → con v
conLemma₂ {v = ⊥} _ = *
conLemma₂ {v = 0ᵤ} _ = *
conLemma₂ {⊥} {s _} conuv = conuv
conLemma₂ {s u} {s _} conuv = conLemma₂ {u} conuv
conLemma₂ {v = ℕ} _ = *
conLemma₂ {⊥} {F _} conuv = conuv
conLemma₂ {F f} {F g} (conPairsfg , conElemsfg)
  = (λ uv∈g u′v′∈g conuu′ → conPairsfg (∪-lemma₄ uv∈g) (∪-lemma₄ u′v′∈g) conuu′) ,
    (λ uv∈g → conElemsfg (∪-lemma₄ uv∈g))
conLemma₂ {⊥} {refl _} conuv = conuv
conLemma₂ {refl u} {refl v} conuv = conLemma₂ {u} conuv
conLemma₂ {⊥} {I _ _ _} conuv = conuv
conLemma₂ {I U u v} {I U′ u′ v′} (conUU′ , (conuu′ , convv′))
  = conLemma₂ {U} conUU′ , (conLemma₂ {u} conuu′ , conLemma₂ {v} convv′)
conLemma₂ {⊥} {Π _ _} conuv = conuv
conLemma₂ {Π u f} {Π v g} (conuv , confg)
  = conLemma₂ {u} conuv , subsetIsCon (∪-lemma₄ {𝑓′ = g}) confg
conLemma₂ {v = 𝒰} _ = *
conLemma₂ {⊥} {incons} conuv = conuv
conLemma₂ {0ᵤ} {incons} conuv = conuv
conLemma₂ {s u} {incons} conuv = conuv
conLemma₂ {ℕ} {incons} conuv = conuv
conLemma₂ {F _} {incons} conuv = conuv
conLemma₂ {Π _ _} {incons} conuv = conuv
conLemma₂ {𝒰} {incons} conuv = conuv
conLemma₂ {incons} {incons} conuv = conuv

conLemma₃' : ∀ {f} → conFinFun f → conFinFun (f ∪ f)
conLemma₃' {f} (conPairs , conElems)
  = (λ uv∈∪ u′v′∈∪ → conPairs (∪-lemma₉ uv∈∪) (∪-lemma₉ u′v′∈∪))
  , (λ uv∈∪ → (⊠-fst (conElems (∪-lemma₉ uv∈∪))) , ⊠-snd (conElems (∪-lemma₉ uv∈∪)))

conLemma₃ : ∀ {u} → con u → con (u ⊔ u)
conLemma₃ {⊥} conu = *
conLemma₃ {0ᵤ} conu = *
conLemma₃ {s u} conu = conLemma₃ {u} conu
conLemma₃ {ℕ} conu = *
conLemma₃ {F f} conu = conLemma₃' conu
conLemma₃ {refl u} conu = conLemma₃ {u} conu
conLemma₃ {I U u v} (conU , (conu , conv))
  = (conLemma₃ {U} conU) , (conLemma₃ {u} conu , conLemma₃ {v} conv)
conLemma₃ {Π U f} (conU , conf) = conLemma₃ {U} conU , conLemma₃' {f = f} conf
conLemma₃ {𝒰} conu = *
conLemma₃ {incons} conu = conu


conFinFunSym : ∀ {f g} → conFinFun (f ∪ g) → conFinFun (g ∪ f)
conFinFunSym {f} (conPairsfg , conElemsfg)
  = (λ uv∈∪ u′v′∈∪ conuu′ → conPairsfg (∪-lemma₆ {𝑓′ = f} uv∈∪) (∪-lemma₆ {𝑓′ = f} u′v′∈∪) conuu′) ,
    (λ uv∈∪ → conElemsfg (∪-lemma₆ {𝑓′ = f} uv∈∪))

conSym : ∀ {u v} → con (u ⊔ v) → con (v ⊔ u)
conSym {⊥} {⊥} _ = *
conSym {⊥} {0ᵤ} _ = *
conSym {⊥} {s _} conuv = conuv
conSym {⊥} {ℕ} _ = *
conSym {⊥} {F _} conuv = conuv
conSym {⊥} {refl _} conuv = conuv
conSym {⊥} {I _ _ _} conuv = conuv
conSym {⊥} {Π _ _} conuv = conuv
conSym {⊥} {𝒰} _ = *
conSym {0ᵤ} {⊥} _ = *
conSym {0ᵤ} {0ᵤ} _ = *
conSym {s _} {⊥} conuv = conuv
conSym {s u} {s _} conuv = conSym {u} conuv
conSym {ℕ} {⊥} _ = *
conSym {ℕ} {ℕ} _ = *
conSym {F _} {⊥} conuv = conuv
conSym {F f} {F g} conuv = conFinFunSym {f = f} conuv
conSym {refl _} {⊥} conuv = conuv
conSym {refl u} {refl v} conuv = conSym {u} conuv
conSym {I _ _ _} {⊥} conuv = conuv
conSym {I U u v} {I U′ u′ v′} (conUU′ , (conuu′ , convv′))
  = (conSym {U} conUU′) , (conSym {u} conuu′ , conSym {v} convv′)
conSym {Π _ _} {⊥} conuv = conuv
conSym {Π u f} {Π _ _} (conuv , confg) = (conSym {u} conuv) , conFinFunSym {f = f} confg
conSym {𝒰} {⊥} _ = *
conSym {𝒰} {𝒰} _ = *

conFinFunAssoc : ∀ {f g h} → conFinFun (f ∪ (g ∪ h)) → conFinFun ((f ∪ g) ∪ h)
conFinFunAssoc {f} {g} {h} (conPairsfgh , conElemsfgh)
  = (λ uv∈ u′v′∈ conuu′ → conPairsfgh (∪-lemma₈ {𝑓 = f} uv∈) (∪-lemma₈ {𝑓 = f} u′v′∈) conuu′) ,
    (λ uv∈ → conElemsfgh (∪-lemma₈ {𝑓 = f} uv∈))

conAssoc'' : ∀ {u v} → con (u ⊔ v) → con ((u ⊔ ⊥) ⊔ v)
conAssoc'' {⊥} conuv = conuv
conAssoc'' {0ᵤ} conuv = conuv
conAssoc'' {s _} conuv = conuv
conAssoc'' {ℕ} conuv = conuv
conAssoc'' {F _} conuv = conuv
conAssoc'' {refl _} conuv = conuv
conAssoc'' {I _ _ _} conuv = conuv
conAssoc'' {Π _ _} conuv = conuv
conAssoc'' {𝒰} conuv = conuv

conAssoc' : ∀ {u} → con u → con (u ⊔ ⊥)
conAssoc' {⊥} _ = *
conAssoc' {0ᵤ} _ = *
conAssoc' {s _} conu = conu
conAssoc' {ℕ} _ = *
conAssoc' {F _} conf = conf
conAssoc' {refl _} conu = conu
conAssoc' {I _ _ _} conu = conu
conAssoc' {Π _ _} conu = conu
conAssoc' {𝒰} _ = *

conAssoc₁ : ∀ {u v w} → con (u ⊔ (v ⊔ w)) → con ((u ⊔ v) ⊔ w)
conAssoc₁ {u} conuvw with (conLemma₁ {u} conuvw) | conLemma₂ {u} conuvw
conAssoc₁ {u} {v} _ | _ | convw with (conLemma₁ {v} convw) |  conLemma₂ {v} convw
conAssoc₁ {u} {⊥} {w} conuvw | _ | _ | _ | _ = conAssoc'' {u} conuvw
conAssoc₁ {u} {0ᵤ} {⊥} conuvw | _ | _ | _ | _ = conAssoc' {u ⊔ 0ᵤ} conuvw
conAssoc₁ {⊥} {0ᵤ} {0ᵤ} _ | _ | _ | _ | _ = *
conAssoc₁ {0ᵤ} {0ᵤ} {0ᵤ} _ | _ | _ | _ | _ = *
conAssoc₁ {u} {s v} {⊥} conuvw | _ | _ | _ | _ = conAssoc' {u ⊔ s v} conuvw
conAssoc₁ {⊥} {s _} {s _} conuvw | _ | _ | _ | _ = conuvw
conAssoc₁ {s u} {s _} {s _} conuvw | _ | _ | _ | _ = conAssoc₁ {u} conuvw
conAssoc₁ {u} {ℕ} {⊥} conuvw | _ | _ | _ | _ = conAssoc' {u ⊔ ℕ} conuvw
conAssoc₁ {⊥} {ℕ} {ℕ} _ | _ | _ | _ | _ = *
conAssoc₁ {ℕ} {ℕ} {ℕ} _ | _ | _ | _ | _ = *
conAssoc₁ {u} {F f} {⊥} conuvw | _ | _ | _ | _ = conAssoc' {u ⊔ F f} conuvw
conAssoc₁ {⊥} {F _} {F _} conuvw | _ | _ | _ | _ = conuvw
conAssoc₁ {F f} {F _} {F _} conuvw | _ | _ | _ | _ = conFinFunAssoc {f = f} conuvw
conAssoc₁ {u} {refl v} {⊥} conuvw | _ | _ | _ | _ = conAssoc' {u ⊔ refl v} conuvw
conAssoc₁ {⊥} {refl _} {refl _} conuvw | _ | _ | _ | _ = conuvw
conAssoc₁ {refl u} {refl _} {refl _} conuvw | _ | _ | _ | _ = conAssoc₁ {u} conuvw
conAssoc₁ {u} {I U′ u′ v′} {⊥} conuvw | _ | _ | _ | _ = conAssoc' {u ⊔ I U′ u′ v′} conuvw
conAssoc₁ {⊥} {I U′ u′ v′} {I U″ u″ v″} conuvw | _ | _ | _ | _ = conuvw
conAssoc₁ {I U u v} {I U′ u′ v′} {I U″ u″ v″} (conUs , (conus , convs)) | _ | _ | _ | _
  = conAssoc₁ {U} conUs , (conAssoc₁ {u} conus , conAssoc₁ {v} convs)
conAssoc₁ {u} {Π v g} {⊥} conuvw | _ | _ | _ | _ = conAssoc' {u ⊔ Π v g} conuvw
conAssoc₁ {⊥} {Π v g} {Π w h} conuvw | _ | _ | _ | _ = conuvw
conAssoc₁ {Π u f} {Π v g} {Π w h} (conuvw , confgh) | _ | _ | _ | _
  = conAssoc₁ {u} conuvw , conFinFunAssoc {f = f} confgh
conAssoc₁ {u} {𝒰} {⊥} conuvw | _ | _ | _ | _ = conAssoc' {u ⊔ 𝒰} conuvw
conAssoc₁ {⊥} {𝒰} {𝒰} _ | _ | _ | _ | _ = *
conAssoc₁ {𝒰} {𝒰} {𝒰} _ | _ | _ | _ | _ = *

conAssoc₂ : ∀ {u v w} → con ((u ⊔ v) ⊔ w) → con (u ⊔ (v ⊔ w))
conAssoc₂ {u} {v} {w} conuvw = conSym {v ⊔ w} {u} convw|u
  where conw|uv = conSym {u ⊔ v} {w} conuvw
        conwu|v = conAssoc₁ {w} {u} {v} conw|uv
        conv|wu = conSym {w ⊔ u} {v} conwu|v
        convw|u = conAssoc₁ {v} {w} {u} conv|wu

conTrans : ∀ {u v w} → con (u ⊔ (v ⊔ w)) → con (u ⊔ w)
conTrans {u} conuvw with (conLemma₁ {u} conuvw) | conLemma₂ {u} conuvw
conTrans {u} {v} _ | _ | convw with (conLemma₁ {v} convw) | conLemma₂ {v} convw
conTrans {u} {v} {⊥} _ | conu | _ | _ | _ = conSym {⊥} {u} conu
conTrans {u} {⊥} {0ᵤ} conuvw | _ | _ | _ | _ = conuvw
conTrans {u} {0ᵤ} {0ᵤ} conuvw | _ | _ | _ | _ = conuvw
conTrans {u} {⊥} {s _} conuvw | _ | _ | _ | _ = conuvw
conTrans {⊥} {s _} {s _} _ | _ | _ | _ | conw = conw
conTrans {s u} {s _} {s _} conuvw | _ | _ | _ | conw = conTrans {u} conuvw
conTrans {u} {⊥} {ℕ} conuvw | _ | _ | _ | _ = conuvw
conTrans {u} {ℕ} {ℕ} conuvw | _ | _ | _ | _ = conuvw
conTrans {u} {⊥} {F _} conuvw | _ | _ | _ | _ = conuvw
conTrans {⊥} {F _} {F _} _ | _ | _ | _ | conw = conw
conTrans {F f} {F g} {F h} conuvw | _ | _ | _ | _
  = subsetIsCon {g = f ∪ (g ∪ h)} (∪-lemma₇ {𝑓 = f} ∪-lemma₄) conuvw
conTrans {u} {⊥} {refl _} conuvw | _ | _ | _ | _ = conuvw
conTrans {⊥} {refl _} {refl _} _ | _ | _ | _ | conw = conw
conTrans {refl u} {refl _} {refl _} conuvw | _ | _ | _ | _ = conTrans {u} conuvw
conTrans {u} {⊥} {I _ _ _} conuvw | _ | _ | _ | _ = conuvw
conTrans {⊥} {I _ _ _} {I _ _ _} _ | _ | _ | _ | conw = conw
conTrans {I U u v} {I U′ u′ v′} {I U″ u″ v″} (conUs , (conus , convs)) | _ | _ | _ | _
  = conTrans {U} conUs , (conTrans {u} conus , conTrans {v} convs)
conTrans {u} {⊥} {Π _ _} conuvw | _ | _ | _ | _ = conuvw
conTrans {⊥} {Π _ _} {Π _ _} _ | _ | _ | _ | conw = conw
conTrans {Π u f} {Π v g} {Π w h} (conuvw , confgh) | _ | _ | _ | _
  = (conTrans {u} conuvw) , subsetIsCon {g = f ∪ (g ∪ h)} (∪-lemma₇ {𝑓 = f} ∪-lemma₄) confgh
conTrans {u} {⊥} {𝒰} conuvw | _ | _ | _ | _ = conuvw
conTrans {⊥} {𝒰} {𝒰} _ | _ | _ | _ | _ = *
conTrans {𝒰} {𝒰} {𝒰} _ | _ | _ | _ | _ = *
