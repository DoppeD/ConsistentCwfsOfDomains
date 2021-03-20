{-# OPTIONS --safe --sized-types #-}

module Cwf.DomainCwf.UniType.ConsistencyLemmata where

open import Base.Core
open import Cwf.DomainCwf.UniType.Consistency
open import Cwf.DomainCwf.UniType.Definition
open import Cwf.DomainCwf.UniType.FinFun

open import Agda.Builtin.Equality

subsetIsCon : ∀ {i} → {f g : FinFun {i}} → f ⊆ g → conFinFun g → conFinFun f
subsetIsCon f⊆g (conPairsg , conElemsg)
  = (λ uv∈f u′v′∈f conuu′ → conPairsg (f⊆g uv∈f) (f⊆g u′v′∈f) conuu′) ,
    (λ uv∈f → conElemsg (f⊆g uv∈f))

conLemma₁ : ∀ {i} → {u v : Nbh {i}} → con (u ⊔ v) → con u
conLemma₁ {u = ⊥} _ = *
conLemma₁ {u = 0ᵤ} _ = *
conLemma₁ {u = s _} {⊥} conuv = conuv
conLemma₁ {u = s u} {s _} conuv = conLemma₁ {u = u} conuv
conLemma₁ {u = ℕ} _ = *
conLemma₁ {u = F _} {⊥} conuv = conuv
conLemma₁ {u = F f} {F g} (conPairsfg , conElemsfg)
  = (λ uv∈f u′v′∈f conuu′ → conPairsfg (∪-lemma₃ uv∈f) (∪-lemma₃ u′v′∈f) conuu′) ,
    (λ uv∈f → conElemsfg (∪-lemma₃ uv∈f))
conLemma₁ {u = Π _ _} {⊥} conuv = conuv
conLemma₁ {u = Π u f} {Π v g} (conuv , confg)
  = conLemma₁ {u = u} conuv , subsetIsCon (∪-lemma₃ {𝑓′ = g}) confg
conLemma₁ {u = 𝒰} _ = *

conLemma₂ : ∀ {i} → {u v : Nbh {i}} → con (u ⊔ v) → con v
conLemma₂ {v = ⊥} _ = *
conLemma₂ {v = 0ᵤ} _ = *
conLemma₂ {u = ⊥} {s _} conuv = conuv
conLemma₂ {u = s u} {s _} conuv = conLemma₂ {u = u} conuv
conLemma₂ {v = ℕ} _ = *
conLemma₂ {u = ⊥} {F _} conuv = conuv
conLemma₂ {u = F f} {F g} (conPairsfg , conElemsfg)
  = (λ uv∈g u′v′∈g conuu′ → conPairsfg (∪-lemma₄ uv∈g) (∪-lemma₄ u′v′∈g) conuu′) ,
    (λ uv∈g → conElemsfg (∪-lemma₄ uv∈g))
conLemma₂ {u = ⊥} {Π _ _} conuv = conuv
conLemma₂ {u = Π u f} {Π v g} (conuv , confg)
  = conLemma₂ {u = u} conuv , subsetIsCon (∪-lemma₄ {𝑓′ = g}) confg
conLemma₂ {v = 𝒰} _ = *
conLemma₂ {u = ⊥} {incons} conuv = conuv
conLemma₂ {u = 0ᵤ} {incons} conuv = conuv
conLemma₂ {u = s u} {incons} conuv = conuv
conLemma₂ {u = ℕ} {incons} conuv = conuv
conLemma₂ {u = F conuv₁} {incons} conuv = conuv
conLemma₂ {u = Π u conuv₁} {incons} conuv = conuv
conLemma₂ {u = 𝒰} {incons} conuv = conuv
conLemma₂ {u = incons} {incons} conuv = conuv

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
conAssoc'' {u = Π _ _} conuv = conuv
conAssoc'' {u = 𝒰} conuv = conuv

conAssoc' : ∀ {i} → {u : Nbh {i}} → con u → con (u ⊔ ⊥)
conAssoc' {u = ⊥} _ = *
conAssoc' {u = 0ᵤ} _ = *
conAssoc' {u = s _} conu = conu
conAssoc' {u = ℕ} _ = *
conAssoc' {u = F _} conf = conf
conAssoc' {u = Π _ _} conux = conux
conAssoc' {u = 𝒰} _ = *

conAssoc₁ : ∀ {i} → {u v w : Nbh {i}} → con (u ⊔ (v ⊔ w)) → con ((u ⊔ v) ⊔ w)
conAssoc₁ {u = u} conuvw with (conLemma₁ {u = u} conuvw) | conLemma₂ {u = u} conuvw
conAssoc₁ {u = u} {v} _ | conu | convw with (conLemma₁ {u = v} convw) |  conLemma₂ {u = v} convw
conAssoc₁ {u = u} {⊥} {w} conuvw | conu | convw | conv | conw = conAssoc'' {u = u} conuvw
conAssoc₁ {u = u} {0ᵤ} {⊥} conuvw | conu | convw | conv | conw = conAssoc' {u = u ⊔ 0ᵤ} conuvw
conAssoc₁ {u = ⊥} {0ᵤ} {0ᵤ} conuvw | conu | convw | conv | conw = *
conAssoc₁ {u = 0ᵤ} {0ᵤ} {0ᵤ} conuvw | conu | convw | conv | conw = *
conAssoc₁ {u = u} {s v} {⊥} conuvw | conu | convw | conv | conw = conAssoc' {u = u ⊔ s v} conuvw
conAssoc₁ {u = ⊥} {s _} {s _} conuvw | conu | convw | conv | conw = conuvw
conAssoc₁ {u = s u} {s _} {s _} conuvw | conu | convw | conv | conw = conAssoc₁ {u = u} conuvw
conAssoc₁ {u = u} {ℕ} {⊥} conuvw | conu | convw | conv | conw = conAssoc' {u = u ⊔ ℕ} conuvw
conAssoc₁ {u = ⊥} {ℕ} {ℕ} conuvw | conu | convw | conv | conw = *
conAssoc₁ {u = ℕ} {ℕ} {ℕ} conuvw | conu | convw | conv | conw = *
conAssoc₁ {u = u} {F f} {⊥} conuvw | conu | convw | conv | conw = conAssoc' {u = u ⊔ F f} conuvw
conAssoc₁ {u = ⊥} {F _} {F _} conuvw | conu | convw | conv | conw = conuvw
conAssoc₁ {u = F f} {F _} {F _} conuvw | conu | convw | conv | conw = conFinFunAssoc {f = f} conuvw
conAssoc₁ {u = u} {Π v g} {⊥} conuvw | conu | convw | conv | conw = conAssoc' {u = u ⊔ Π v g} conuvw
conAssoc₁ {u = ⊥} {Π v g} {Π w h} conuvw | conu | convw | conv | conw = conuvw
conAssoc₁ {u = Π u f} {Π v g} {Π w h} (conuvw , confgh) | conu | convw | conv | conw
  = conAssoc₁ {u = u} conuvw , conFinFunAssoc {f = f} confgh
conAssoc₁ {u = u} {𝒰} {⊥} conuvw | conu | convw | conv | conw = conAssoc' {u = u ⊔ 𝒰} conuvw
conAssoc₁ {u = ⊥} {𝒰} {𝒰} conuvw | conu | convw | conv | conw = *
conAssoc₁ {u = 𝒰} {𝒰} {𝒰} conuvw | conu | convw | conv | conw = *

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
conTrans {u = u} {⊥} {Π _ _} conuvw | _ | _ | _ | _ = conuvw
conTrans {u = ⊥} {Π _ _} {Π _ _} _ | _ | _ | _ | conw = conw
conTrans {u = Π u f} {Π v g} {Π w h} (conuvw , confgh) | _ | _ | _ | _
  = (conTrans {u = u} conuvw) , subsetIsCon {g = f ∪ (g ∪ h)} (∪-lemma₇ {𝑓 = f} ∪-lemma₄) confgh
conTrans {u = u} {⊥} {𝒰} conuvw | _ | _ | _ | _ = conuvw
conTrans {u = ⊥} {𝒰} {𝒰} _ | _ | _ | _ | _ = *
conTrans {u = 𝒰} {𝒰} {𝒰} _ | _ | _ | _ | _ = *
