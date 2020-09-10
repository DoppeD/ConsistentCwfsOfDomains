{-# OPTIONS --safe --sized-types #-}

module Ucwf.DomainUcwf.LambdaBetaInstance where

open import Ucwf.LambdaBeta
open import Ucwf.DomainUcwf.LambdaBeta.ap.Instance
open import Ucwf.DomainUcwf.LambdaBeta.apCong
open import Ucwf.DomainUcwf.LambdaBeta.apSub
open import Ucwf.DomainUcwf.LambdaBeta.beta
open import Ucwf.DomainUcwf.LambdaBeta.lam.Instance
open import Ucwf.DomainUcwf.LambdaBeta.lamCong
open import Ucwf.DomainUcwf.LambdaBeta.lamSub
open import Ucwf.DomainUcwf.PlainInstance

domλβUcwf : λβ-ucwf
λβ-ucwf.ucwf domλβUcwf    = domUcwf
λβ-ucwf.lam domλβUcwf     = lam
λβ-ucwf.ap domλβUcwf      = ap
λβ-ucwf.lamSub domλβUcwf  = lamSub
λβ-ucwf.apSub domλβUcwf   = apSub
λβ-ucwf.β domλβUcwf       = β-equal
λβ-ucwf.lamCong domλβUcwf = lamCong
λβ-ucwf.apCong domλβUcwf  = apCong
