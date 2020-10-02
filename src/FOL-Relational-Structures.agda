module FOL-Relational-Structures where

open import Data.Nat using () renaming (ℕ to Nat)
open import Data.Fin using (Fin; _≟_)
open import Data.Vec using (Vec; map)
open import Data.Bool using (Bool; true; false; _∧_) renaming (not to ¬_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)

infix 10  not_
infix 9 _and_
infix 8  _or_
infix 7  _impl_

Consts = {n : Nat} -> Fin n
Rels   = {m : Nat} -> Fin m
Signature = Consts ⊎ Rels
postulate
  ar : Rels -> Nat

Dom = {n : Nat} -> Fin n

img : Signature -> Set
img (inj₁ c) = Dom
img (inj₂ r) = Vec Dom (ar r)

postulate
  _ˢ : (s : Signature) -> img s

Name = Nat

data T : Set where
  C : Consts -> T
  V : Name   -> T

data F  : Set where
  _and_ : F -> F -> F
  not_  : F -> F
  rel   :(r : Rels) -> Vec T (ar r) -> F
  _eq_  : T -> T -> F
  exist : Name -> F -> F

_or_ : F -> F -> F
φ₀ or φ₁ = not (not φ₀ and not φ₁)

_impl_ : F -> F -> F
φ₀ impl φ₁ = not φ₀ or φ₁

universal : Name -> F -> F
universal n φ = not (exist n (not φ))

_[_/_] : (Name -> Dom) -> Dom -> Name -> (Name -> Dom)
(α [ d / x ]) n = {!!}


evalT : (Name -> Dom) -> ((σ : Signature) -> img σ) -> (τ : T) -> Dom
evalT α _ˢ (C c) = inj₁ c ˢ
evalT α _ˢ (V x) = α x

evalF : (Name -> Dom) -> ((σ : Signature) -> img σ) -> (φ : F) -> Bool
evalF α _ˢ (φ and φ₁)  = evalF α _ˢ φ ∧ evalF α _ˢ φ₁
evalF α _ˢ (not φ)     = ¬ evalF α _ˢ φ
evalF α _ˢ (rel p v)   = {!!}
evalF α _ˢ (x eq x₁)   with  evalT α _ˢ x ≟ evalT α _ˢ x₁
evalF α _ˢ (x eq x₁) | yes _ = true
evalF α _ˢ (x eq x₁) | no  _ = false
evalF α _ˢ (exist x φ) = evalF (α [ {!!} / x ]) _ˢ φ

