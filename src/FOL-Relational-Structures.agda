module FOL-Relational-Structures where

open import Data.Nat using () renaming (ℕ to Nat)
open import Data.Vec using (Vec; map)
open import Data.Bool using (Bool; true; false; _∧_) renaming (not to ¬_)

infix 10 not_
infix 9 _and_
infix 8 _or_ _∈_

postulate
  Dom   : Nat -> Set
  _≟ᵈ_   : (a : Dom 0) -> (b : Dom 0) -> Bool
  Pred  : Nat -> Set
  _∈_   : ∀ {n} -> Vec (Dom 0) n -> Dom n ->  Bool  
  Const : Set
  Name  : Set
  _≟ⁿ_  : Name -> Name -> Bool

data Σ : Set where
  left : Const -> Σ
  right : ∀ {n} -> Pred n -> Σ

img : Σ -> Set
img (left _)      = Dom 0
img (right {n} _) = Dom n

data T : Set where
  C : Const -> T
  V : Name -> T

data F  : Set where
  _and_ : F -> F -> F
  not_  : F -> F
  rel   : ∀ {n} -> Pred n -> Vec T n -> F
  _eq_  : T -> T -> F
  exist : Name -> F -> F

_or_ : F -> F -> F
φ₀ or φ₁ = not (not φ₀ and not φ₁)

_impl_ : F -> F -> F
φ₀ impl φ₁ = not φ₀ or φ₁

universal : Name -> F -> F
universal n φ = not (exist n (not φ))

_[_/_] : (Name -> Dom 0) -> Dom 0 -> Name -> (Name -> Dom 0)
(α [ d / x ]) n with n ≟ⁿ x
(α [ d / x ]) n | false = α n
(α [ d / x ]) n | true  = d

evalT : (Name -> Dom 0) -> ((σ : Σ) -> img σ) -> (τ : T) -> Dom 0
evalT α _ˢ (C c) = left c ˢ
evalT α _ˢ (V x) = α x

evalF : (Name -> Dom 0) -> ((σ : Σ) -> img σ) -> (φ : F) -> Bool
evalF α _ˢ (φ and φ₁)  = evalF α _ˢ φ ∧ evalF α _ˢ φ₁
evalF α _ˢ (not φ)     = ¬ evalF α _ˢ φ
evalF α _ˢ (rel p v)   = map (evalT α _ˢ) v ∈ right p ˢ
evalF α _ˢ (x eq x₁)   = evalT α _ˢ x ≟ᵈ evalT α _ˢ x₁
evalF α _ˢ (exist x φ) = evalF (α [ {!!} / x ]) _ˢ φ
