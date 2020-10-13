# Propositional Logic

```
module Propositional-Logic where

open import Data.Nat using () renaming (ℕ to Nat)
open import Data.Fin using (Fin)
open import Data.Bool using (Bool; true; false; _∧_) renaming (not to ¬_)

infix 10  not_
infix 9 _and_
infix 8  _or_
infix 7  _impl_
  
```

We give ourselves an infinite set of variable names

```
Name = Nat

```

Conjunction and negation are a complete subset of connectives.
We then can define disjunction and implication as derived form.

```
data F : Set where
  C : Bool -> F
  V : Name   -> F
  _and_ : F -> F -> F
  not_  : F -> F

_or_ : F -> F -> F
φ₀ or φ₁ = not (not φ₀ and not φ₁)

_impl_ : F -> F -> F
φ₀ impl φ₁ = not φ₀ or φ₁

```

We define evaluation wrt an assignation function

```
eval : (Name -> Bool) -> F -> Bool
eval α (C b)       = b
eval α (V n)       = α n
eval α (F₁ and F₂) = eval α F₁ ∧ eval α F₂
eval α (not F₁)    = ¬ eval α F₁

