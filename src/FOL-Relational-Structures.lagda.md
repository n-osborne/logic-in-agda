# First Order Logic with equality for relational structures

```
module FOL-Relational-Structures where

open import Data.Nat         using (zero; suc; _<_; _≤_) renaming (ℕ to Nat; _≟_ to _≟ⁿ_)
open import Data.Fin         using (Fin; fromℕ<) renaming (_≟_ to _≟ᶠ_)
open import Data.List        using (List; []; _∷_; foldr)
open import Data.Vec         using (Vec; map)
open import Data.Bool        using (Bool; true; false; _∧_; _∨_) renaming (not to ¬_)
open import Data.Sum         using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
```

We want to work in a context where we have a finite set of constant
symbols, a finite set of relation symbols and a function that gives an
arity to each of these relation symbols. In order to do so, we work in
a module parametrized by the cardinal of the set of constants, the
cardinal of the set of relations and the function that assigns an arity
to the relation symbols.

```
module M (consts : Nat) (rels : Nat) (ar : Fin rels -> Nat) where
```

We then define some priority levels for the FOL.

```
  infix 10  not_
  infix 9 _and_
  infix 8  _or_
  infix 7  _impl_
```

## Signature

Now we define the sets of constant and relation symbols as finite set
of the given cardinality. A Signature is the union of these two finite
sets.

```
  Consts    = Fin consts
  Rels      = Fin rels
  Signature = Consts ⊎ Rels
```

## Syntax

We also give ourselves an infinite set of names for the variables.

```
  Name = Nat
```

We can now define the syntax of the FOL with equality. We first define the
terms, which can be constants or variables, and then formulaes.

```
  data T : Set where
    C : Consts -> T
    V : Name -> T

  data F : Set where
    rel    : (r : Rels) -> Vec T (ar r) -> F
    _and_  : F -> F -> F
    _eq_   : T -> T -> F
    not_   : F -> F
    exists : Name -> F -> F
```

Disjunction, implication and universal quantification are derived forms.

```
  _or_ : F -> F -> F
  φ₀ or φ₁ = not (not φ₀ and not φ₁)

  _impl_ : F -> F -> F
  φ₀ impl φ₁ = not φ₀ or φ₁

  universal : Name -> F -> F
  universal n φ = not (exists n (not φ))
```

## Semantic

We can now turn to the definition of the semantic. We'll need to
compute the type of the interpretation of the symbols in the Signature
according to the cardinal of the domain in which we interprete the
symbols.

```
  img : Nat -> Signature -> Set
  img d (inj₁ c) = Fin d
  img d (inj₂ r) = List (Vec (Fin d) (ar r))
```

We define a structure by a natural, the one that denotes the last
element of the domain if we give a number to each one of them, and
the function ˢ that interprets the symbols in the domain.

```
  record Structure : Set where
    field
      dom : Nat
      ˢ   : (σ : Signature) -> img (suc dom) σ
  open Structure
```

The cardinal of the domain is the successor of the natural used to
define the Structure. We'll need this difference when we'll construct
the list of all the elements of the domain in order to evaluate
existential formulas.

```
  card : Structure -> Nat
  card s = suc (dom s)
```

Then, we define substitution in the assignation function. An
assignation function maps names to elements of the
domain. Substitution adds one name and one element of the domain to a
previous mapping. This again is used in the evaluation of the
existential formulas.


```
  [_]_[_/_] : (S : Structure) -> (Name -> Fin (card S)) -> Fin (card S) -> Name -> (Name -> Fin (card S))
  ([ s ] α [ d / x ]) n with n ≟ⁿ x
  ([ s ] α [ d / x ]) n | yes _ = d
  ([ s ] α [ d / x ]) n | no  _ = α n
```

We will need to check whether a tuple of elements is in a list of
tuple. We give oursalves some trivial postulate about tuple decidable
equality and ordering relation that should disapear once I find my
way in agda standard library.

```
  postulate
    _≟ⱽ_ : ∀ {n m} -> (v : Vec (Fin n) m) -> (v₁ : Vec (Fin n) m) -> Dec (v ≡ v₁)

  _∈?_ : ∀ {m n} -> Vec (Fin n) m -> List (Vec (Fin n) m) -> Bool
  v ∈? [] = false
  v ∈? (x ∷ l) with v ≟ⱽ x
  v ∈? (x ∷ l) | yes _ = true
  v ∈? (x ∷ l) | no  _ = v ∈? l
```

And we will also need to build the list of all the elements of the
domain of a structure.

```
  postulate
    pred< : ∀ {m n} -> suc m < n -> m < n
  
  toList : ∀ {m} -> (n : Nat) -> n < m -> List (Fin m) -> List (Fin m)
  toList {m} zero p acc    = fromℕ< p ∷ acc 
  toList {m} (suc n) p acc = toList n (pred< p) (fromℕ< p ∷ acc)

  getDom : (s : Structure) -> List (Fin (card s))
  getDom s = toList {card s} (dom s) (n<sn (dom s)) []
    where
      n<sn : (n : Nat) -> n < suc n
      n<sn zero    = _≤_.s≤s _≤_.z≤n
      n<sn (suc n) = _≤_.s≤s (n<sn n)

```

Now we have all we need to express the evaluation function, first for
terms, and then for formulas.

```
  evalT : (S : Structure) -> (Name -> Fin (card S)) -> T -> Fin (card S)
  evalT s α (C c) = ˢ s (inj₁ c)
  evalT s α (V n) = α n

  evalF : (S : Structure) -> (Name -> Fin (card S)) -> F -> Bool
  evalF s α (rel r x)         = map (evalT s α) x ∈? (ˢ s (inj₂ r)) 
  evalF s α (f and f₁)        = evalF s α f ∧ evalF s α f₁
  evalF s α (τ eq τ₁) with evalT s α τ ≟ᶠ evalT s α τ₁
  evalF s α (τ eq τ₁) | yes _ = true
  evalF s α (τ eq τ₁) | no  _ = false  
  evalF s α (not f)           = ¬ evalF s α f
  evalF s α (exists n f)      = foldr (λ x y -> y ∨ evalF s ([ s ] α [ x / n ]) f) false (getDom s)
```
