# Negational Normal Form as DAG

```
module NNF where

open import Data.Nat         using (zero; suc; _⊔_; _+_) renaming (ℕ to Nat)
open import Data.Fin         using (Fin; _<_; _≟_) renaming (toℕ to toNat)
open import Data.List        using (List; []; _∷_; _++_; map; foldr)
open import Data.Bool        using (Bool; true; false)
open import Data.Product     using (_×_; _,_; ∃-syntax; proj₁)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary  using (Decidable)
open import Data.List.Relation.Unary.Any          using (Any; any)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)


module Utils where
```

We'll need membership predicate on List (Fin n) and a decision
procedure for that predicate.

```

  _∈_ : ∀ {n} -> Fin n -> List (Fin n) -> Set _
  v ∈ vs = Any (λ x -> v ≡ x) vs

  _∈?_ : ∀ {n} -> Decidable (_∈_ {n})
  v ∈? vs = any (λ x -> v ≟ x) vs

  if_then_else_ : ∀ {A : Set} -> Bool -> A -> A -> A
  if false then _ else a₁ = a₁
  if true then a₀ else _  = a₀

  empty : ∀ {n} -> Fin n -> Bool
  empty = λ _ -> false
  
  add : ∀ {n} -> (Fin n -> Bool) -> Fin n -> Fin n -> Bool
  add f n x with n ≟ x
  add f n x | yes _ = true
  add f n x | no  _ = f x

  id : ∀ {A : Set} -> A -> A
  id a = a

  pass : ∀ {A B : Set} -> A -> B -> B
  pass _ b = b

open Utils
```

According to [1]:

  *Definition 2.1* Let PS be a denumerable set of propositional
  variables. A sentence in NNF_{PS} is a rooted, directed acyclic
  graph (DAG) where each leaf node is labeled with true, false, X or
  ¬X, X ∈ PS; and each internal node is labeled with ∧ or ∨ and can
  have arbitrarily many children. The size of a sentence Σ in NNF_{PS}
  , denoted | Σ |, is the number of its DAG edges. Its height is the
  maximum number of edges from the root to some leaf in the DAG.

So we take PS to be Nat.

```

PS = Nat

```

Then, we define the labels for internal nodes and leaves as two
different data: Connective and Atom.

```

data Connective : Set where
  and or : Connective

data Atom : Set where
  true false : Atom
  var not : PS -> Atom

```

And we define a function labelTy, that, given the list of adjacent
nodes in a DAG, computes the type of label for the vertex.

```

labelTy : ∀ {A : Set} -> List A -> Set
labelTy []      = Atom
labelTy (_ ∷ _) = Connective

```

We can now define a sentence as a record parametrized by n: Nat, the
number of vertices. Each vertex is given a number (Fin n).

```

record Sentence (n : Nat) : Set where

```

The record contains two fields:

  - a function `edges` that, given a vertex, compute the list of
    adjacents, an adjacent vertex being represented by a dependent sum
    of its number and the proof that it is greater than the first
    vertex (so we donc have cycle in the graph).

  - a function `label` that relates each vertex to a label of the
    right type (accordingly to the fact that it is an internal vertex
    or a leaf.


```

  field
    edges : (v : Fin n) -> List (∃[ x ] (v < x))
    label : (v : Fin n) -> labelTy (edges v)

```

These two fields are enough to define a sentence in NNF. We then add
some other functions.

  - a function `next` that, given a vertex, computes the list of its
    adjacents.

```

  next : Fin n -> List (Fin n)
  next v = map proj₁ (edges v)

```

We will want to fold a DAG. We define a fold that traverse the DAG
depth first.

Folding needs two functions to operate:

  - f that takes a vertex and the accumulator and return a new accumulator
    this function is called on each vertex.
  - g that takes that takes two accumulators and return a new accumulator
    this function is called and each adjacent of a vertex and correspond
    to the depth-first search.

Then, we'll need to keep track of the vertices that has been already
visited. This is done by the function h.

To define folding, we need to put in place a mutual recursion between
the treatment of a vertex and the treatment of the list of the
adjacent vertices of a vertex.

```

  private
    mutual

```

The mutual recursion works as follow:

  - dag-fold' check whether the vertex has already been visited, and
    if not call dag-fold-aux with the list of adjacent vertices, an
    updated function h and an updated accumulator.

```

      dag-foldr' : ∀ {A : Set}
                  -> Nat
                  -> (Fin n -> A -> A)
                  -> (A -> A -> A)
                  -> (Fin n -> Bool)
                  -> A
                  -> Fin n
                  -> A × (Fin n -> Bool)
      dag-foldr' zero f g h acc v      = acc , h
      dag-foldr' (suc gas) f g h acc v =
        if h v then acc , h else dag-foldr-aux gas f g (add h v) (f v acc) (next v)

```

  - dag-fold-aux call dag-fold' on each of the adjacent vertices,
    keeping track of the already visited vertices and accumulator


```

      dag-foldr-aux : ∀ {A : Set}       
                      -> Nat               
                      -> (Fin n -> A -> A) 
                      -> (A -> A -> A)     
                      -> (Fin n -> Bool)   
                      -> A                 
                      -> List (Fin n)      
                      -> A × (Fin n -> Bool)
      dag-foldr-aux zero _ _ h acc _             = acc , h
      dag-foldr-aux (suc _) f g h acc []         = acc , h
      dag-foldr-aux (suc gas) f g h acc (v ∷ vs) with dag-foldr' (suc gas) f g h acc v
      dag-foldr-aux (suc gas) f g h acc (v ∷ vs) | a , h' =
        dag-foldr-aux gas f g h' (g a acc) vs

```

As the terminaison checker need some assurances that the mutual
recursion eventually terminates, we add some gas to each of these
functions to convince him. Then, we define dag-foldr as dag-foldr'
with the number of vertices as gas and an empty set of visited
vertices.
    
```

  dag-foldr : ∀ {A : Set} -> (Fin n -> A -> A) -> (A -> A -> A) -> A -> Fin n -> A
  dag-foldr f g a v = proj₁ (dag-foldr' n f g empty a v)

```

Then, depth-first search is defined as dag-foldr with the list
constructor as f, concatenation as g and the empty list as
accumulator.

```

  dfs : Fin n -> List (Fin n)
  dfs v = dag-foldr _∷_ _++_ [] v

```

The size of a sentence is the number of edges and can be defined with
the help of dag-foldr:

  - when we encounter a vertex, we pass

  - when we look at an adjacent vertex, we take the successor of the
    result and add 1

```

  size : Fin n -> Nat
  size v = dag-foldr pass (λ a acc -> suc a + acc) zero v

```

The height of a sentence is the length of the longest path to a leaf.

  - as in the size function, when we encounter a vertex we pass

  - when we look at an adjacent vertex, we add one to the result and
    take the max between that and the accumulator
    
```

  height : Fin n -> Nat
  height v = dag-foldr pass (λ a acc -> (suc a) ⊔ acc) zero v

     


open Sentence
```


[1]A. Darwiche et P. Marquis, « A Knowledge Compilation Map », jair, vol. 17, p. 229‑264, sept. 2002, doi: 10.1613/jair.989.
