# Negational Normal Form as DAG

```
module NNF where

open import Data.Nat using (zero; suc; _⊔_; _+_; _≤_) renaming (ℕ to Nat; _<_ to _<ᴺ_)
open import Data.Fin using (Fin; _≟_; toℕ; fromℕ<) renaming (zero to zeroᶠ; _<_ to _<ᶠ_)
open import Data.Unit using (⊤)
open import Data.Bool using (Bool; true; false) renaming (not to notᵇ)
open import Data.List using (List; []; _∷_; _++_; map) renaming (and to f-and; or to f-or)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; ∃-syntax; proj₁)
open import Relation.Binary using (Decidable)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Nat.Properties using (_<?_; _≤?_)
open import Relation.Nullary.Decidable using (map′)
open import Data.List.Relation.Unary.Any using (Any; any)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; setoid)
open import Data.List.Membership.Setoid (setoid Nat) using (_∈_)
open import Data.List.Relation.Unary.Unique.Setoid (setoid Nat) using (Unique)
open import Data.List.Relation.Binary.Disjoint.Setoid (setoid Nat) using (Disjoint)


module Utils where
```

We'll need some utility functions.

```

  same-vars : List Nat -> List Nat -> Set
  same-vars l₀ l₁ = All (λ x -> x ∈ l₁) l₀ × All (λ x -> x ∈ l₀) l₁

  if_then_else_ : ∀ {A : Set} -> Bool -> A -> A -> A
  if false then _ else a₁ = a₁
  if true then a₀ else _  = a₀

  empty : ∀ {n} -> Fin n -> Bool
  empty = λ _ -> false
  
  add : ∀ {n} -> (Fin n -> Bool) -> Fin n -> Fin n -> Bool
  add f n x with n ≟ x
  add f n x | yes _ = true
  add f n x | no  _ = f x

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

data LabelBox : Set where
  at : Atom -> LabelBox
  co : Connective -> LabelBox

mkBox : ∀ {A}{l : List A} -> labelTy l -> LabelBox
mkBox {A} {[]} lab = at lab
mkBox {A} {x ∷ l} lab = co lab

```

We now define a NNF sentence as a record. 

```

record NNF : Set where

```

The record contains three fields:

  - n : Nat the number of vertices in the DAG, each vertex is then
    represented by a Fin n
    
  - a function `edges` that, given a vertex, compute the list of
    adjacents, an adjacent vertex being represented by a dependent sum
    of its number and the proof that it is greater than the first
    vertex (so we donc have cycle in the graph).

  - a function `label` that relates each vertex to a label of the
    right type (accordingly to the fact that it is an internal vertex
    or a leaf.

```

  field
    n     : Nat
    edges : (v : Fin n) -> List (∃[ x ] (v <ᶠ x))
    label : (v : Fin n) -> labelTy (edges v)

```

These three fields are enough to define a sentence in NNF. We then add
some other functions.

  - a function `next` that, given a vertex, computes the list of its
    adjacents.

```

  next : Fin n -> List (Fin n)
  next v = map proj₁ (edges v)

  is-disjunction : (v : Fin n) -> Set
  is-disjunction v = is-disjunction-aux (label v)
    where
      is-disjunction-aux : {A : Set}{c : List A} -> labelTy c -> Set
      is-disjunction-aux {_} {[]} l = ⊥
      is-disjunction-aux {_} {x ∷ _} and = ⊥
      is-disjunction-aux {_} {x ∷ _} or = ⊤

  is-conjunction : (v : Fin n) -> Set
  is-conjunction v = is-conjunction-aux (label v)
    where
      is-conjunction-aux : {A : Set}{c : List A} -> labelTy c -> Set
      is-conjunction-aux {_} {[]} l = ⊥
      is-conjunction-aux {_} {x ∷ _} and = ⊤
      is-conjunction-aux {_} {x ∷ _} or = ⊥

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

  dfs-next-toℕ : Fin n -> List (List Nat)
  dfs-next-toℕ v = map (map toℕ) (map dfs (next v))
  
```

The size of a sentence is the number of edges and can be defined with
the help of dag-foldr:

  - when we encounter a vertex, we pass

  - when we look at an adjacent vertex, we take the successor of the
    result and add 1

```

  size : Fin n -> Nat
  size v = dag-foldr pass (λ a acc -> suc a + acc) zero v

  size-root : Nat
  size-root with 0 <? n
  ... | yes p = size (fromℕ< p)
  ... | no ¬p = zero
```

The height of a sentence is the length of the longest path to a leaf.

  - as in the size function, when we encounter a vertex we pass

  - when we look at an adjacent vertex, we add one to the result and
    take the max between that and the accumulator
    
```

  height : Fin n -> Nat
  height v = dag-foldr pass (λ a acc -> (suc a) ⊔ acc) zero v

  height-root : Nat
  height-root with 0 <? n
  ... | yes p  = height (fromℕ< p)
  ... | no  ¬p = zero


  
open NNF

eval-sub-graph : Nat -> (Σ : NNF) -> (PS -> Bool) -> Fin (n Σ) -> Bool
eval-sub-graph zero _ _ _ = false
eval-sub-graph (suc gas) Σ α v with mkBox (label Σ v)
... | at true    = true
... | at false   = false
... | at (var x) = α x
... | at (not x) = notᵇ (α x)
... | co and     = f-and (map (eval-sub-graph gas Σ α) (next Σ v))
... | co or      = f-or (map (eval-sub-graph gas Σ α) (next Σ v))

contradictory : (Σ : NNF) ->  Fin (n Σ) -> Fin (n Σ) -> Set
contradictory Σ v₀ v₁ = ∀ {α : PS -> Bool} -> eval-sub-graph (height Σ v₀) Σ α v₀ ≢ eval-sub-graph (height Σ v₁) Σ α v₁

flatness : NNF -> Set
flatness Σ = (height-root Σ) ≤ 2

flat?' : (Σ : NNF) -> Dec (flatness Σ)
flat?' Σ = height-root Σ ≤? 2

simple-disjunction : NNF -> Set
simple-disjunction Σ = ∀ (v : Fin (n Σ)) -> is-disjunction Σ v -> height Σ v ≡ 1 × Unique (map toℕ (next Σ v))

simple-conjunction : NNF -> Set
simple-conjunction Σ = ∀ (v : Fin (n Σ)) -> is-conjunction Σ v -> height Σ v ≡ 1 × Unique (map toℕ (next Σ v))

record f-NNF : Set where
  field
    nnf   : NNF
    f-nnf : flatness nnf
open f-NNF

record CNF : Set where
  field
    f-nnf : f-NNF
    cnf   : simple-disjunction (nnf f-nnf)
open CNF

record DNF : Set where
  field
    f-nnf : f-NNF
    dnf   : simple-conjunction (nnf f-nnf)
open DNF

decomposability : NNF -> Set
decomposability Σ = ∀ (v : Fin (n Σ)) -> is-conjunction Σ v -> decomposable Σ v
  where
    decomposable : (Σ : NNF) -> Fin (n Σ) -> Set
    decomposable Σ v = AllPairs Disjoint (dfs-next-toℕ Σ v)

determinism : NNF -> Set
determinism Σ = ∀ (v : Fin (n Σ)) -> is-disjunction Σ v -> deterministic Σ v
  where
    deterministic : (Σ : NNF) -> Fin (n Σ) -> Set
    deterministic Σ v = AllPairs (contradictory Σ) (next Σ v) 

smoothness : NNF -> Set
smoothness Σ = ∀ (v : Fin (n Σ)) -> is-disjunction Σ v -> smooth Σ v
  where
    smooth : (Σ : NNF) -> Fin (n Σ) -> Set
    smooth Σ v = AllPairs same-vars (dfs-next-toℕ Σ v)

```

[1]A. Darwiche et P. Marquis, « A Knowledge Compilation Map », jair, vol. 17, p. 229‑264, sept. 2002, doi: 10.1613/jair.989.
