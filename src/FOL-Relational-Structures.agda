module FOL-Relational-Structures where

open import Data.Nat         using (zero; suc; _<_; _≤_; _∸_) renaming (ℕ to Nat; _≟_ to _≟ⁿ_)
open import Data.Fin         using (Fin; toℕ; fromℕ<; fromℕ) renaming (_≟_ to _≟ᶠ_; zero to zeroᶠ; suc to sucᶠ)
open import Data.List        using (List; []; _∷_; foldr)
open import Data.List.Membership.DecSetoid
open import Data.Vec         using (Vec; map)
open import Data.Bool        using (Bool; true; false; _∧_; _∨_) renaming (not to ¬_)
open import Data.Sum         using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
open import Data.Vec.Relation.Binary.Equality.DecSetoid

module M (consts : Nat) (rels : Nat) (ar : Fin rels -> Nat) where

  infix 10  not_
  infix 9 _and_
  infix 8  _or_
  infix 7  _impl_

  Consts = Fin consts
  Rels   = Fin rels
  
  Signature = Consts ⊎ Rels

  img : Nat -> Signature -> Set
  img d (inj₁ c) = Fin d
  img d (inj₂ r) = List (Vec (Fin d) (ar r))

  record Structure : Set where
    field
      dom : Nat
      ˢ   : (σ : Signature) -> img (suc dom) σ
  open Structure

  card : Structure -> Nat
  card s = suc (dom s)
  
  Name = Nat
  
  data T : Set where
    C : Consts -> T
    V : Name -> T

  data F : Set where
    rel    : (r : Rels) -> Vec T (ar r) -> F
    _and_  : F -> F -> F
    _eq_   : T -> T -> F
    not_   : F -> F
    exists : Name -> F -> F

  _or_ : F -> F -> F
  φ₀ or φ₁ = not (not φ₀ and not φ₁)

  _impl_ : F -> F -> F
  φ₀ impl φ₁ = not φ₀ or φ₁

  universal : Name -> F -> F
  universal n φ = not (exists n (not φ))

  [_]_[_/_] : (S : Structure) -> (Name -> Fin (card S)) -> Fin (card S) -> Name -> (Name -> Fin (card S))
  ([ s ] α [ d / x ]) n with n ≟ⁿ x
  ([ s ] α [ d / x ]) n | yes _ = d
  ([ s ] α [ d / x ]) n | no  _ = α n

  evalT : (S : Structure) -> (Name -> Fin (card S)) -> T -> Fin (card S)
  evalT s α (C c) = ˢ s (inj₁ c)
  evalT s α (V n) = α n

  postulate
    _≟ⱽ_ : ∀ {n m} -> (v : Vec (Fin n) m) -> (v₁ : Vec (Fin n) m) -> Dec (v ≡ v₁)

  _in?_ : ∀ {m n} -> Vec (Fin n) m -> List (Vec (Fin n) m) -> Bool
  v in? [] = false
  v in? (x ∷ l) with v ≟ⱽ x
  v in? (x ∷ l) | yes _ = true
  v in? (x ∷ l) | no  _ = v in? l
  
  exist? : ∀ {n} -> Fin n -> (Nat -> Bool) -> Bool
  exist? zeroᶠ P    = P zero
  exist? (sucᶠ n) P = P (suc (toℕ n)) ∨ (exist? n P)

  postulate
    pred< : ∀ {m n} -> suc m < n -> m < n
  
  toList : ∀ {m} -> (n : Nat) -> n < m -> List (Fin m) -> List (Fin m)
  toList {m} zero p acc    = fromℕ< p ∷ acc 
  toList {m} (suc n) p acc = toList n (pred< p) (fromℕ< p ∷ acc)

  postulate
    n<sn : (n : Nat) -> n < suc n

  getDom : (s : Structure) -> List (Fin (card s))
  getDom s = toList {card s} (dom s) (n<sn (dom s)) []
  
  evalF : (S : Structure) -> (Name -> Fin (card S)) -> F -> Bool
  evalF s α (rel r x)         = map (evalT s α) x in? (ˢ s (inj₂ r)) 
  evalF s α (f and f₁)        = evalF s α f ∧ evalF s α f₁
  evalF s α (τ eq τ₁) with evalT s α τ ≟ᶠ evalT s α τ₁
  evalF s α (τ eq τ₁) | yes _ = true
  evalF s α (τ eq τ₁) | no  _ = false  
  evalF s α (not f)           = ¬ evalF s α f
  evalF s α (exists n f)      = foldr (λ x y -> y ∨ evalF s ([ s ] α [ x / n ]) f) false (getDom s)
