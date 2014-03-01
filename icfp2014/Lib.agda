module Lib where

open import Data.Nat public hiding (_<_) 
open import Function public using (_∘_)
open import Data.List public 
open import Data.Product public using (_×_ ; _,_ ; proj₁ ; proj₂ ; Σ ; ∃)
open import Data.Sum public using (_⊎_ ; [_,_]′ ; inj₁ ; inj₂)
open import Relation.Nullary public
open import Relation.Binary.PropositionalEquality public hiding ([_])

open import Category.Functor public

-- Pointer into a list. It is similar to list membership as defined in
-- Data.List.AnyMembership, rather than going through propositional
-- equality, it asserts the existence of the referenced element
-- directly.
infix 4 _∈_
data _∈_ {A : Set} : A → List A → Set where
  hd : ∀ {x xs} → x ∈ (x ∷ xs)
  tl : ∀ {x y xs} → x ∈ xs → x ∈ (y ∷ xs)

mapIdx : {A B : Set} → (f : A → B) →
         {x : A} {xs : List A} → x ∈ xs → f x ∈ map f xs
mapIdx f hd = hd
mapIdx f (tl x₁) = tl (mapIdx f x₁)

