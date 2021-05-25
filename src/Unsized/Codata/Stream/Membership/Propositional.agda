{-# OPTIONS --without-K --safe --guardedness #-}

module Unsized.Codata.Stream.Membership.Propositional where

open import Level
open import Unsized.Codata.Stream
open import Unsized.Codata.Stream.Relation.Unary.Any
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)

private
  variable
    a : Level
    A : Set a

_∈_ : A → Stream A → Set _
x ∈ xs = Any (x ≡_) xs

_∉_ : A → Stream A → Set _
x ∉ xs = ¬ (x ∈ xs)
