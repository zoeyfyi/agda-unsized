{-# OPTIONS --without-K --safe --guardedness #-}

module Unsized.Codata.Stream.Relation.Unary.Linked.Properties where

open import Level
open import Relation.Binary using (Rel; _⇒_)
open import Relation.Binary.PropositionalEquality
open import Relation.Unary using (_⊆_)
open import Unsized.Codata.Stream 
open import Unsized.Codata.Stream.Relation.Unary.Linked

private
  variable
    a ℓ ℓ₁ : Level
    A : Set a

------------------------------------------------------------------------
-- iterate

iterate-linked : ∀ {f : A → A} {a : A} → Linked (λ x y → y ≡ f x) (iterate f a)
hd iterate-linked = refl
tl iterate-linked = iterate-linked
