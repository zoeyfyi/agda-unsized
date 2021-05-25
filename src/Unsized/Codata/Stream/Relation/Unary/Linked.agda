{-# OPTIONS --without-K --safe --guardedness #-}

module Unsized.Codata.Stream.Relation.Unary.Linked where

open import Level
open import Relation.Binary using (Rel; _⇒_)
open import Relation.Unary using (_⊆_)
open import Unsized.Codata.Stream using (Stream; _∷_; hd; tl) 

private
  variable
    a ℓ ℓ₁ : Level
    A : Set a

record Linked {a ℓ} {A : Set a} (R : Rel A ℓ) (xs : Stream A) : Set (a ⊔ ℓ) where
  constructor _∷_
  coinductive
  field
    hd : R (hd xs) (hd (tl xs))
    tl : Linked R (tl xs)
open Linked public

module _ {R : Rel A ℓ} {S : Rel A ℓ₁} where

  map : R ⇒ S → Linked R ⊆ Linked S
  hd (map R⇒S x) = R⇒S (hd x)
  tl (map R⇒S x) = map R⇒S (tl x)

