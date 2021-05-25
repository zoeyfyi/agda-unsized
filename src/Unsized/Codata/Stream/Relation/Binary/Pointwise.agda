{-# OPTIONS --without-K --safe --guardedness #-}

module Unsized.Codata.Stream.Relation.Binary.Pointwise where

open import Data.List.NonEmpty using (List⁺)
open import Data.List using (List)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans)
open import Function.Base
open import Unsized.Codata.Stream
open import Level using (_⊔_)

record Pointwise {a ℓ} {A : Set a} (R : Rel A ℓ) (xs : Stream A) (ys : Stream A) : Set (a ⊔ ℓ) where
  coinductive
  field
    hd : R (hd xs) (hd ys)
    tl : Pointwise R (tl xs) (tl ys)
open Pointwise public
