{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Unsized.Data.Tree.Rose.Membership.Setoid {c ℓ} (S : Setoid c ℓ) where

open import Level
open import Data.Product as Prod using (∃; _×_; _,_)
open import Relation.Nullary using (¬_)
open import Relation.Unary using (Pred)
open import Function.Base using (_∘_; id; flip)
open import Unsized.Data.Tree.Rose using (Rose)
open import Unsized.Data.Tree.Rose.Relation.Unary.Any

open Setoid S renaming (Carrier to A)

------------------------------------------------------------------------
-- Definitions

infix 4 _∈_ _∉_

_∈_ : A → Rose A → Set _
x ∈ xs = Any (x ≈_) xs

_∉_ : A → Rose A → Set _
x ∉ xs = ¬ x ∈ xs

------------------------------------------------------------------------
-- Finding and losing witnesses

module _ {p} {P : Pred A p} where

  find : ∀ {xs} → Any P xs → ∃ λ x → x ∈ xs × P x
  find (here px) = _ , here refl , px
  find (there t∈cs pxs) = Prod.map id (Prod.map (there t∈cs) id) (find pxs)
  
  lose : P Respects _≈_ →  ∀ {x ts} → x ∈ ts → P x → Any P ts
  lose resp x∈ts px = map (flip resp px) x∈ts
