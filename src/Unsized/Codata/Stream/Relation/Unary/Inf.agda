{-# OPTIONS --safe --without-K --guardedness #-}

module Unsized.Codata.Stream.Relation.Unary.Inf where

open import Level using (Level; _⊔_)
open import Relation.Binary using (Rel; _⇒_)
open import Relation.Unary using (Pred; _⊆_)
open import Data.Nat using (ℕ; suc; zero)
open import Unsized.Codata.Stream using (Stream; _∷_; hd; tl) 
open import Unsized.Codata.Stream.Relation.Unary.Any as Any using (Any) 

private
  variable
    a ℓ ℓ₁ : Level
    A : Set a
    P Q : Pred A ℓ
    xs : Stream A

record Inf {a ℓ} {A : Set a} (P : Pred A ℓ) (xs : Stream A) : Set (a ⊔ ℓ) where
  coinductive
  field
    here : Any P xs
    there : Inf P (tl xs)
open Inf public

map : P ⊆ Q → Inf P xs → Inf Q xs
here (map P⊆Q x) = Any.map P⊆Q (here x)
there (map P⊆Q x) = map P⊆Q (there x)
