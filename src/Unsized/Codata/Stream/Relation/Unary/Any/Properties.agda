{-# OPTIONS --safe --without-K --guardedness #-}

module Unsized.Codata.Stream.Relation.Unary.Any.Properties where

open import Level using (Level; _⊔_)
open import Relation.Binary using (Rel; _⇒_)
open import Relation.Unary using (Pred; _⊆_)
open import Data.Nat using (ℕ; suc; zero)
open import Unsized.Codata.Stream using (Stream; _∷_; hd; tl; lookup) 
import Unsized.Codata.Stream.Relation.Unary.Any as Any
open import Unsized.Codata.Stream.Relation.Unary.Any using (Any; here; there)

private
  variable
    a ℓ ℓ₁ : Level
    A : Set a
    P Q : Pred A ℓ
    xs : Stream A
    
------------------------------------------------------------------------
-- Any.lookup

lookup-result : ∀ (p : Any P xs) → P (Any.lookup p)
lookup-result (here px) = px
lookup-result (there p) = lookup-result p

lookup-index : ∀ (p :  Any P xs) → P (lookup (Any.index p) xs)
lookup-index (here px) = px
lookup-index (there p) = lookup-index p
