{-# OPTIONS --safe --without-K --guardedness #-}

module Unsized.Codata.Stream.Relation.Unary.Any where

open import Level using (Level; _⊔_)
open import Relation.Binary using (Rel; _⇒_)
open import Relation.Unary using (Pred; _⊆_)
open import Data.Nat using (ℕ; suc; zero)
open import Unsized.Codata.Stream using (Stream; _∷_; hd; tl) 

private
  variable
    a ℓ ℓ₁ : Level
    A : Set a
    P Q : Pred A ℓ
    xs : Stream A

-- record Any {a ℓ} {A : Set a} (P : Pred A ℓ) (xs : Stream A) : Set (a ⊔ ℓ) where
--   coinductive
--   field
--     here : 

data Any {a ℓ} {A : Set a} (P : Pred A ℓ) (xs : Stream A) : Set (ℓ ⊔ a) where
  here : P (hd xs) → Any P xs
  there : Any P (tl xs) → Any P xs

map : P ⊆ Q → Any P xs → Any Q xs 
map P⊆Q (here px) = here (P⊆Q px)
map P⊆Q (there x) = there (map P⊆Q x)

index : Any P xs → ℕ
index (here _) = zero
index (there x) = suc (index x)

lookup : ∀ {xs : Stream A} → Any P xs → A
lookup {xs = xs} (here x) = hd xs
lookup (there x) = lookup x
