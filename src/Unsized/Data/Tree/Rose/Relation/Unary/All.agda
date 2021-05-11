{-# OPTIONS --without-K --safe #-}

module Unsized.Data.Tree.Rose.Relation.Unary.All where

open import Level
open import Relation.Nullary as Dec
open import Relation.Unary using (Pred; _⊆_; Decidable; Satisfiable)
import Relation.Nullary.Decidable.Core as Dec
open import Unsized.Data.Tree.Rose using (Rose; node)
open import Data.List using (List; _∷_; [])
open import Data.List.Membership.Propositional
import Data.List.Relation.Unary.All as List
open import Data.Product using (∃; _,_)

private
  variable
    ℓ ℓ₁ : Level
    A : Set ℓ
    P Q : Pred A ℓ₁
    t : Rose A
    
data All {A : Set ℓ} (P : Pred A ℓ₁) : Pred (Rose A) (ℓ ⊔ ℓ₁) where
  node : ∀ {r cs} → P r → List.All (All P) cs → All P (node r cs)

map : P ⊆ Q → All P t → All Q t
map' : ∀ {ts : List (Rose A)} → P ⊆ Q → List.All (All P) ts → List.All (All Q) ts
map' g List.[] = List.[]
map' g (px List.∷ ts) = map g px List.∷ map' g ts
map g (node x x₁) = node (g x) (map' g x₁)
