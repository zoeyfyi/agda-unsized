{-# OPTIONS --without-K --safe #-}

module Unsized.Data.Tree.Rose where

open import Data.Bool
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; _?∷_)
import Data.List as List
open import Data.List.Extrema.Nat using (max)
open import Level using (Level)
open import Data.Nat
open import Relation.Nullary
open import Relation.Unary

private
  variable
    ℓ : Level
    A B C : Set ℓ

record Rose {ℓ} (A : Set ℓ) : Set ℓ
Forest : Set ℓ → Set ℓ
Forest A = List (Rose A)

record Rose A where
  constructor node
  inductive
  field
    root : A
    children : Forest A
  
open Rose public

leaf : A → Rose A
leaf a = node a []

leaves : List A → Forest A
leaves [] = []
leaves (a ∷ as) = (leaf a) ∷ (leaves as)

map : (A → B) → Rose A → Rose B
map' : (A → B) → Forest A → Forest B
map f (node root₁ children₁) = node (f root₁) (map' f children₁)
map' f [] = []
map' f (x ∷ a) = map f x ∷ map' f a

foldr : (A → List B → B) → Rose A → B
foldr' : (A → List B → B) → Forest A → List B
foldr n (node r cs) = n r (foldr' n cs)
foldr' n [] = []
foldr' n (x ∷ t) = foldr n x ∷ (foldr' n t)

depth : Rose A → ℕ
depth' : Forest A → ℕ
depth (node root₁ children₁) = suc (depth' children₁)
depth' [] = 0
depth' (x ∷ ns) = (depth x) ⊔ (depth' ns)

nodes : Rose A → ℕ
nodes' : Forest A → ℕ
nodes (node root₁ children₁) = suc (nodes' children₁)
nodes' [] = 0
nodes' (x ∷ ns) = nodes x + nodes' ns

module _ {P : Pred A ℓ} (P? : Decidable P) where

  filter : Rose A → Maybe (Rose A)
  filter' : Forest A → Forest A

  filter (node root₁ children₁) = if does (P? root₁) 
    then just (node root₁ (filter' children₁)) 
    else nothing

  filter' [] = []
  filter' (t@(node root₁ children₁) ∷ ts) = if does (P? root₁)
    then filter t ?∷ filter' ts
    else filter' ts
  
  filterChildren : Rose A → Rose A
  filterChildren (node root₁ children₁) = node root₁ (filter' children₁)

flatten : Rose A → List A
flatten' : Forest A → List A
flatten' [] = []
flatten' (t ∷ ts) = (flatten t) List.++ (flatten' ts)
flatten (node root₁ children₁) = root₁ ∷ flatten' children₁