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

roots : Forest A → List A
roots = List.map root

leaf : A → Rose A
leaf a = node a []

leaves : List A → Forest A
leaves [] = []
leaves (a ∷ as) = (leaf a) ∷ (leaves as)

map : (A → B) → Rose A → Rose B
mapᶠ : (A → B) → Forest A → Forest B
map f (node root₁ children₁) = node (f root₁) (mapᶠ f children₁)
mapᶠ f [] = []
mapᶠ f (x ∷ a) = map f x ∷ mapᶠ f a

foldr : (A → List B → B) → Rose A → B
foldrᶠ : (A → List B → B) → Forest A → List B
foldr n (node r cs) = n r (foldrᶠ n cs)
foldrᶠ n [] = []
foldrᶠ n (x ∷ t) = foldr n x ∷ (foldrᶠ n t)

depth : Rose A → ℕ
depthᶠ : Forest A → ℕ
depth (node root₁ children₁) = suc (depthᶠ children₁)
depthᶠ [] = 0
depthᶠ (x ∷ ns) = (depth x) ⊔ (depthᶠ ns)

nodes : Rose A → ℕ
nodesᶠ : Forest A → ℕ
nodes (node root₁ children₁) = suc (nodesᶠ children₁)
nodesᶠ [] = 0
nodesᶠ (x ∷ ns) = nodes x + nodesᶠ ns

module _ {P : Pred A ℓ} (P? : Decidable P) where

  filter : Rose A → Maybe (Rose A)
  filterᶠ : Forest A → Forest A

  filter (node root₁ children₁) = if does (P? root₁) 
    then just (node root₁ (filterᶠ children₁)) 
    else nothing

  filterᶠ [] = []
  filterᶠ (t ∷ ts) = (filter t) ?∷ (filterᶠ ts)
  
  filterChildren : Rose A → Rose A
  filterChildren (node root₁ children₁) = node root₁ (filterᶠ children₁)

flatten : Rose A → List A
flattenᶠ : Forest A → List A
flattenᶠ [] = []
flattenᶠ (t ∷ ts) = (flatten t) List.++ (flattenᶠ ts)
flatten (node root₁ children₁) = root₁ ∷ flattenᶠ children₁
