{-# OPTIONS --without-K --safe #-}

module Unsized.Data.Tree.Rose.Relation.Unary.Siblings where

open import Level
open import Relation.Nullary as Dec
open import Relation.Unary using (Pred)
open import Relation.Binary using (Rel; _⇒_)
import Relation.Nullary.Decidable.Core as Dec
open import Unsized.Data.Tree.Rose using (Rose; node; root)
open import Data.List using (List; _∷_; [])
open import Data.List.Membership.Propositional
import Data.List.Relation.Unary.AllPairs as AllPairs
open AllPairs using (AllPairs)
import Data.List.Relation.Unary.All as List
open import Data.Product using (∃; _,_)
open import Function

private
  variable
    ℓ ℓ₁ : Level
    A : Set ℓ
    P Q : Rel A ℓ₁
    t : Rose A
    
data Siblings {A : Set ℓ} (_∼_ : Rel A ℓ₁) : Pred (Rose A) (ℓ ⊔ ℓ₁) where
  node : ∀ {r cs} → 
         AllPairs (λ x y → (root x) ∼ (root y)) cs → 
         List.All (Siblings _∼_) cs → 
         Siblings _∼_ (node r cs)

map : P ⇒ Q → Siblings P t → Siblings Q t
map' : ∀ {ts : List (Rose A)} → P ⇒ Q → List.All (Siblings P) ts → List.All (Siblings Q) ts
map P⇒Q (node x cs) = node (AllPairs.map P⇒Q x) (map' P⇒Q cs)
map' P⇒Q List.[] = List.[]
map' P⇒Q (px List.∷ ts) = map P⇒Q px List.∷ map' P⇒Q ts
