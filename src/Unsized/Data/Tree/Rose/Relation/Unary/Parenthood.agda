{-# OPTIONS --without-K --safe #-}

module Unsized.Data.Tree.Rose.Relation.Unary.Parenthood where

open import Level
open import Relation.Nullary as Dec
open import Relation.Unary using (Pred)
open import Relation.Binary using (Rel; _⇒_)
import Relation.Nullary.Decidable.Core as Dec
open import Unsized.Data.Tree.Rose using (Rose; Forest; node; root)
open import Data.List using (List; _∷_; [])
open import Data.List.Membership.Propositional
import Data.List.Relation.Unary.All as List
open import Data.Product using (∃; _,_)
open import Function

private
  variable
    ℓ ℓ₁ ℓ₂ : Level
    A : Set ℓ
    P Q : Rel A ℓ₁
    t : Rose A
    
data Parenthood {A : Set ℓ} (_∼_ : Rel A ℓ₁) : Pred (Rose A) (ℓ ⊔ ℓ₁) 

Parenthoodᶠ : {A : Set ℓ₁} → Rel A ℓ₂ → Pred (Forest A) (ℓ₁ ⊔ ℓ₂)
Parenthoodᶠ P = List.All (Parenthood P)

data Parenthood _∼_ where
  node : ∀ {r cs} → 
         List.All ((r ∼_) ∘ root) cs → 
         Parenthoodᶠ _∼_ cs → 
         Parenthood _∼_ (node r cs)

map : P ⇒ Q → Parenthood P t → Parenthood Q t
map' : ∀ {ts : Forest A} → P ⇒ Q → List.All (Parenthood P) ts → List.All (Parenthood Q) ts
map P⇒Q (node x cs) = node (List.map P⇒Q x) (map' P⇒Q cs)
map' P⇒Q List.[] = List.[]
map' P⇒Q (px List.∷ ts) = map P⇒Q px List.∷ map' P⇒Q ts
