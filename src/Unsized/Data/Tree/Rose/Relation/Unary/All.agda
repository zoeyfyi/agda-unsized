{-# OPTIONS --without-K --safe #-}

module Unsized.Data.Tree.Rose.Relation.Unary.All where

open import Level
open import Relation.Nullary as Dec
open import Relation.Binary using (Setoid; _Respects_)
open import Relation.Unary using (Pred; _⊆_; Decidable; Satisfiable; _∩_; IUniversal; _⇒_)
import Relation.Nullary.Decidable.Core as Dec
open import Unsized.Data.Tree.Rose using (Rose; Forest; node)
open import Data.List using (List; _∷_; [])
open import Data.List.Membership.Propositional renaming (_∈_ to _∈ₗ_)
import Unsized.Data.Tree.Rose.Membership.Setoid as SetoidMembership
open import Unsized.Data.Tree.Rose.Membership.Propositional
import Data.List.Relation.Unary.All as List
import Data.List.Relation.Unary.Any as AnyList
open import Data.Product as Prod using (∃; _,_)
open import Unsized.Data.Tree.Rose.Relation.Unary.Any as Any using (Any)
open import Relation.Binary.PropositionalEquality as P using (refl; _≡_)
open import Unsized.Data.Tree.Rose.Relation.Unary.Any using (here; there)
open import Function.Base

private
  variable
    ℓ₁ ℓ₂ ℓ₃ : Level
    A : Set ℓ₁
    P Q R : Pred A ℓ₁
    t : Rose A
    
------------------------------------------------------------------------
-- Definitions

data All {A : Set ℓ₁} (P : Pred A ℓ₂) : Pred (Rose A) (ℓ₁ ⊔ ℓ₂)

Allᶠ : {A : Set ℓ₁} → Pred A ℓ₂ → Pred (Forest A) (ℓ₁ ⊔ ℓ₂)
Allᶠ P = List.All (All P)

data All P where
  node : ∀ {r cs} → P r → List.All (All P) cs → All P (node r cs)

------------------------------------------------------------------------
-- Operations on All

root : ∀ {r cs} → All P (node r cs) → P r
root (node p _) = p

children : ∀ {r cs} → All P (node r cs) → Allᶠ P cs
children (node _ pcs) = pcs

map : P ⊆ Q → All P t → All Q t
mapᶠ : ∀ {ts : Forest A} → P ⊆ Q → Allᶠ P ts → Allᶠ Q ts
map g (node x x₁) = node (g x) (mapᶠ g x₁)
mapᶠ g List.[] = List.[]
mapᶠ g (px List.∷ ts) = map g px List.∷ mapᶠ g ts

module _(S : Setoid ℓ₁ ℓ₂) {P : Pred (Setoid.Carrier S) ℓ₃} where
  open Setoid S renaming (Carrier to C; refl to refl₁)
  open SetoidMembership S renaming (_∈_ to _∈ₛ_)

  tabulateₛ : (∀ {x} → x ∈ₛ t → P x) → All P t
  tabulateₛᶠ : ∀ {ts : Forest C} → 
               (∀ {x t} → t ∈ₗ ts → x ∈ₛ t → P x) → 
               Allᶠ P ts
  tabulateₛ {node root children} hyp = 
    node (hyp (here refl₁)) (tabulateₛᶠ (λ x x₁ → hyp (there x x₁)))
  tabulateₛᶠ {ts = []} hyp = List.[]
  tabulateₛᶠ {ts = t ∷ ts} hyp = 
    tabulateₛ (hyp (AnyList.here refl)) List.∷ tabulateₛᶠ (λ x x₁ → hyp (AnyList.there x) x₁)

tabulate : (∀ {x} → x ∈ t → P x) → All P t
tabulate = tabulateₛ (P.setoid _)

------------------------------------------------------------------------
-- Generalised lookup based on a proof of Any

lookupAny : All P t → (i : Any Q t) → (P ∩ Q) (Any.lookup i)
lookupAny (node px pxs) (Any.here qx) = px , qx
lookupAny (node px pxs) (Any.there t∈cs i) = lookupAny (List.lookup pxs t∈cs) i

lookupWith : ∀[ P ⇒ Q ⇒ R ] → All P t → (i : Any Q t) → R (Any.lookup i)
lookupWith f pxs i = Prod.uncurry f (lookupAny pxs i)

lookup : All P t → (∀ {x} → x ∈ t → P x)
lookup pxs = lookupWith (λ { px refl → px }) pxs

module _ (S : Setoid ℓ₁ ℓ₂) {P : Pred (Setoid.Carrier S) ℓ₃} where
  open Setoid S renaming (sym to sym₁)
  open SetoidMembership S renaming (_∈_ to _∈ₛ_)

  lookupₛ : P Respects _≈_ → All P t → (∀ {x} → x ∈ₛ t → P x)
  lookupₛ resp pxs = lookupWith ((λ py x=y → resp (sym₁ x=y) py)) pxs

------------------------------------------------------------------------
-- Properties of predicates preserved by All

all? : Decidable P → Decidable (All P)
all?ᶠ : Decidable P → Decidable (Allᶠ P)
all? p (node root' children') with p root' | all?ᶠ p children'
... | yes pr | yes pcs = yes (node pr pcs)
... | no ¬pr | _       = no (¬pr ∘ root)
... | yes _  | no ¬pcs = no (¬pcs ∘ children)
all?ᶠ p [] = yes List.[]
all?ᶠ p (c ∷ cs) with all? p c | all?ᶠ p cs
... | yes pc | yes pcs = yes (pc List.∷ pcs)
... | no ¬pc | _ = no (λ { (px List.∷ x) → ¬pc px })
... | yes _ | no ¬pcs = no (λ { (px List.∷ x) → ¬pcs x })