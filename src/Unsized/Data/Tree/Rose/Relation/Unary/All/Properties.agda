{-# OPTIONS --without-K --safe #-}

module Unsized.Data.Tree.Rose.Relation.Unary.All.Properties where

open import Level
open import Relation.Nullary as Dec
open import Relation.Binary using (Setoid; _Respects_)
open import Relation.Unary using (Pred; Decidable; Satisfiable; _∩_; IUniversal; _⇒_) renaming (_⊆_ to _⋐_)
import Relation.Nullary.Decidable.Core as Dec
open import Unsized.Data.Tree.Rose using (Rose; node)
open import Data.List using (List; _∷_; [])
open import Data.List.Membership.Propositional renaming (_∈_ to _∈ₗ_)
import Unsized.Data.Tree.Rose.Membership.Setoid as SetoidMembership
open import Unsized.Data.Tree.Rose.Membership.Propositional
import Data.List.Relation.Unary.All as List
import Data.List.Relation.Unary.Any as AnyList
open import Data.Product as Prod using (∃; _,_)
open import Unsized.Data.Tree.Rose.Relation.Unary.Any as Any using (Any)
open import Relation.Binary.PropositionalEquality as P using (refl; _≡_; cong₂; _≗_)
open P.≡-Reasoning
open import Unsized.Data.Tree.Rose.Relation.Unary.Any using (here; there)
open import Unsized.Data.Tree.Rose.Relation.Unary.All as All
import Data.List.Relation.Unary.All.Properties as AllList
open import Function.Base

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A : Set ℓ
    P : Pred A ℓ₁
    Q : Pred A ℓ₂
    R : Pred A ℓ₃
    t : Rose A
    cs : List (Rose A)

------------------------------------------------------------------------
-- map

map-id : ∀ (ts : All P t) → All.map id ts ≡ ts
map'-id : ∀ (css : List.All (All P) cs) → map' id css ≡ css
map-id (node r cs) = cong₂ node refl (map'-id cs)
map'-id List.[] = refl
map'-id (px List.∷ css) = cong₂ List._∷_ (map-id px) (map'-id css)


map-cong : ∀ {f : P ⋐ Q} {g : P ⋐ Q} (pt : All P t) →
           (∀ {x} → f {x} ≗ g) → All.map f pt ≡ All.map g pt
map'-cong : ∀ {f : P ⋐ Q} {g : P ⋐ Q} (pcs : List.All (All P) cs) →
            (∀ {x} → f {x} ≗ g) → All.map' f pcs ≡ All.map' g pcs
map-cong (node pr pcs) feq = cong₂ node (feq pr) (map'-cong pcs feq)
map'-cong List.[] feq = refl
map'-cong (px List.∷ pcs) feq = cong₂ List._∷_ (map-cong px feq) (map'-cong pcs feq)

map-compose : ∀ {f : P ⋐ Q} {g : Q ⋐ R} (pt : All P t) →
              All.map g (All.map f pt) ≡ All.map (g ∘ f) pt
map'-compose : ∀ {f : P ⋐ Q} {g : Q ⋐ R} (pcs : List.All (All P) cs) →
               All.map' g (All.map' f pcs) ≡ All.map' (g ∘ f) pcs
map-compose (node x cs) = cong₂ node refl (map'-compose cs)   
map'-compose List.[] = refl
map'-compose (px List.∷ pcs) = cong₂ List._∷_ (map-compose px) (map'-compose pcs)

lookup-map : ∀ {x : A} {f : P ⋐ Q} (pt : All P t) (i : x ∈ t) →
             lookup (All.map f pt) i ≡ f (lookup pt i)
lookup-map' : ∀ {f : P ⋐ Q} (pcs : List.All (All P) cs) (i : t ∈ₗ cs) →
              List.lookup (All.map' f pcs) i ≡ All.map f (List.lookup pcs i)
lookup-map (node x x₁) (here refl) = refl
lookup-map  {Q = Q} {f = f} (node x x₁) (there x₂ i) = begin
    lookup (All.map f (node x x₁)) (there x₂ i)      ≡⟨⟩
    lookup (node (f x) (All.map' f x₁)) (there x₂ i) ≡⟨⟩
    lookup (List.lookup (map' f x₁) x₂) i            ≡⟨ P.cong (λ x₄ → lookup x₄ i) (lookup-map' x₁ x₂) ⟩ 
    lookup (All.map f (List.lookup x₁ x₂)) i         ≡⟨ lookup-map (List.lookup x₁ x₂) i ⟩ 
    f (lookup (node x x₁) (there x₂ i))              ∎
lookup-map' {f = f} (px List.∷ pcs) (AnyList.here refl) = refl
lookup-map' {f = f} (px List.∷ pcs) (AnyList.there i) = begin
  List.lookup (All.map' f (px List.∷ pcs)) (AnyList.there i)             ≡⟨⟩
  List.lookup ((All.map f px) List.∷ (All.map' f pcs)) (AnyList.there i) ≡⟨⟩
  List.lookup (All.map' f pcs) i                                         ≡⟨ lookup-map' pcs i ⟩
  All.map f (List.lookup pcs i)                                          ≡⟨⟩
  All.map f (List.lookup (px List.∷ pcs) (AnyList.there i))              ∎
