{-# OPTIONS --without-K --safe #-}

module Unsized.Data.Tree.Rose.Relation.Unary.Siblings.Properties where

open import Level
open import Data.Empty using (⊥-elim)
open import Relation.Nullary as Dec
open import Relation.Nullary.Negation using (¬?)
open import Relation.Binary using (Rel)
open import Relation.Binary as B using (REL; Setoid; _Respects_)
open import Relation.Unary using (Pred; Decidable; Satisfiable; _∩_; IUniversal; _⇒_) renaming (_⊆_ to _⋐_)
import Relation.Nullary.Decidable.Core as Dec
open import Unsized.Data.Tree.Rose as Rose
open import Unsized.Data.Tree.Rose.Properties as Rose
open import Data.List using (List; _∷_; [])
open import Data.List.Membership.Propositional renaming (_∈_ to _∈ₗ_; find to findₗ)
import Data.List.Membership.Propositional.Properties as List
import Unsized.Data.Tree.Rose.Membership.Setoid as SetoidMembership
open import Unsized.Data.Tree.Rose.Membership.Propositional
import Unsized.Util.AllPairs as Pairs
import Data.List.Relation.Unary.All as List
import Data.List.Relation.Unary.AllPairs as Pairs
import Data.List.Relation.Unary.AllPairs.Properties as Pairs
import Data.List.Relation.Unary.Any as AnyList
open import Data.List.Relation.Binary.Equality.Propositional using (≡⇒≋)
open import Data.Product as Prod using (∃; _,_)
open import Unsized.Data.Tree.Rose.Relation.Unary.Any as Any using (Any)
import Unsized.Data.Tree.Rose.Relation.Unary.All.Properties as All
open import Relation.Binary.PropositionalEquality as P using (refl; _≡_; cong₂; _≗_)
open P.≡-Reasoning
open import Unsized.Data.Tree.Rose.Relation.Unary.Any using (here; there)
open import Unsized.Data.Tree.Rose.Relation.Unary.Siblings as Siblings
import Data.List.Relation.Unary.All.Properties as AllList
import Data.Maybe.Relation.Unary.All as Maybe
open import Function.Base
open import Function.Equivalence using (_⇔_; equivalence; Equivalence)
open import Function.Inverse using (_↔_; inverse)
open import Function.Surjection using (_↠_; surjection)

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A B : Set ℓ
    _~_ : Rel A ℓ₁
    t : Rose A
    cs : Forest A
    P : Pred A ℓ

------------------------------------------------------------------------
-- Introduction (⁺) and elimination (⁻) rules for rose operations
------------------------------------------------------------------------
-- leaf

leaf⁺ : ∀ {x : A} → Siblings _~_ (leaf x)
leaf⁺ = node Pairs.[] List.[]

------------------------------------------------------------------------
-- children

children⁺ : Siblings _~_ t → Siblingsᶠ _~_ (children t)
children⁺ (node _ cs) = cs

------------------------------------------------------------------------
-- map

map⁺ : ∀ {_~_ : Rel B ℓ} {f : A → B} → Siblings (λ x y → f x ~ f y) t → Siblings _~_ (Rose.map f t)
mapᶠ⁺ : ∀ {_~_ : Rel B ℓ} {f : A → B} →  Siblingsᶠ (λ x y → f x ~ f y) cs → Siblingsᶠ _~_ (Rose.mapᶠ f cs)
map⁺ (node x y) = node (P.subst (Pairs.AllPairs _) (map∘map≡mapᶠ _ _) (Pairs.map⁺ x)) (mapᶠ⁺ y)
mapᶠ⁺ List.[] = List.[]
mapᶠ⁺ (px List.∷ x) = map⁺ px List.∷ mapᶠ⁺ x

map⁻ : ∀ {_~_ : Rel B ℓ} {f : A → B} → Siblings _~_ (Rose.map f t) → Siblings (λ x y → f x ~ f y) t
mapᶠ⁻ : ∀ {_~_ : Rel B ℓ} {f : A → B} → Siblingsᶠ _~_ (Rose.mapᶠ f cs) → Siblingsᶠ (λ x y → f x ~ f y) cs
map⁻ {f = f} (node r cs) = node (Pairs.map⁻ {f = Rose.map f} (P.subst (Pairs.AllPairs _) (P.sym (map∘map≡mapᶠ _ _)) r)) (mapᶠ⁻ cs)
mapᶠ⁻ {cs = []} x = List.[]
mapᶠ⁻ {cs = x₁ ∷ cs} (px List.∷ x) = (map⁻ px) List.∷ (mapᶠ⁻ x)

------------------------------------------------------------------------
-- filter

module _ (P? : Decidable P) where

  all~filterᶠ : ∀ {r} cs → List.All (λ y → r ~ root y) cs → 
                List.All (λ y → r ~ root y) (filterᶠ P? cs)
  all~filterᶠ [] x = x
  all~filterᶠ {_~_ = _~_} (node r cs ∷ cs') (px List.∷ x) with P? r
  ... | yes pr = px List.∷ all~filterᶠ {_~_ = _~_} cs' x
  ... | no ¬pr = all~filterᶠ {_~_ = _~_} cs' x  
  
  pairs~filterᶠ : ∀ cs → Pairs.AllPairs (λ x y → root x ~ root y) cs →
                  Pairs.AllPairs (λ x y → root x ~ root y) (filterᶠ P? cs)
  pairs~filterᶠ [] = id
  pairs~filterᶠ {_~_ = _~_} (node r cs ∷ cs') (x₁ Pairs.∷ x₂) with P? r
  ... | yes pr = all~filterᶠ {_~_ = _~_} cs' x₁ Pairs.∷ pairs~filterᶠ cs' x₂
  ... | no ¬pr = pairs~filterᶠ cs' x₂       

  filter⁺ : ∀ t → Siblings _~_ t → Maybe.All (Siblings _~_) (Rose.filter P? t)
  filterᶠ⁺ : ∀ t → Siblingsᶠ _~_ t → Siblingsᶠ _~_ (filterᶠ P? t) 
  filter⁺ (node r cs) (node x x₁) with P? r 
  ... | yes pr = Maybe.just (node (pairs~filterᶠ cs x) (filterᶠ⁺ cs x₁))
  ... | no ¬pr = Maybe.nothing
  filterᶠ⁺ [] x = x
  filterᶠ⁺ (c@(node r cs) ∷ cs') (px List.∷ x) with P? r | filter⁺ c px
  ... | yes pr | Maybe.just x₁ = x₁ List.∷ filterᶠ⁺ cs' x
  ... | no ¬pr | t2 = filterᶠ⁺ cs' x
  
------------------------------------------------------------------------
-- filterChildren

  filterChildren⁺ : Siblings _~_ t → Siblings _~_ (filterChildren P? t)
  filterChildren⁺ (node x x₁) = node (pairs~filterᶠ _ x) (filterᶠ⁺ _ x₁)
  