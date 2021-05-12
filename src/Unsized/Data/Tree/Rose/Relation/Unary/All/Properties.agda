{-# OPTIONS --without-K --safe #-}

module Unsized.Data.Tree.Rose.Relation.Unary.All.Properties where

open import Level
open import Data.Empty using (⊥-elim)
open import Relation.Nullary as Dec
open import Relation.Binary as B using (REL; Setoid; _Respects_)
open import Relation.Unary using (Pred; Decidable; Satisfiable; _∩_; IUniversal; _⇒_) renaming (_⊆_ to _⋐_)
import Relation.Nullary.Decidable.Core as Dec
open import Unsized.Data.Tree.Rose using (Rose; node)
open import Data.List using (List; _∷_; [])
open import Data.List.Membership.Propositional renaming (_∈_ to _∈ₗ_; find to findₗ)
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
open import Function.Equivalence using (_⇔_; equivalence; Equivalence)
open import Function.Inverse using (_↔_; inverse)
open import Function.Surjection using (_↠_; surjection)

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A B : Set ℓ
    P : Pred A ℓ₁
    Q : Pred A ℓ₂
    R : Pred A ℓ₃
    t : Rose A
    cs : List (Rose A)

------------------------------------------------------------------------
-- Lemmas relating Any, All and negation.

All⇒Any : ∀ {t} → All P t → Any P t
All⇒Any (node p _) = here p

¬Any⇒All¬ : ∀ (t : Rose A) → ¬ Any P t → All (¬_ ∘ P) t
¬Any⇒All¬' : ∀ (cs : List (Rose A)) → (∀ {t} → t ∈ₗ cs → ¬ Any P t) → List.All (All (¬_ ∘ P)) cs
¬Any⇒All¬ (node root children) ¬p = node (λ z → ¬p (here z)) (¬Any⇒All¬' children λ x → ¬p ∘ there x)
¬Any⇒All¬' [] ¬p = List.[]
¬Any⇒All¬' (c ∷ cs) ¬p = ¬Any⇒All¬ c (¬p (AnyList.here refl)) List.∷ ¬Any⇒All¬' cs (λ z → ¬p (AnyList.there z)) 

All¬⇒¬Any : ∀ (t : Rose A) → All (¬_ ∘ P) t → ¬ Any P t
All¬⇒¬Any (node root children) (node x x₁) (here x₂) = x x₂
All¬⇒¬Any (node root children) (node x x₁) (there x₂ y) = All¬⇒¬Any _ (List.lookup x₁ x₂) y

¬All⇒Any¬ : Decidable P → ∀ t → ¬ All P t → Any (¬_ ∘ P) t
¬All⇒Any¬' : Decidable P → ∀ cs → AnyList.Any (¬_ ∘ All P) cs → Prod.Σ[ c ∈ _ ] c ∈ₗ cs Prod.× Any (¬_ ∘ P) c
¬All⇒Any¬ dec (node root children) ¬∀ with dec root | List.all? (all? dec) children
... | yes pr | yes pcs = ⊥-elim (¬∀ (node pr pcs))
... | no ¬pr | _       = here ¬pr
... | yes _  | no ¬pcs with ¬All⇒Any¬' dec children (AllList.¬All⇒Any¬ (all? dec) children ¬pcs) 
... | t1 , t2 , t3 = there t2 t3
¬All⇒Any¬' dec (c ∷ cs) (AnyList.here px) = _ , AnyList.here refl , ¬All⇒Any¬ dec _ px
¬All⇒Any¬' dec (x ∷ cs) (AnyList.there xs) with ¬All⇒Any¬' dec cs xs 
... | t1 , t2 , t3 = t1 , AnyList.there t2 , t3

Any¬⇒¬All : Any (¬_ ∘ P) t → ¬ All P t
Any¬⇒¬All (here x) = x ∘ root
Any¬⇒¬All (there x x₂) x₁ = Any¬⇒¬All x₂ (List.lookup (children x₁) x)

¬Any↠All¬ : (¬ Any P t) ↠ All (¬_ ∘ P) t
¬Any↠All¬ = surjection (¬Any⇒All¬ _) (All¬⇒¬Any _) to∘from
  where 
    to∘from' : ∀ (¬cs : List.All (All (¬_ ∘ P)) cs) → ¬Any⇒All¬' cs (λ x x₁ → All¬⇒¬Any _ (List.lookup ¬cs x) x₁) ≡ ¬cs
    to∘from : ∀ (¬p : All (¬_ ∘ P) t) → ¬Any⇒All¬ t (All¬⇒¬Any t ¬p) ≡ ¬p
    to∘from (node x x₁) = cong₂ node refl (to∘from' x₁)
    to∘from' List.[] = refl
    to∘from' (px List.∷ ¬cs) = cong₂ List._∷_ (to∘from px) (to∘from' ¬cs)
    
Any¬⇔¬All : Decidable P → Any (¬_ ∘ P) t ⇔ (¬ All P t)
Any¬⇔¬All dec = equivalence Any¬⇒¬All (¬All⇒Any¬ dec _)

module _ {_~_ : REL A B ℓ} where
  All-swap : ∀ {t1 t2} → All (λ x → All (x ~_) t2) t1 → All (λ y → All (_~ y) t1) t2
  All-swap {node root₁ children₁} {node root₂ children₂} (node x x₁) = node (node (root x) (List.map (map All.root) x₁)) 
    (List.tabulate λ x₂ → tabulate (λ x₄ → node (lookup x (there x₂ x₄)) (List.map (map (λ x₇ → lookup x₇ (there x₂ x₄))) x₁)))

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