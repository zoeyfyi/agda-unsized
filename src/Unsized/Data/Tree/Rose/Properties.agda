{-# OPTIONS --without-K --safe #-}

module Unsized.Data.Tree.Rose.Properties where

open import Data.List using (List; []; _∷_)
import Data.List.Properties as List
import Data.Nat.Properties as Nat
import Data.List.Relation.Unary.All as List
open import Data.Product using (_×_; _,_; uncurry; curry)
import Data.List as List
open import Data.List.Extrema.Nat using (max)
open import Level using (Level)
open import Data.Nat
open import Relation.Nullary
open import Unsized.Data.Tree.Rose
open import Unsized.Data.Tree.Rose.Relation.Unary.All using (All)
open import Unsized.Util
open import Function.Base
open import Function.Definitions
import Relation.Nullary.Decidable as Decidable
open import Relation.Unary using (Pred; Decidable)
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary using (DecidableEquality)
open ≡-Reasoning

private
  variable
    ℓ : Level
    A B C : Set ℓ
    t t₁ t₂ : Rose A
    r r₁ r₂ : A
    cs cs₁ cs₂ : Forest A
    
-----------------------------------------------------------------------
-- node

node-injective : node r₁ cs₁ ≡ node r₂ cs₂ → r₁ ≡ r₂ × cs₁ ≡ cs₂
node-injective refl = refl , refl

node-injectiveₗ : node r₁ cs₁ ≡ node r₂ cs₂ → r₁ ≡ r₂
node-injectiveₗ refl = refl

node-injectiveᵣ : node r₁ cs₁ ≡ node r₂ cs₂ → cs₁ ≡ cs₂
node-injectiveᵣ refl = refl

node-dec : Dec (r₁ ≡ r₂) → Dec (cs₁ ≡ cs₂) → Dec (node r₁ cs₁ ≡ node r₂ cs₂)
node-dec r₁≟r₂ cs₁≟cs₂ = Decidable.map′ (uncurry (cong₂ node)) node-injective (r₁≟r₂ ×-dec cs₁≟cs₂)

≡-dec : DecidableEquality A → DecidableEquality (Rose A)
≡-decᶠ : DecidableEquality A → DecidableEquality (Forest A)
≡-dec _≟_ (node root₁ children₁) (node root₂ children₂) = node-dec (root₁ ≟ root₂) (≡-decᶠ _≟_ children₁ children₂)
≡-decᶠ _≟_ [] [] = yes refl
≡-decᶠ _≟_ [] (_ ∷ _) = no (λ ())
≡-decᶠ _≟_ (_ ∷ _) [] = no (λ ())
≡-decᶠ _≟_ (c₁ ∷ cs₁) (c₂ ∷ cs₂) = List.∷-dec (≡-dec _≟_ c₁ c₂) (≡-decᶠ _≟_ cs₁ cs₂)

------------------------------------------------------------------------
-- leaf

leaf-depth : depth (leaf r) ≡ 1
leaf-depth = refl

------------------------------------------------------------------------
-- map

map-id : map id ≗ id {A = Rose A}
mapᶠ-id : mapᶠ id ≗ id {A = Forest A}
map-id (node root₁ children₁) = cong (node root₁) (mapᶠ-id children₁)
mapᶠ-id [] = refl
mapᶠ-id (c ∷ cs) = cong₂ _∷_ (map-id c) (mapᶠ-id cs)

map-id₂ : ∀ {f : A → A} → All (λ x → f x ≡ x) t → map f t ≡ t
mapᶠ-id₂ : ∀ {f : A → A} → List.All (All (λ x → f x ≡ x)) cs → mapᶠ f cs ≡ cs
map-id₂ (All.node x x₁) = cong₂ node x (mapᶠ-id₂ x₁)
mapᶠ-id₂ List.[] = refl
mapᶠ-id₂ (px List.∷ x) = cong₂ _∷_ (map-id₂ px) (mapᶠ-id₂ x)

map-cong : ∀ {f g : A → B} → f ≗ g → map f ≗ map g
mapᶠ-cong : ∀ {f g : A → B} → f ≗ g → mapᶠ f ≗ mapᶠ g
map-cong f≗g (node root₁ children₁) = cong₂ node (f≗g root₁) (mapᶠ-cong f≗g children₁)
mapᶠ-cong f≗g [] = refl
mapᶠ-cong f≗g (c ∷ cs) = cong₂ _∷_ (map-cong f≗g c) (mapᶠ-cong f≗g cs)

map-cong₂ : ∀ {f g : A → B} → All (λ x → f x ≡ g x) t → map f t ≡ map g t
mapᶠ-cong₂ : ∀ {f g : A → B} → List.All (All (λ x → f x ≡ g x)) cs → mapᶠ f cs ≡ mapᶠ g cs
map-cong₂ (All.node x x₁) = cong₂ node x (mapᶠ-cong₂ x₁)
mapᶠ-cong₂ List.[] = refl
mapᶠ-cong₂ (px List.∷ x) = cong₂ _∷_ (map-cong₂ px) (mapᶠ-cong₂ x)

map-compose : (f : A → B) (g : B → C) → map (g ∘ f) ≗ map g ∘ map f
mapᶠ-compose : (f :  A → B) (g : B → C) → mapᶠ (g ∘ f) ≗ mapᶠ g ∘ mapᶠ f
map-compose f g (node r []) = refl
map-compose f g (node r (c ∷ cs)) = cong (node (g (f r))) $ begin
  map (g ∘ f) c ∷ mapᶠ (g ∘ f) cs          ≡⟨ cong₂ _∷_ (map-compose f g c) (mapᶠ-compose f g cs) ⟩
  (map g ∘ map f) c ∷ (mapᶠ g ∘ mapᶠ f) cs ∎
mapᶠ-compose f g [] = refl
mapᶠ-compose f g (t ∷ ts) = begin
  map (g ∘ f) t ∷ mapᶠ (g ∘ f) ts          ≡⟨ cong₂ _∷_ (map-compose f g t) (mapᶠ-compose f g ts) ⟩
  (map g ∘ map f) t ∷ (mapᶠ g ∘ mapᶠ f) ts ≡⟨⟩
  (mapᶠ g ∘ mapᶠ f) (t ∷ ts)               ∎

map-injective : ∀ {f : A → B} → Injective _≡_ _≡_ f → Injective _≡_ _≡_ (map f)
mapᶠ-injective : ∀ {f : A → B} → Injective _≡_ _≡_ f → Injective _≡_ _≡_ (mapᶠ f)
map-injective finj {node root₁ children₁} {node root₂ children₂} eq = 
  let fr₁≡fr₂ , fcs₁≡fcs₂ = node-injective eq in cong₂ node (finj fr₁≡fr₂) (mapᶠ-injective finj fcs₁≡fcs₂)
mapᶠ-injective finj {[]} {[]} eq = refl
mapᶠ-injective finj {c₁ ∷ cs₁} {c₂ ∷ cs₂} eq = 
  let fc₁≡fc₂ , fcs₁≡fcs₂ = List.∷-injective eq in cong₂ _∷_ (map-injective finj fc₁≡fc₂) (mapᶠ-injective finj fcs₁≡fcs₂)

------------------------------------------------------------------------
-- foldr

foldr-map : (f : A → B) (n : B → List C → C) (ts : Rose A) →
            foldr n (map f ts) ≡ foldr (n ∘ f) ts
foldrᶠ-map : (f : A → B) (n : B → List C → C) (ts : Forest A) →
             foldrᶠ n (mapᶠ f ts) ≡ foldrᶠ (n ∘ f) ts 
foldr-map f n (node root₁ children₁) = cong (n (f root₁)) $ begin
  foldrᶠ n (mapᶠ f children₁) ≡⟨ foldrᶠ-map f n children₁ ⟩
  foldrᶠ (n ∘ f) children₁    ∎
foldrᶠ-map f n [] = refl
foldrᶠ-map f n (t ∷ ts) = begin
  foldr n (map f t) ∷ foldrᶠ n (mapᶠ f ts) ≡⟨ cong₂ _∷_ (foldr-map f n t) (foldrᶠ-map f n ts) ⟩ 
  foldr (n ∘ f) t ∷ foldrᶠ (n ∘ f) ts      ∎

------------------------------------------------------------------------
-- depth

depth-map : (f : A → B) (t : Rose A) → depth (map f t) ≡ depth t
depthᶠ-map : (f : A → B) (ts : Forest A) → depthᶠ (mapᶠ f ts) ≡ depthᶠ ts
depth-map f (node root₁ children₁) = cong suc $ begin
  depthᶠ (mapᶠ f children₁) ≡⟨ depthᶠ-map f children₁ ⟩
  depthᶠ children₁          ∎
depthᶠ-map f [] = refl
depthᶠ-map f (t ∷ ts) = begin 
    depth (map f t) ⊔ depthᶠ (mapᶠ f ts) ≡⟨ cong₂ _⊔_ (depth-map f t) (depthᶠ-map f ts) ⟩ 
    depth t ⊔ depthᶠ ts                  ∎

depth≤nodes : ∀ (t : Rose A) → depth t ≤ nodes t
depthᶠ≤nodesᶠ : ∀ (cs : Forest A) → depthᶠ cs ≤ nodesᶠ cs
depth≤nodes (node root₁ children₁) = s≤s (depthᶠ≤nodesᶠ children₁)
depthᶠ≤nodesᶠ [] = z≤n
depthᶠ≤nodesᶠ (c ∷ cs) = m≤o⇒n≤o⇒m⊔n≤o 
  (m≤n⇒m≤n+o (depth≤nodes c)) (m≤o⇒m≤n+o (depthᶠ≤nodesᶠ cs))

------------------------------------------------------------------------
-- flatten

nodes≡length∘flatten : (t : Rose A) → nodes t ≡ List.length (flatten t) 
nodesᶠ≡length∘flattenᶠ : (cs : Forest A) → nodesᶠ cs ≡ List.length (flattenᶠ cs)
nodes≡length∘flatten (node root₁ children₁) = cong suc (nodesᶠ≡length∘flattenᶠ children₁)
nodesᶠ≡length∘flattenᶠ [] = refl
nodesᶠ≡length∘flattenᶠ (c ∷ cs) = 
  cong suc (trans (cong₂ _+_ (nodesᶠ≡length∘flattenᶠ (children c)) (nodesᶠ≡length∘flattenᶠ cs)) 
                  (sym (List.length-++ (flattenᶠ (children c)))))