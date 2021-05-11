{-# OPTIONS --without-K --safe --guardedness #-}

module Unsized.Codata.Stream.Bisimularity where

open import Data.List.NonEmpty using (List⁺)
open import Data.List using (List)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans)
open import Function.Base
open import Unsized.Codata.Stream


record _≈_ {ℓ} {A : Set ℓ} (xs : Stream A) (ys : Stream A) : Set ℓ where
  coinductive
  field
    hd-≈ : hd xs ≡ hd ys
    tl-≈ : tl xs ≈ tl ys
open _≈_ public

module _ {ℓ} {A : Set ℓ} where

  reflexive : Reflexive (_≈_ {ℓ} {A})
  hd-≈ reflexive = refl
  tl-≈ reflexive = reflexive

  symmetric : Symmetric (_≈_ {ℓ} {A})
  hd-≈ (symmetric x≈y) = sym (hd-≈ x≈y)
  tl-≈ (symmetric x≈y) = symmetric (tl-≈ x≈y)

  transitive : Transitive (_≈_ {ℓ} {A})
  hd-≈ (transitive i≈j j≈k) = trans (hd-≈ i≈j) (hd-≈ j≈k)
  tl-≈ (transitive i≈j j≈k) = transitive (tl-≈ i≈j) (tl-≈ j≈k)

  isEquivalence : IsEquivalence (_≈_ {ℓ} {A})
  isEquivalence = record
    { refl = reflexive
    ; sym = symmetric
    ; trans = transitive
    }

  setoid : Setoid ℓ ℓ
  setoid = record
    { Carrier = Stream A
    ; _≈_ = _≈_
    ; isEquivalence = isEquivalence
    }

module ≈-Reasoning {ℓ} {A : Set ℓ} where

  open import Relation.Binary.Reasoning.Setoid (setoid {ℓ} {A}) public

module _ {ℓ} {A : Set ℓ} where

  ∷-congˡ : ∀ {a a' : A} {as : Stream A} → a ≡ a' → (a ∷ as) ≈ (a' ∷ as)
  ∷-congˡ refl = reflexive

  ∷-congʳ : ∀ {a : A} {as as' : Stream A} → as ≈ as' → (a ∷ as) ≈ (a ∷ as')
  hd-≈ (∷-congʳ as≈as') = refl
  tl-≈ (∷-congʳ as≈as') = as≈as'

  ++-congʳ : ∀ {ls : List A} {as as' : Stream A} → as ≈ as' → (ls ++ as) ≈ (ls ++ as')
  hd-≈ (++-congʳ {List.[]} as≈as') = hd-≈ as≈as'
  hd-≈ (++-congʳ {x List.∷ ls} as≈as') = refl
  tl-≈ (++-congʳ {List.[]} as≈as') = tl-≈ as≈as'
  tl-≈ (++-congʳ {x List.∷ ls} as≈as') = ++-congʳ as≈as'
 
  ⁺++-congʳ : ∀ {ls : List⁺ A} {as as' : Stream A} → as ≈ as' → (ls ⁺++ as) ≈ (ls ⁺++ as')
  hd-≈ (⁺++-congʳ as≈as') = refl
  tl-≈ (⁺++-congʳ as≈as') = ++-congʳ as≈as'

module _ {ℓ} {ℓ₁} {A : Set ℓ} {B : Set ℓ₁} where

  map-cong : ∀ {f : A → B} {as as' : Stream A} → as ≈ as' → map f as ≈ map f as'
  hd-≈ (map-cong {f} as≈as') = cong f (hd-≈ as≈as')
  tl-≈ (map-cong as≈as') = map-cong (tl-≈ as≈as')
