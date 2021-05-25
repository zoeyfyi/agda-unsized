{-# OPTIONS --without-K --safe --guardedness #-}

module Unsized.Codata.Stream where

open import Data.Nat.Base
open import Data.Maybe using (Maybe)
open import Data.List.Base as L using (List; []; _∷_)
open import Data.List.NonEmpty as L⁺ using (List⁺; _∷_; _++⁺_; [_])
open import Data.Vec.Base using (Vec; []; _∷_)
open import Data.Product as P hiding (map)
open import Function.Base

record Stream {ℓ} (A : Set ℓ) : Set ℓ where
  constructor _∷_
  coinductive
  field
    hd : A
    tl : Stream A
open Stream public

module _ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′} where

  map : (A → B) → Stream A → Stream B
  hd (map f as) = f (hd as)
  tl (map f as) = map f (tl as)

  ap : Stream (A → B) → Stream A → Stream B
  hd (ap fs as) = (hd fs) (hd as)
  tl (ap fs as) = ap (tl fs) (tl as)

  unfold : (A → A × B) → A → Stream B
  hd (unfold f a) = proj₂ (f a)
  tl (unfold f a) = unfold f (proj₁ (f a))

  scanl : (B → A → B) → B → Stream A → Stream B
  hd (scanl f b as) = b
  tl (scanl f b as) = scanl f (f b (hd as)) (tl as)

module _ {ℓ} {A : Set ℓ} where

  repeat : A → Stream A
  hd (repeat a) = a
  tl (repeat a) = repeat a

  head : Stream A → A
  head = hd

  tail : Stream A → Stream A
  tail = tl

  lookup : ℕ → Stream A → A
  lookup zero as = hd as
  lookup (suc n) as = lookup n (tl as)

  take : (n : ℕ) → Stream A → Vec A n
  take zero as = []
  take (suc n) as = hd as ∷ take n (tl as)

  drop : (n : ℕ) → Stream A → Stream A
  drop zero as = as
  drop (suc n) as = drop n (tl as)

  splitAt : (n : ℕ) → Stream A → Vec A n × Stream A
  splitAt n = < take n , drop n >

  even : Stream A → Stream A 
  hd (even as) = hd as
  tl (even as) = even (tl (tl as))

  odd : Stream A → Stream A
  hd (odd as) = hd (tl as)
  tl (odd as) = odd (tl (tl as))

  infixr 5 _++_ _⁺++_

  _++_ : List A → Stream A → Stream A
  hd ([] ++ as) = hd as
  tl ([] ++ as) = tl as
  hd ((l ∷ ls) ++ as) = l
  tl ((l ∷ ls) ++ as) = ls ++ as

  _⁺++_ : List⁺ A → Stream A → Stream A
  hd ((l ∷ ls) ⁺++ as) = l
  tl ((l ∷ ls) ⁺++ as) = ls ++ as

  concat : Stream (List⁺ A) → Stream A
  hd (concat as) = List⁺.head (hd as)
  tl (concat as) with (hd as)
  ... | _ ∷ []     = concat (tl as)
  ... | _ ∷ h ∷ hs = concat ((h ∷ hs) ∷ (tl as))

  interleave : Stream A → Stream A → Stream A
  hd (interleave as bs) = hd as
  tl (interleave as bs) = interleave bs (tl as)

  split : Stream A → Stream A × Stream A
  split as = (even as) , (odd as)

  chunksOf : (n : ℕ) → Stream A → Stream (Vec A n)
  hd (chunksOf n as) = take n as
  tl (chunksOf n as) = chunksOf n (drop n as)

module _ {ℓ} {A : Set ℓ} where

  cycle : List⁺ A → Stream A
  cycle ls = concat (repeat ls)

module _ {ℓ ℓ₁ ℓ₂} {A : Set ℓ} {B : Set ℓ₁} {C : Set ℓ₂} where

  zipWith : (A → B → C) → Stream A → Stream B → Stream C
  hd (zipWith f as bs) = f (hd as) (hd bs)
  tl (zipWith f as bs) = zipWith f (tl as) (tl bs)

module _ {ℓ} {A : Set ℓ} where

  iterate : (A → A) → A → Stream A
  hd (iterate f a) = a
  tl (iterate f a) = iterate f (f a)
