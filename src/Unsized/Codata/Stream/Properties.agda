{-# OPTIONS --without-K --safe --guardedness #-}

module Unsized.Codata.Stream.Properties where

open import Level using (Level)
open import Unsized.Codata.Stream
open import Unsized.Codata.Stream.Bisimularity
open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Nat.GeneralisedArithmetic using (fold; fold-pull)
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≢_; refl; cong; cong₂; sym)
open import Data.Product as Prod using (_,_; proj₁; proj₂; _×_)
open import Data.Product.Properties as Prod
open import Data.Vec.Base as Vec using (_∷_; [])
open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.NonEmpty.Properties as List⁺
import Data.List.NonEmpty as List⁺
open import Function.Base
open import Function.Bundles
import Data.Fin.Base as Fin
import Data.Nat.Tactic.RingSolver
open import Tactic.RingSolver.Core.AlmostCommutativeRing using (AlmostCommutativeRing)
      
-- TODO: refactor out of here
lookup⁺ : ∀ {ℓ} {A : Set ℓ} (xs : List⁺ A) → Fin.Fin (List⁺.length xs) → A
lookup⁺ (x ∷ xs) Fin.zero = x
lookup⁺ (x ∷ xs) (Fin.suc n) = List.lookup xs n

private
  variable
    ℓ ℓ₁ ℓ₂ : Level
    A : Set ℓ
    B : Set ℓ₁
    C : Set ℓ₂

------------------------------------------------------------------------
-- lookup

all-lookup-repeat : ∀ (a : A) as → (∀ n → lookup n as ≡ a) → as ≈ repeat a
hd-≈ (all-lookup-repeat a as all) = all 0
tl-≈ (all-lookup-repeat a as all) = all-lookup-repeat a (tl as) λ n → all (suc n)

all-lookup : ∀ {as bs : Stream A} → (∀ n → lookup n as ≡ lookup n bs) → as ≈ bs
hd-≈ (all-lookup all) = all 0
tl-≈ (all-lookup all) = all-lookup (λ n → all (suc n))

lookup-cong : ∀ {as bs : Stream A} (n) → as ≈ bs → lookup n as ≡ lookup n bs
lookup-cong zero as≈bs = hd-≈ as≈bs
lookup-cong (suc n) as≈bs = lookup-cong n (tl-≈ as≈bs)

lookup-map : ∀ (f : A → B) {as : Stream A} (n) → lookup n (map f as) ≡ f (lookup n as)
lookup-map f zero = refl
lookup-map f (suc n) = lookup-map f n

lookup-drop-∸ : ∀ {n} m {as : Stream A} → m ≤ n → lookup (n ∸ m) (drop m as) ≡ lookup n as 
lookup-drop-∸ zero {as} m<n = refl
lookup-drop-∸ {n = suc n} (suc m) {as} (s≤s m<n) = begin 
  lookup (suc n ∸ suc m) (drop (suc m) as)  ≡⟨⟩ 
  lookup (n ∸ m) (drop (suc m) as)          ≡⟨ lookup-cong (n ∸ m) reflexive ⟩ 
  lookup (n ∸ m) (drop m (tl as))           ≡⟨ lookup-drop-∸ m m<n ⟩ 
  lookup n (tl as)                          ≡⟨⟩ 
  lookup (suc n) as                         ∎ where open P.≡-Reasoning

lookup-drop-+ : ∀ {as : Stream A} (m n : ℕ) → lookup n (drop m as) ≡ lookup (n + m) as
lookup-drop-+ zero n rewrite +-identityʳ n = refl
lookup-drop-+ {as = as} (suc m) n = begin 
  lookup n (drop (suc m) as)  ≡⟨ refl ⟩ 
  lookup n (drop m (tl as))   ≡⟨ lookup-drop-+ m n ⟩
  lookup (n + m) (tl as)      ≡⟨ cong (λ x → lookup x (tl as)) (+-comm n m) ⟩
  lookup (m + n) (tl as)      ≡⟨ refl ⟩ 
  lookup (suc m + n) as       ≡⟨ cong (λ x → lookup x as) (+-comm (suc m) n) ⟩ 
  lookup (n + suc m) as       ∎ where open P.≡-Reasoning

------------------------------------------------------------------------
-- drop

drop-congˡ : ∀ {as : Stream A} {n} {m} → n ≡ m → drop n as ≡ drop m as
drop-congˡ refl = refl

drop-congʳ : ∀ {as bs : Stream A} (n) → as ≈ bs → drop n as ≈ drop n bs
drop-congʳ zero as≈bs = as≈bs
drop-congʳ (suc n) as≈bs = drop-congʳ n (tl-≈ as≈bs)

drop-tl : ∀ {as : Stream A} (n) → drop n (tl as) ≈ drop (suc n) as
drop-tl zero = reflexive
hd-≈ (drop-tl (suc n)) = refl
tl-≈ (drop-tl (suc n)) = reflexive

-- suc-+ : ∀ x y → suc x + y ≡ x + suc y
-- suc-+ x y = begin 
--   suc x + y ≡⟨ +-comm {!   !} {! x  !} ⟩ 
--   x + suc y ≡⟨ +-comm {! suc x  !} {! x  !} ⟩ 
--   {!   !} ∎ where open P.≡-Reasoning 

drop-drop-fusion : ∀ {as : Stream A} (n m : ℕ) → drop n (drop m as) ≈ drop (n + m) as
drop-drop-fusion zero m = reflexive
drop-drop-fusion (suc n) zero rewrite +-identityʳ n = reflexive
drop-drop-fusion {as = as} (suc n) (suc m) = begin 
  drop (suc n) (drop (suc m) as)  ≈⟨ reflexive ⟩  
  drop (suc n) (drop m (tl as))   ≈⟨ drop-drop-fusion (suc n) m ⟩  
  drop (suc n + m) (tl as)        ≈⟨ reflexive ⟩  
  drop (suc (suc n + m)) as       ≡⟨ drop-congˡ {as = as} {n = suc (suc n + m)} {m = suc n + suc m} (cong suc (sym (+-suc n m))) ⟩  
  drop (suc n + suc m) as         ∎ where open ≈-Reasoning
------------------------------------------------------------------------
-- repeat

lookup-repeat-identity : (n : ℕ) (a : A) → lookup n (repeat a) ≡ a
lookup-repeat-identity zero a = refl
lookup-repeat-identity (suc n) a = lookup-repeat-identity n a

take-repeat-identity : (n : ℕ) (a : A) → take n (repeat a) ≡ Vec.replicate a
take-repeat-identity zero a = refl
take-repeat-identity (suc n) a = cong (a ∷_ ) (take-repeat-identity n a)

drop-repeat-identity : (n : ℕ) (a : A) → drop n (repeat a) ≡ repeat a
drop-repeat-identity zero a = refl
drop-repeat-identity (suc n) a = drop-repeat-identity n a

splitAt-repeat-identity : (n : ℕ) (a : A) → splitAt n (repeat a) ≡ (Vec.replicate a , repeat a)
splitAt-repeat-identity n a = (Inverse.f Prod.×-≡,≡↔≡ (take-repeat-identity n a , drop-repeat-identity n a))

replicate-repeat : ∀ (n : ℕ) (a : A) → (List.replicate n a ++ repeat a) ≈ (repeat a)
hd-≈ (replicate-repeat zero a) = refl
tl-≈ (replicate-repeat zero a) = reflexive
hd-≈ (replicate-repeat (suc n) a) = refl
tl-≈ (replicate-repeat (suc n) a) = replicate-repeat n a


cycle-repeat : ∀ (a : A) → cycle (List⁺.[ a ]) ≈ repeat a
hd-≈ (cycle-repeat a) = refl
tl-≈ (cycle-repeat a) = cycle-repeat a

lookup-⁺++-< : ∀ {as} (n : ℕ) (ls : List⁺ A) (n<ls : n < List⁺.length ls) → lookup n (ls ⁺++ as) ≡ lookup⁺ ls (Fin.fromℕ< n<ls) --ls List⁺.! n
lookup-⁺++-< zero ls n<ls = refl
lookup-⁺++-< (suc zero) (_ ∷ _ ∷ _) (s≤s _) = refl
lookup-⁺++-< (suc (suc n)) (l ∷ l' ∷ ls) (s≤s n<ls) = lookup-⁺++-< (suc n) (l' ∷ ls) n<ls

lookup-⁺++-≥ : ∀ {as} (n : ℕ) (ls : List⁺ A) (n≥ls : n ≥ List⁺.length ls) → lookup n (ls ⁺++ as) ≡ lookup (n ∸ List⁺.length ls) as
lookup-⁺++-≥ (suc zero) (_ ∷ []) n>ls = refl
lookup-⁺++-≥ (suc zero) (_ ∷ l ∷ ls) (s≤s ())
lookup-⁺++-≥ (suc (suc n)) (_ ∷ []) (s≤s z≤n) = refl
lookup-⁺++-≥ (suc (suc n)) (l ∷ l' ∷ ls) (s≤s n>ls) = lookup-⁺++-≥ (suc n) (l' ∷ ls) n>ls

open import Relation.Nullary using (_because_)
open import Data.Bool using (true; false)

cycle-singleton-repeat : ∀ (a : A) → cycle (a ∷ []) ≈ repeat a
hd-≈ (cycle-singleton-repeat a) = refl
tl-≈ (cycle-singleton-repeat a) = cycle-singleton-repeat a


[]++ : ∀ {as : Stream A} → ([] ++ as) ≈ as
hd-≈ []++ = refl
tl-≈ []++ = reflexive

concat-∷-⁺++ : ∀ {ls : List⁺ A} {as : Stream (List⁺ A)} → concat (ls ∷ as) ≈ (ls ⁺++ concat as)
concat-∷-⁺++ {_} {_} {ls} {as} = aux ls as (List⁺.length ls) refl
  where
    length-remove-second : ∀ (l l' : A) (ls : List A) {n : ℕ} → suc n ≡ List⁺.length (l ∷ l' ∷ ls) → n ≡ List⁺.length (l ∷ ls)
    length-remove-second _ _ _ refl = refl

    ++-⁺++ : ∀ (l : A) (ls : List A) (as : Stream A) → ((l ∷ ls) ++ as) ≈ ((l ∷ ls) ⁺++ as)
    hd-≈ (++-⁺++ l ls as) = refl
    tl-≈ (++-⁺++ l ls as) = reflexive

    ∷-++ : ∀ (l : A) (ls : List A) (as : Stream A) → (l ∷ (ls ++ as)) ≈ ((l ∷ ls) ++ as)
    hd-≈ (∷-++ l [] as) = refl
    tl-≈ (∷-++ l [] as) = reflexive
    hd-≈ (∷-++ l (l' ∷ ls) as) = refl
    tl-≈ (∷-++ l (l' ∷ ls) as) = reflexive

    aux : ∀ (ls : List⁺ A) (as : Stream (List⁺ A)) (n : ℕ) → n ≡ List⁺.length ls → concat (ls ∷ as) ≈ (ls ⁺++ concat as)
    hd-≈ (aux (l ∷ ls) as n nlen) = refl
    tl-≈ (aux (l ∷ []) as n nlen) = symmetric []++
    hd-≈ (tl-≈ (aux (l ∷ l' ∷ []) as n nlen)) = refl
    tl-≈ (tl-≈ (aux (l ∷ l' ∷ []) as n nlen)) = symmetric []++
    tl-≈ (aux (l ∷ l' ∷ l'' ∷ ls) as (suc (suc n)) nlen) = begin
      concat ((l' ∷ l'' ∷ ls) ∷ as)    ≈⟨ record { hd-≈ = refl ; tl-≈ = reflexive } ⟩
      l' ∷ concat ((l'' ∷ ls) ∷ as)    ≈⟨ ∷-congʳ (aux (l'' ∷ ls) as n (length-remove-second l' l'' ls (length-remove-second l l' (l'' ∷ ls) nlen))) ⟩
      l' ∷ ((l'' ∷ ls) ⁺++ concat as)  ≈⟨ ∷-congʳ (symmetric (++-⁺++ l'' ls (concat as))) ⟩
      l' ∷ ((l'' ∷ ls) ++ concat as)   ≈⟨ ∷-++ l' (l'' ∷ ls) (concat as) ⟩
      (l' ∷ l'' ∷ ls) ++ concat as     ∎ where open ≈-Reasoning
    
cycle-replicate : ∀ (n : ℕ) (n≢0 : n ≢ 0) (a : A) → cycle (List⁺.replicate n n≢0 a) ≈ repeat a
cycle-replicate n n≢0 a = all-lookup-repeat a (cycle (List⁺.replicate n n≢0 a)) λ k → aux-unwrap k n n≢0
  where
    aux : (n : ℕ) (m : ℕ) (n≢0 : n ≢ 0)  (k : ℕ) → lookup k ((List.replicate m a) ++ cycle (List⁺.replicate n n≢0 a)) ≡ a
    aux n zero n0 zero = refl
    aux n (suc m) n0 zero = refl
    aux zero zero n0 (suc k) = ⊥-elim (n0 refl)
    aux (suc zero) zero n0 (suc k) = begin 
      lookup k (cycle (List⁺.replicate 1 n0 a))  ≡⟨ lookup-cong k (cycle-singleton-repeat a) ⟩
      lookup k (repeat a)                        ≡⟨ lookup-repeat-identity k a ⟩  
      a                                          ∎ where open P.≡-Reasoning
    aux (suc (suc n)) zero n0 (suc k) = begin 
      lookup k (concat ((a ∷ List.replicate n a) ∷ repeat (List⁺.replicate (suc (suc n)) n0 a)))  ≡⟨ lookup-cong k concat-∷-⁺++ ⟩ 
      lookup k ((a ∷ List.replicate n a) ⁺++ cycle (List⁺.replicate (suc (suc n)) n0 a))          ≡⟨ lookup-cong k (record { hd-≈ = refl ; tl-≈ = reflexive }) ⟩ 
      lookup k ((a ∷ List.replicate n a) ++ cycle (List⁺.replicate (suc (suc n)) n0 a))           ≡⟨ aux (suc (suc n)) (suc n) n0 k ⟩ 
      a                                                                                           ∎ where open P.≡-Reasoning
    aux n (suc m) n0 (suc k) = aux n m n0 k

    aux-unwrap : ∀ (k : ℕ) (n : ℕ) (n≢0 : n ≢ 0)  → lookup k (cycle (List⁺.replicate n n≢0 a)) ≡ a
    aux-unwrap k n n≢0 = begin 
      lookup k (cycle (List⁺.replicate n n≢0 a))        ≡⟨ lookup-cong k (symmetric ([]++)) ⟩
      lookup k ([] ++ cycle (List⁺.replicate n n≢0 a))  ≡⟨ aux n 0 n≢0 k ⟩ 
      a                                                 ∎ where open P.≡-Reasoning

map-repeat : ∀ (f : A → B) a →  map f (repeat a) ≈ repeat (f a)
hd-≈ (map-repeat f a) = refl
tl-≈ (map-repeat f a) = map-repeat f a

map-drop : ∀ (f : A → B) (n) {as : Stream A} → drop n (map f as) ≈ map f (drop n as)
map-drop f zero = reflexive
map-drop f (suc n) = map-drop f n

ap-repeat : ∀ (f : A → B) a → ap (repeat f) (repeat a) ≈ repeat (f a)
hd-≈ (ap-repeat f a) = refl
tl-≈ (ap-repeat f a) = ap-repeat f a

ap-repeatˡ : ∀ (f : A → B) as → ap (repeat f) as ≈ map f as
hd-≈ (ap-repeatˡ f as) = refl
tl-≈ (ap-repeatˡ f as) = ap-repeatˡ f (Stream.tl as)

ap-repeatʳ : ∀ (fs : Stream (A → B)) a → ap fs (repeat a) ≈ map (_$ a) fs
hd-≈ (ap-repeatʳ fs a) = refl
tl-≈ (ap-repeatʳ fs a) = ap-repeatʳ (Stream.tl fs) a

map-++ : ∀ (f : A → B) as xs → map f (xs ++ as) ≈ (List.map f xs ++ map f as)
hd-≈ (map-++ f as List.[]) = refl
hd-≈ (map-++ f as (x List.∷ xs)) = refl
tl-≈ (map-++ f as List.[]) = reflexive
tl-≈ (map-++ f as (x List.∷ xs)) = map-++ f as xs

map-⁺++ : ∀ (f : A → B) as xs → map f (xs ⁺++ as) ≈ (List⁺.map f xs ⁺++ map f as)
hd-≈ (map-⁺++ f as xs) = refl
tl-≈ (map-⁺++ f as xs) = map-++ f as (List⁺.tail xs)

concat-cong : ∀ {as bs : Stream (List⁺ A)} → as ≈ bs → concat as ≈ concat bs
hd-≈ (concat-cong as≈bs) = cong List⁺.head (hd-≈ as≈bs)
tl-≈ (concat-cong {as = as} {bs = bs} as≈bs) with Stream.hd as | Stream.hd bs | hd-≈ as≈bs
... | a ∷ [] | .a ∷ [] | refl = concat-cong (tl-≈ as≈bs)
... | a ∷ a' ∷ as' | .a ∷ .a' ∷ .as' | refl = concat-cong (∷-congʳ (tl-≈ as≈bs))

concat-∷ : ∀ (a a' : A) (as' : List A) (as : Stream (List⁺ A)) → concat ((a ∷ (a' ∷ as')) ∷ as) ≈ (a ∷ concat ((a' ∷ as') ∷ as))
hd-≈ (concat-∷ a a' as' as) = refl
tl-≈ (concat-∷ a a' as' as) = reflexive

map-concat : ∀ (f : A → B) (as : Stream (List⁺ A)) → map f (concat as) ≈ concat (map (List⁺.map f) as)
map-concat f as = all-lookup λ n → aux n as
  where
    aux : ∀ n as → lookup n (map f (concat as)) ≡ lookup n (concat (map (List⁺.map f) as))
    aux zero _ = refl
    aux (suc n) as with hd as 
    ... | _ ∷ [] = aux n (tl as)
    ... | a ∷ a' ∷ as' = begin 
      lookup (suc n) (map f (concat ((a ∷ (a' ∷ as')) ∷ tl as)))               ≡⟨ lookup-cong (suc n) (map-cong (concat-∷ a a' as' (tl as))) ⟩ 
      lookup (suc n) (map f (a ∷ concat ((a' ∷ as') ∷ tl as)))                 ≡⟨⟩
      lookup n (map f (concat ((a' ∷ as') ∷ tl as)))                           ≡⟨ aux n ((a' ∷ as') ∷ tl as) ⟩
      lookup n (concat (map (List⁺.map f) ((a' ∷ as') ∷ tl as)))               ≡⟨ lookup-cong n (concat-cong (record { hd-≈ = refl ; tl-≈ = reflexive })) ⟩
      lookup n (concat ((f a' ∷ List.map f as') ∷ map (List⁺.map f) (tl as)))  ∎ where open P.≡-Reasoning


map-cycle : ∀ (f : A → B) as → map f (cycle as) ≈ cycle (List⁺.map f as)
map-cycle f as = all-lookup (λ n → aux n as)
  where
    aux : ∀ n as → lookup n (map f (cycle as)) ≡ lookup n (cycle (List⁺.map f as))
    aux zero as = refl
    aux (suc n) (a ∷ []) = begin 
      lookup (suc n) (map f (cycle (List⁺.[ a ])))  ≡⟨ lookup-cong (suc n) (map-cong (cycle-repeat a)) ⟩ 
      lookup (suc n) (map f (repeat a))  ≡⟨ lookup-cong (suc n) (map-repeat f a) ⟩ 
      lookup (suc n) (repeat (f a))  ≡⟨ lookup-cong (suc n) (symmetric (cycle-repeat (f a))) ⟩ 
      lookup (suc n) (cycle (List⁺.map f (List⁺.[ a ])))  ∎ where open P.≡-Reasoning
    aux (suc n) (a ∷ a' ∷ as) = begin 
      lookup (suc n) (map f (cycle (a ∷ a' ∷ as)))  ≡⟨⟩ 
      lookup n (map f (concat ((a' ∷ as) ∷ repeat (a ∷ a' ∷ as))))    ≡⟨ lookup-cong n (map-cong concat-∷-⁺++) ⟩ 
      lookup n (map f ((a' ∷ as) ⁺++ concat (repeat (a ∷ a' ∷ as))))  ≡⟨ lookup-cong n (map-⁺++ f (concat (repeat (a ∷ a' ∷ as))) (a' ∷ as)) ⟩ 
      lookup n (List⁺.map f (a' ∷ as) ⁺++ map f (concat (repeat (a ∷ a' ∷ as))))  ≡⟨ lookup-cong n (⁺++-congʳ (map-concat f (repeat (a ∷ a' ∷ as)))) ⟩ 
      lookup n (List⁺.map f (a' ∷ as) ⁺++ concat (map (List⁺.map f) (repeat (a ∷ a' ∷ as))))  ≡⟨ lookup-cong n (⁺++-congʳ (concat-cong (map-repeat (List⁺.map f) (a ∷ a' ∷ as)))) ⟩ 
      lookup n (List⁺.map f (a' ∷ as) ⁺++ concat (repeat (List⁺.map f (a ∷ a' ∷ as))))  ≡⟨ lookup-cong n (symmetric concat-∷-⁺++) ⟩ 
      lookup n (concat (List⁺.map f (a' ∷ as) ∷ repeat (List⁺.map f (a ∷ a' ∷ as))))  ≡⟨⟩
      lookup (suc n) (cycle (List⁺.map f (a ∷ a' ∷ as))) ∎ where open P.≡-Reasoning

------------------------------------------------------------------------
-- interleave

even-odd-interleave : ∀ (as : Stream A) → interleave (even as) (odd as) ≈ as
hd-≈ (even-odd-interleave as) = refl
hd-≈ (tl-≈ (even-odd-interleave as)) = refl
tl-≈ (tl-≈ (even-odd-interleave as)) = even-odd-interleave (tl (tl as))

interleave-split : ∀ (as : Stream A) → Prod.uncurry interleave (split as) ≈ as
interleave-split as = even-odd-interleave as

------------------------------------------------------------------------
-- Functor laws

map-identity : ∀ (as : Stream A) → map id as ≈ as
hd-≈ (map-identity as) = refl
tl-≈ (map-identity as) = map-identity (tl as)

map-map-fusion : ∀ (f : A → B) (g : B → C) as → map g (map f as) ≈ map (g ∘ f) as
hd-≈ (map-map-fusion f g as) = refl
tl-≈ (map-map-fusion f g as) = map-map-fusion f g (tl as)

------------------------------------------------------------------------
-- splitAt

splitAt-map : ∀ n (f : A → B) as → splitAt n (map f as) ≡ Prod.map (Vec.map f) (map f) (splitAt n as)
splitAt-map zero f as = refl
splitAt-map (suc n) f as = cong (Prod.map₁ (f (hd as)  Vec.∷_)) (splitAt-map n f (tl as))

------------------------------------------------------------------------
-- iterate

lookup-iterate-identity : ∀ n f (a : A) → lookup n (iterate f a) ≡ fold a f n
lookup-iterate-identity zero f a = refl
lookup-iterate-identity (suc n) f a = begin 
  lookup (suc n) (iterate f a) ≡⟨⟩
  lookup n (iterate f (f a))   ≡⟨ lookup-iterate-identity n f (f a) ⟩ 
  fold (f a) f n               ≡⟨ fold-pull (const ∘′ f) (f a) refl (λ _ → refl) n ⟩ 
  f (fold a f n)               ≡⟨⟩
  fold a f (suc n)             ∎ where open P.≡-Reasoning
