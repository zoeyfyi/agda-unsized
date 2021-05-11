{-# OPTIONS --without-K --safe #-}

module Unsized.Data.Tree.Rose.Show where

open import Level using (Level)
open import Data.Bool.Base using (Bool; true; false; if_then_else_; _∧_)
open import Data.DifferenceList as DList renaming (DiffList to DList) using ()
open import Data.List.Base as List using (List; []; [_]; _∷_; _∷ʳ_)
open import Data.Nat.Base using (ℕ; _∸_)
open import Data.Product using (_×_; _,_)
open import Data.String.Base hiding (show)
open import Unsized.Data.Tree.Rose using (Rose; node; map)
open import Function.Base using (flip; _∘′_; id)

private
  variable
    ℓ : Level
    A : Set ℓ

display : Rose (List String) → List String
display t = DList.toList (go (([] , t) ∷ []))
    where
    padding : Bool → List Bool → String → String
    padding dir? [] str = str
    padding dir? (b ∷ bs) str = 
      (if (dir? ∧ (List.null bs)) 
       then (if b then " ├ " else " └ ") 
       else (if b then " │ "  else "   "))
      ++ padding dir? bs str

    nodePrefixes : List A → List Bool
    nodePrefixes as = true ∷ List.replicate (List.length as ∸ 1) false

    childrenPrefixes : List A → List Bool
    childrenPrefixes as = List.replicate (List.length as ∸ 1) true ∷ʳ false

    go : List (List Bool × Rose (List String)) → DList String
    go' : List (List Bool) → List (Rose (List String)) → DList String
    go'' : List Bool → Rose (List String) → DList String

    go []              = DList.[]
    go ((bs , t) ∷ ts) = go'' bs t DList.++ go ts

    go' bs [] = DList.[]
    go' [] (_ ∷ _) = DList.[]
    go' (b ∷ bs) (t ∷ ts) = go'' b t DList.++ go' bs ts

    go'' bs (node a ts₁) = let bs′ = List.reverse bs in
      DList.fromList (List.zipWith (flip padding bs′) (nodePrefixes a) a)
      DList.++ go' (List.map (_∷ bs) (childrenPrefixes ts₁)) ts₁
   
show : (A → List String) → Rose A → List String
show toString = display ∘′ map toString

showSimple : (A → String) → Rose A → List String
showSimple toString = show ([_] ∘′ toString)
