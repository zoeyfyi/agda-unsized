{-# OPTIONS --without-K --safe #-}

module Unsized.Util.Nat where

open import Data.Nat
open import Data.Nat.Properties

private
  variable
    m n o : ℕ

m≤o⇒n≤o⇒m⊔n≤o : m ≤ o → n ≤ o → m ⊔ n ≤ o
m≤o⇒n≤o⇒m⊔n≤o {zero} x x₁ = x₁
m≤o⇒n≤o⇒m⊔n≤o {suc _} {n = zero} x x₁ = x
m≤o⇒n≤o⇒m⊔n≤o {suc m} {n = suc n} (s≤s x) (s≤s x₁) = s≤s (m≤o⇒n≤o⇒m⊔n≤o x x₁)

m≤n⇒m≤n+o : m ≤ n → m ≤ n + o
m≤n⇒m≤n+o {zero} x = z≤n
m≤n⇒m≤n+o {suc m} {suc n} (s≤s x) = s≤s (m≤n⇒m≤n+o x)

m≤o⇒m≤n+o : m ≤ o → m ≤ n + o
m≤o⇒m≤n+o {zero} {o} x = z≤n
m≤o⇒m≤n+o {suc m} {suc o} {n} (s≤s x) rewrite +-suc n o = s≤s (m≤o⇒m≤n+o x)