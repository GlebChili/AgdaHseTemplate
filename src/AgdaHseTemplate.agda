{-# OPTIONS --without-K --safe #-}

module AgdaHseTemplate where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
                           renaming (Set to 𝒰)
                           public

data 𝟘 : 𝒰 where

𝟘-elim : ({A : 𝒰} → (𝟘 → A))
𝟘-elim = λ ()

data 𝟙 : 𝒰 where
    * : 𝟙

--- d : B -> {A : 𝒰} → A → 𝟙, b : B, d b : {A : 𝒰} → A → 𝟙
𝟙-terminal : {A : 𝒰} → A → 𝟙
𝟙-terminal {A} = λ (a : A) → *

data Bool : 𝒰 where
    True : Bool
    False : Bool

not : Bool → Bool
not True = False
not False = True

data ℕ : 𝒰 where
    zero : ℕ
    suc : ℕ → ℕ

add : ℕ → ℕ → ℕ
add x zero = x
add x (suc y) = suc (add x y)

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
x + y = add x y

data _≡_ {A : 𝒰} : A → A → 𝒰 where
    refl : (x : A) → x ≡ x

ap : {A B : 𝒰} → {f : A → B} → {x y : A} → (x ≡ y) → (f x) ≡ (f y)
ap {A} {B} {f} {x} {.x} (refl .x) = refl (f x)

lemma : (y : ℕ) → (0 + y) ≡ y
lemma = {!   !}

commute : (x y : ℕ) → (x + y) ≡ (y + x)
commute = {!   !}