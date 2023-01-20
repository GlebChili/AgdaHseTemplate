{-# OPTIONS --without-K --safe #-}

module AgdaHseTemplate where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
                           renaming (Set to 𝒰)
                           public

data 𝟙 : 𝒰 where
    * : 𝟙

data 𝟘 : 𝒰 where

data Bool : 𝒰 where
    True : Bool
    False : Bool

not : Bool → Bool
not True = False
not False = True

example1 : Bool
example1 = not True

example2 : Bool
example2 = not False
    
𝟘-elim : {A : 𝒰} → 𝟘 → A
𝟘-elim = λ ()

𝟙-is-final : {A : 𝒰} → A → 𝟙
𝟙-is-final {A} = λ (x : A) → *

¬ : 𝒰 → 𝒰
¬ A = A → 𝟘

TripleNegationLemma : {A : 𝒰} → (¬ (¬ (¬ A))) → (¬ A)
TripleNegationLemma {A} t = λ (x : A) →  t (λ (z : (A → 𝟘)) → z x) 

data Σ {A : 𝒰} (B : A → 𝒰) : 𝒰 where
    _,_ : (a : A) → (B a) → Σ {A} B

Sigma : (A : 𝒰) → (B : A → 𝒰) → 𝒰
Sigma A B = Σ {A} B

syntax Sigma A (λ x → b) = Σ x ꞉ A , b

_×_ : 𝒰 → 𝒰 → 𝒰
A × B = Σ {A} (λ x → B)

data _∔_ (A B : 𝒰) : 𝒰 where
    inl : A → A ∔ B
    inr : B → A ∔ B

AndLemma₁ : {A B : 𝒰} → A × B → A
AndLemma₁ (a , x) = a

AndLemma₂ : {A B : 𝒰} → A × B → B
AndLemma₂ (a , b) = b

AndLemma₃ : {A B : 𝒰} → A → B → A × B
AndLemma₃ a b = a , b

AndLemma₄ : {A B C : 𝒰} → (A → C) → (A × B → C)
AndLemma₄ f (a , x) = f a

AndLemma₅ : {A B : 𝒰} → A × B → B × A
AndLemma₅ (a , b) = b , a

AndLemma₆ : {A B C : 𝒰} → (B → C) → (A × B → C)
AndLemma₆ f p = AndLemma₄ f (AndLemma₅ p)

OrLemma : {A B C : 𝒰} → (A → C) → (B → C) → (A ∔ B → C)
OrLemma f g (inl x) = f x
OrLemma f g (inr x) = g x

data ℕ : 𝒰 where
    zero : ℕ
    suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
a + zero = a
a + suc b = suc (a + b)

addExample : ℕ
addExample = 10 + 6

data _≡_ {A : 𝒰} : A → A → 𝒰 where
    refl : (x : A) → x ≡ x

reflexivity : {A : 𝒰} → (x : A) → x ≡ x
reflexivity _ = refl _

sym : {A : 𝒰} → (x y : A) → x ≡ y → y ≡ x
sym x .x (refl .x) = refl x

_∘_ : {A : 𝒰} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl x ∘ refl x = refl x

ap : {A B : 𝒰} → {f : A → B} → {x y : A} → (x ≡ y) → (f x) ≡ (f y)
ap (refl _) = refl _

transport : {A : 𝒰} → {B : A → 𝒰} → {x y : A} → (x ≡ y) → B x → B y
transport (refl _) = λ x → x 

_≢_ : {A : 𝒰} → A → A → 𝒰
x ≢ y = ¬ (x ≡ y)

noneqLemma : 1 ≢ 0
noneqLemma = λ eq → (transport {ℕ} {helper} {1} {0} (eq) *)
    where
        helper : ℕ → 𝒰
        helper zero = 𝟘
        helper (suc n) = 𝟙
    