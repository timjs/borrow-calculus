module Experiments where

open import Prelude
import Data.String.Instances
import Data.Nat.Instances

_⊕_ : {n : ℕ} → ℕ → ℕ → ℕ
_⊕_ {n} a b = a + b + n -- ok!
-- a ⊕ b = a + b + n -- n not in scope

use-⊕ : _⊕_ {1} 2 3 ≡ 6 -- ok!
-- use-⊕ : 2 (_⊕_ {1}) 3  ≡ 6
use-⊕ = refl

it = String-≡-isDecEquivalence

test1 : (x : String) → (y : String) → Dec (x ≡ y)
test1 x y with x String.≟ y
... | yes refl = yes refl
... | no ¬x≡y = no ¬x≡y

test2 : (x : String) → (y : String) → Dec (x ≡ y)
test2 x y with x ≟ y
... | yes refl = yes refl
... | no ¬x≡y = no ¬x≡y

Name : Set
Name = String

test3 : (x : Name) → (y : Name) → Dec (x ≡ y)
test3 x y with x ≟ y
... | yes refl = yes refl
... | no ¬x≡y = no ¬x≡y

record Parameter : Set where
  inductive
  constructor _∙_∶_
  field
    quantity : ℕ
    name : Name
    type : String

_≟ᵖ_ : (p₁ : Parameter) → (p₂ : Parameter) → Dec (p₁ ≡ p₂)
(q₁ ∙ x₁ ∶ τ₁) ≟ᵖ (q₂ ∙ x₂ ∶ τ₂) with q₁ ≟ q₂ | x₁ ≟ x₂ | τ₁ ≟ τ₂
... | yes refl | yes refl | yes refl = yes refl
... | pq | px | pt = no {!   !}
