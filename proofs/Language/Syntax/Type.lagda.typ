```agda
{-# OPTIONS --allow-unsolved-metas #-}
module Language.Syntax.Type where

open import Prelude

open import Language.Syntax.Name
open import Language.Syntax.Quantity

import Data.Vec.Properties as Vec
```

We define `Type`s, `Parameter`s, and `Constructor`s simultaneously.
```agda
data Type : Set
record Parameter : Set
record Constructor : Set

infix 10  _⟶_
infix  9  _∙_∶_
```

Parameters have a `quantity`, `name`, and `type`.
We define selector functions over parameter vectors
to get access to the appropriate fields.
We use these selector functions in typing rules to make clear the relation between
parameter vectors and their components.
```agda
record Parameter where
  inductive
  constructor _∙_∶_
  field
    quantity : Quantity
    name : Name
    type : Type

quantities : ∀{n} → Parameter ^ n → Quantity ^ n
quantities = Vec.map Parameter.quantity

names : ∀{n} → Parameter ^ n → Name ^ n
names = Vec.map Parameter.name

types : ∀{n} → Parameter ^ n → Type ^ n
types = Vec.map Parameter.type
```

```agda
record Constructor where
  inductive
  constructor _⟪_⟫ -- Todo: change
  field
    name : Name
    type : ∀{n} → Type ^ n
```

```agda
data Type where
  _⟶_ : ∀{n} → Parameter ^ n → Type → Type
  ⟨|_|⟩ : ∀{m} → Constructor ^ m → Type -- Todo: change
```

== Decidable equality

For type synthesis, we need decidable equality on `Type`s and `Parameter`s.

```agda
_≟ᵖ_ : (p₁ : Parameter) → (p₂ : Parameter) → Dec (p₁ ≡ p₂)
_≟ᶜ_ : (s₁ : Constructor) → (s₂ : Constructor) → Dec (s₁ ≡ s₂)
_≟ᵗ_ : (τ₁ : Type) → (τ₂ : Type) → Dec (τ₁ ≡ τ₂)

instance
  Parameter-≡-isDecEquivalence = isDecEquivalence _≟ᵖ_
  Constructor-≡-isDecEquivalence = isDecEquivalence _≟ᶜ_
  Type-≡-isDecEquivalence = isDecEquivalence _≟ᵗ_

(q₁ ∙ x₁ ∶ τ₁) ≟ᵖ (q₂ ∙ x₂ ∶ τ₂) with q₁ ≟ q₂ | x₁ ≟ x₂ | τ₁ ≟ τ₂
... | yes refl | yes refl | yes refl = yes refl
... | pq | px | pt = no {!   !}

(C₁ ⟪ τⁿ₁ ⟫) ≟ᶜ (C₂ ⟪ τⁿ₂ ⟫) with C₁ ≟ C₂ | τⁿ₁ ≟ τⁿ₂
... | yes refl | yes p = {! p !} -- yes refl
... | pC | pt = no {!   !}

t1 ≟ᵗ t2 = {!   !}
```

(n × x ⟶ t0) ≟ᵗ (n′ × x′ ⟶ t0′) = {!  !}
(n × x ⟶ t1) ≟ᵗ (⟨∣ x₁ ∣⟩) = {!   !}
⟨∣ cs ∣⟩ ≟ᵗ t2 = {!   !}
