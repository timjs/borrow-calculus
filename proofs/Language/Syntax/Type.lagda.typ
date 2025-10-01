```agda
module Language.Syntax.Type where

open import Prelude

open import Language.Syntax.Name
open import Language.Syntax.Quantity
```

We define `Type`s, `Parameter`s, and `Constructor`s simultaneously.
```agda
data Type : Set
record Parameter : Set
record Constructor : Set

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
  constructor _[_] -- Todo: change
  field
    name : Name
    type : ∀{n} → Type ^ n
```

```agda
data Type where
  _×_⟶_ : (n : ℕ) → Parameter ^ n → Type → Type
  ⟨∣_∣⟩ : ∀{m} → Constructor ^ m → Type -- Todo: change
```
