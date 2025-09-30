module Language.Syntax.Type where

open import Prelude

open import Language.Syntax.Name
open import Language.Syntax.Quantity

data Type : Set
record Parameter : Set
record Constructor : Set

infix  9  _∙_∶_

record Parameter where
  inductive
  constructor _∙_∶_
  field
    quantity : Quantity
    name : Name
    type : Type

names : Parameter * → Name *
names = List.map Parameter.name

record Constructor where
  inductive
  constructor _[_]
  field
    name : Name
    type : ∀{n} → Type ^ n

data Type where
  _⟶_ : ∀ {n} → Parameter ^ n → Type → Type
  ⟨_⟩ : ∀{m} → Constructor ^ m → Type
