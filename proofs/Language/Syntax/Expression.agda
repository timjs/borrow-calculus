module Language.Syntax.Expression where

open import Prelude

open import Language.Syntax.Name
open import Language.Syntax.Quantity
open import Language.Syntax.Type

data Expression : Set
record Branch : Set

data Expression where
  ` : Name → Expression
  val_∙_＝_⨾_ : Quantity → Name → Expression → Expression → Expression
  [_∣_] : Name * → Expression → Expression
  fn⟨_⟩_ : ∀{n} → Parameter ^ n → Expression → Expression
  _⟨_⟩ : ∀{n} → Expression → Expression ^ n → Expression
  _⟪_⟫ : ∀{n} → Name → Expression ^ n → Expression
  match_∙_[_] : ∀ {m} → Quantity → Expression → Branch ^ m → Expression

record Branch where
  inductive
  constructor _⟪_×_⟫↦_
  field
    name : Name
    arity : ℕ
    binders : Name ^ arity
    body : Expression
