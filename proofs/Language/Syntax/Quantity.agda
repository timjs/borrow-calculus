module Language.Syntax.Quantity where

open import Prelude

data Quantity : Set where
  ε 𝟏 ω : Quantity

_≟_ : (q₁ : Quantity) → (q₂ : Quantity) → Dec (q₁ ≡ q₂)
ε ≟ ε = yes refl
ε ≟ 𝟏 = no λ()
ε ≟ ω = no λ()
𝟏 ≟ ε = no λ()
𝟏 ≟ 𝟏 = yes refl
𝟏 ≟ ω = no λ()
ω ≟ ε = no λ()
ω ≟ 𝟏 = no λ()
ω ≟ ω = yes refl

-- instance
--   Quantity-≡-isDecEquivalence = isDecEquivalence _?=_
