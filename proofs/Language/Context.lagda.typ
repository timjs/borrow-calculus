```agda
{-# OPTIONS --allow-unsolved-metas #-}
module Language.Context where

open import Prelude
open import Language.Syntax

import Language.Syntax.Quantity as Quantity

infixl 8  _/_  -- _÷_
infixl 7  _∩_
infixl 6  _∪_  _∪ⁿ_×_  _–_  _–ⁿ_×_
infix  6  ⌊_⌋_  ⌈_⌉_
-- infixr 4  _,_
infix  1  _∋_↝_  _∋_∶_
```

= Contexts

```agda
data Context : Set where
  ∅ : Context
  -- _,_∙_∶_ : Context → Quantity → Name → Type → Context
  _,_ : Context → Parameter → Context
```

== Union and Intersection

```agda
_∪_ : Context → Context → Context
Γ ∪ ∅ = Γ
Γ ∪ (Γ' , q ∙ x ∶ τ) = (Γ , q ∙ x ∶ τ) ∪ Γ'

_∪ⁿ_×_ : Context → (n : ℕ) → Parameter ^ n → Context
Γ ∪ⁿ 0 × [] = Γ
Γ ∪ⁿ suc n × (q ∙ x ∶ τ ∷ q∙x∶τⁿ) = (Γ , q ∙ x ∶ τ) ∪ⁿ n × q∙x∶τⁿ

_∩_ : Context → Context → Context
_∩_ = {!   !}
```

== Filters

```agda
_/_ : Context → Quantity → Context
∅ / _ = ∅
(Γ , q ∙ x ∶ τ) / q₀ with q Quantity.≟ q₀
... | yes refl = Γ / q₀ , q ∙ x ∶ τ
... | no ¬q≡q₀ = Γ / q₀

_–_ : Context → Name → Context
∅ – _ = ∅
(Γ , q ∙ x ∶ τ) – x₀ with x String.≟ x₀
... | yes refl = Γ -- – x₀
... | no ¬x≡x₀ = Γ – x₀ , q ∙ x ∶ τ

-- _–′_ : Context → Parameter → Context
-- Γ –′ _ ∙ x₀ ∶ _ = Γ – x₀

_–ⁿ_×_ : Context → (n : ℕ) → Name ^ n → Context
Γ –ⁿ _ × q∙x∶τⁿ = Vec.foldl′ _–_ Γ q∙x∶τⁿ
```

∅ – _ = ∅
Γ – [] = Γ
(Γ , q ∙ x ∶ t) – (_ ∙ x₀ ∶ _ ∷ q∙x∶τⁿ) with x String.≟ x₀
... | yes refl = {!   !}
... | no ¬x≡x₀ = {!   !}

== Membership

```agda
data _∋_↝_ : Context → Parameter → Context → Set where
  ∋here-1 : ∀{Γ x τ} →
    -----------------------------
    Γ , 𝟏 ∙ x ∶ τ ∋ 𝟏 ∙ x ∶ τ ↝ Γ
  ∋here-ε : ∀{Γ x τ} →
    -----------------------------------------
    Γ , ε ∙ x ∶ τ ∋ ε ∙ x ∶ τ ↝ Γ , ε ∙ x ∶ τ
  ∋here-ω : ∀{Γ q x τ} →
    -----------------------------------------
    Γ , ω ∙ x ∶ τ ∋ q ∙ x ∶ τ ↝ Γ , ω ∙ x ∶ τ
  -- ∋weak-1 : ∀{Γ x τ} →
  --   -----------------------------------------
  --   Γ , ω ∙ x ∶ τ ∋ 𝟏 ∙ x ∶ τ ↝ Γ , ω ∙ x ∶ τ
  -- ∋weak-ε : ∀{Γ x τ} →
  --   -----------------------------------------
  --   Γ , ω ∙ x ∶ τ ∋ ε ∙ x ∶ τ ↝ Γ , ω ∙ x ∶ τ
  ∋there : ∀{Γ q x τ Γ' q' x' τ'} →
    x' ≢ x →
    Γ ∋ q ∙ x ∶ τ ↝ Γ' →
    ------------------------------------------------
    Γ , q' ∙ x' ∶ τ' ∋ q ∙ x ∶ τ ↝ Γ' , q' ∙ x' ∶ τ'
```

```agda
_∋_∶_ : Context → Name → Type → Set
Δ ∋ C ∶ ⟨q∙x∶τⁿ⟩⟶τ₀ = Δ ∋ _ ∙ C ∶ ⟨q∙x∶τⁿ⟩⟶τ₀ ↝ _
```



```agda
-- Modifify quantity of one name
[_]¹⟨_↦_⟩_ : Context → Quantity → Quantity → Name → Context
[ ∅ ]¹⟨ _ ↦ _ ⟩ _ = ∅
[ Γ , q ∙ x ∶ τ ]¹⟨ q₁ ↦ q₂ ⟩ y with x String.≟ y | q Quantity.≟ q₁
... | yes refl | yes refl = Γ , q₂ ∙ x ∶ τ
... | _ | _ = [ Γ ]¹⟨ q₁ ↦ q₂ ⟩ x , q ∙ x ∶ τ

-- Borrow one name
⌊_⌋¹_ : Context → Name → Context
⌊_⌋¹_ = [_]¹⟨ 𝟏 ↦ ε ⟩_

-- Unborrow one name
⌈_⌉¹_ : Context → Name → Context
⌈_⌉¹_ = [_]¹⟨ ε ↦ 𝟏 ⟩_

-- Modify quantity of multiple names
[_]⟨_↦_⟩_ : Context → Quantity → Quantity → Name * → Context
[ Γ ]⟨ q₁ ↦ q₂ ⟩ x* = List.foldl [_]¹⟨ q₁ ↦ q₂ ⟩_ Γ x*

-- Borrow one name
⌊_⌋_ : Context → Name * → Context
⌊_⌋_ = [_]⟨ 𝟏 ↦ ε ⟩_

-- Unborrow one name
⌈_⌉_ : Context → Name * → Context
⌈_⌉_ = [_]⟨ ε ↦ 𝟏 ⟩_
```




{-
⌊ Γ , q ∙ x ∶ τ ⌋¹ y with x String.≟ y | q Quantity.≟ 𝟏
... | yes refl | yes refl = Γ , ε ∙ x ∶ τ
... | _ | _ = ⌊ Γ ⌋¹ x , q ∙ x ∶ τ

-- Unborrow one name
⌈_⌉¹_ : Context → Name → Context
⌈ ∅ ⌉¹ _ = ∅
⌈ Γ , q ∙ x ∶ τ ⌉¹ y with x String.≟ y | q Quantity.≟ 𝟏
... | yes refl | yes refl = Γ , ε ∙ x ∶ τ
... | _ | _ = ⌈ Γ ⌉¹ x , q ∙ x ∶ τ
-}

-- _∌_⦂_ : Context → Name → Type → Set
-- Γ ∌ x ⦂ τ = ¬ (Γ ∋ x ⦂ τ)
--
-- data _∋!_⦂_ : Context → Name → Type → Set where
--   here : ∀ {Γ x τ} →
--     Γ ∌ x ⦂ τ →
--     ----------------
--     Γ , x ⦂ τ ∋! x ⦂ τ
--   there : ∀ {Γ x y τ σ} →
--     x ≢ y →
--     Γ ∋! x ⦂ τ →
--     ----------------
--     Γ , y ⦂ σ ∋! x ⦂ τ
