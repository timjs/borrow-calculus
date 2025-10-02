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
infix  3  _∋_↝_  _∋_∶_
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
  ∋there : ∀{Γ q x τ Γ′ q′ x′ τ′} →
    x ≢ x′ → -- Note: only search further up in the context iff we know the head is not what we're looking for
    Γ ∋ q ∙ x ∶ τ ↝ Γ′ →
    ------------------------------------------------
    Γ , q′ ∙ x′ ∶ τ′ ∋ q ∙ x ∶ τ ↝ Γ′ , q′ ∙ x′ ∶ τ′
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

== Extensionality

To prove the `no` cases in `lookup?` below, we need an extensionality lemma.
It states that, if we know we cannot lookup a binding `x` in `Γ`,
we won't be able to look it up in `Γ` extended with a binding `x′` unequal to `x`.

```agda
ext∋ : ∀ {Γ q x q′ x′ τ′} →
  x ≢ x′ →
  ¬ (∃[ τ ] ∃[ Γ′ ] Γ ∋ q ∙ x ∶ τ ↝ Γ′) →
  ----------------------------------------------------
  ¬ (∃[ τ ] ∃[ Γ′ ] Γ , q′ ∙ x′ ∶ τ′ ∋ q ∙ x ∶ τ ↝ Γ′)
ext∋ x≢x′ _ (τ , Γ′ , ∋here-1) = x≢x′ refl
ext∋ x≢x′ _ (τ , Γ′ , ∋here-ε) = x≢x′ refl
ext∋ x≢x′ _ (τ , Γ′ , ∋here-ω) = x≢x′ refl
ext∋ x≢x′ ¬∃ (τ , Γ′ , ∋there x′≢x″ ∋x″) = ¬∃ (τ , _ , ∋x″)
```

== Lookup

Some lemma's we'll need below.
If we found a binding in the context,
but the quantity doesn't match according to the rules we specified in `_∋_↝_` above,
we simply cannot lookup that binding.
```agda
∌here-ε𝟏 : ∀{Γ x₀ τ₀ τ Γ′} → Γ , (ε ∙ x₀ ∶ τ₀) ∋ 𝟏 ∙ x₀ ∶ τ ↝ Γ′ → ⊥
∌here-ε𝟏 (∋there x₀≢x₀ _) = x₀≢x₀ refl

∌here-εω : ∀{Γ x₀ τ₀ τ Γ′} → Γ , (ε ∙ x₀ ∶ τ₀) ∋ ω ∙ x₀ ∶ τ ↝ Γ′ → ⊥
∌here-εω (∋there x₀≢x₀ _) = x₀≢x₀ refl

∌here-𝟏ε : ∀{Γ x₀ τ₀ τ Γ′} → Γ , (𝟏 ∙ x₀ ∶ τ₀) ∋ ε ∙ x₀ ∶ τ ↝ Γ′ → ⊥
∌here-𝟏ε (∋there x₀≢x₀ _) = x₀≢x₀ refl

∌here-𝟏ω : ∀{Γ x₀ τ₀ τ Γ′} → Γ , (𝟏 ∙ x₀ ∶ τ₀) ∋ ω ∙ x₀ ∶ τ ↝ Γ′ → ⊥
∌here-𝟏ω (∋there x₀≢x₀ _) = x₀≢x₀ refl
```

Now we prove that, give a quantity `q` and a name `x`,
we can decide on it's existence in `Γ`.
Either:
1. it is here and the quantities match
2. it is here but the quantities don't match
3. it is there
4. it isn't there at all
For cases (2) we need the absurd lemma's above.
For case (4) we need the extensionality lemma.
```agda
lookup? :
  (Γ : Context) →
  (q : Quantity) →
  (x : Name) →
  ---------------------------------------
  Dec (∃[ τ ] ∃[ Γ′ ] Γ ∋ q ∙ x ∶ τ ↝ Γ′)
lookup? ∅ _ _ = no λ ()
lookup? (Γ , q₀ ∙ x₀ ∶ τ₀) q x with x String.≟ x₀
lookup? (Γ , ε  ∙ x  ∶ τ₀) ε x | yes refl = yes (τ₀ , (Γ , ε ∙ x ∶ τ₀) , ∋here-ε)
lookup? (Γ , ε  ∙ x  ∶ τ₀) 𝟏 x | yes refl = no λ where (_ , _ , ∋ε𝟏) → ∌here-ε𝟏 ∋ε𝟏
lookup? (Γ , ε  ∙ x  ∶ τ₀) ω x | yes refl = no λ where (_ , _ , ∋εω) → ∌here-εω ∋εω
lookup? (Γ , 𝟏  ∙ x  ∶ τ₀) ε x | yes refl = no λ where (_ , _ , ∋𝟏ε) → ∌here-𝟏ε ∋𝟏ε
lookup? (Γ , 𝟏  ∙ x  ∶ τ₀) 𝟏 x | yes refl = yes (τ₀ , Γ , ∋here-1)
lookup? (Γ , 𝟏  ∙ x  ∶ τ₀) ω x | yes refl = no λ where (_ , _ , ∋𝟏ω) → ∌here-𝟏ω ∋𝟏ω
lookup? (Γ , ω  ∙ x  ∶ τ₀) q x | yes refl = yes (τ₀ , (Γ , ω ∙ x ∶ τ₀) , ∋here-ω)
lookup? (Γ , q₀ ∙ x₀ ∶ τ₀) q x | no ¬x≡x₀ with lookup? Γ q x
... | yes (τ , Γ′ , ∋x) = yes (τ , (Γ′ , q₀ ∙ x₀ ∶ τ₀) , ∋there ¬x≡x₀ ∋x)
... | no ¬∃ = no (ext∋ ¬x≡x₀ ¬∃)
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
