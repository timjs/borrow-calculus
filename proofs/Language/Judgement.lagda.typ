```agda
{-# OPTIONS --allow-unsolved-metas #-}
module Language.Judgement where

open import Prelude

open import Language.Context public
open import Language.Syntax public

infix  3  _⊢_∙_∶_⊣_  _⊩_×_∙_∶_⊣_  _⊩→_×_∙_of_as_∶_⊣_  -- Note: Fix precedence (higher than ∃ 2, lower than ...)

data _⊢_∙_∶_⊣_ : Context → Quantity → Expression → Type → Context → Set
data _⊩_×_∙_∶_⊣_ : Context → (n : ℕ) → Quantity ^ n → Expression ^ n → Type ^ n → Context → Set
data _⊩→_×_∙_of_as_∶_⊣_ : Context → (m : ℕ) → Quantity → Quantity → Branch ^ m → Type → Type → Context → Set

data _⊢_∙_∶_⊣_ where
  ---- Lookup ----
  ⊢var : ∀{Γ₀ Γ₁ q x τ} →
    Γ₀ ∋ q ∙ x ∶ τ ↝ Γ₁ →
    ----------------------
    Γ₀ ⊢ q ∙ ` x ∶ τ ⊣ Γ₁
  ---- Borrow ----
  ⊢borrow : ∀{Γ₀ q₀ e₀ τ₀ x* Γ₁} →
    ⌊ Γ₀ ⌋ x* ⊢ 𝟏 ∙ e₀ ∶ τ₀ ⊣ Γ₁ →
    -------------------------------------
    Γ₀ ⊢ q₀ ∙ [ x* ∣ e₀ ] ∶ τ₀ ⊣ ⌈ Γ₁ ⌉ x*
  ---- Bind ----
  ⊢let : ∀{Γ₀ Γ₁ Γ₂ q₀ x₀ e₀ τ₀ q e τ} →
    Γ₀ ⊢ q₀ ∙ e₀ ∶ τ₀ ⊣ Γ₁ →
    Γ₁ , q₀ ∙ x₀ ∶ τ₀ ⊢ q ∙ e ∶ τ ⊣ Γ₂ →
    ---------------------------------------------
    Γ₀ ⊢ q ∙ (val q₀ ∙ x₀ ＝ e₀ ⨾ e) ∶ τ ⊣ Γ₁ -- –¹ x₀ ?? Needed ??
  ---- Abstract ----
  ⊢abs-ε : ∀{Γ₀ Γ₁ n q∙x∶τⁿ e₀ τ₀} →
    Γ₀ / ε ∪ Γ₀ / ω ∪ⁿ n × q∙x∶τⁿ ⊢ 𝟏 ∙ e₀ ∶ τ₀ ⊣ Γ₁ →
    ----------------------------------------------------------------------
    Γ₀ ⊢ ε ∙ fn⟨ q∙x∶τⁿ ⟩ e₀ ∶ n × q∙x∶τⁿ ⟶ τ₀ ⊣ Γ₀ / 𝟏 ∪ Γ₁ –ⁿ n × names q∙x∶τⁿ
  ⊢abs-1 : ∀{Γ₀ Γ₁ n q∙x∶τⁿ e₀ τ₀} →
    Γ₀ / 𝟏 ∪ Γ₀ / ω ∪ⁿ n × q∙x∶τⁿ ⊢ 𝟏 ∙ e₀ ∶ τ₀ ⊣ Γ₁ →
    ----------------------------------------------------------------------
    Γ₀ ⊢ 𝟏 ∙ fn⟨ q∙x∶τⁿ ⟩ e₀ ∶ n × q∙x∶τⁿ ⟶ τ₀ ⊣ Γ₀ / ε ∪ Γ₁ –ⁿ n × names q∙x∶τⁿ
  ⊢abs-ω : ∀{Γ₀ Γ₁ n q∙x∶τⁿ e₀ τ₀} →
    Γ₀ / ω ∪ⁿ n × q∙x∶τⁿ ⊢ 𝟏 ∙ e₀ ∶ τ₀ ⊣ Γ₁ →
    -------------------------------------------------------------------------------
    Γ₀ ⊢ ω ∙ fn⟨ q∙x∶τⁿ ⟩ e₀ ∶ n × q∙x∶τⁿ ⟶ τ₀ ⊣ Γ₀ / ε ∪ Γ₀ / 𝟏 ∪ Γ₁ –ⁿ n × names q∙x∶τⁿ
  ---- Apply ----
  ⊢app-ε : ∀{Γ₀ Γ₁ Γₙ₊₁ e₀ τ₀ n eⁿ q∙x∶τⁿ} →
    Γ₀ ⊢ ε ∙ e₀ ∶ n × q∙x∶τⁿ ⟶ τ₀ ⊣ Γ₁ →
    Γ₁ ⊩ n × quantities q∙x∶τⁿ ∙ eⁿ ∶ types q∙x∶τⁿ ⊣ Γₙ₊₁ →
    -------------------------------------------------------
    Γ₀ ⊢ ε ∙ e₀ ⟨ eⁿ ⟩ ∶ τ₀ ⊣ Γₙ₊₁
  ⊢app-1 : ∀{Γ₀ Γ₁ Γₙ₊₁ e₀ τ₀ n eⁿ q∙x∶τⁿ} →
    Γ₀ ⊢ ε ∙ e₀ ∶ n × q∙x∶τⁿ ⟶ τ₀ ⊣ Γ₁ →
    Γ₁ ⊩ n × quantities q∙x∶τⁿ ∙ eⁿ ∶ types q∙x∶τⁿ ⊣ Γₙ₊₁ →
    -------------------------------------------------------
    Γ₀ ⊢ 𝟏 ∙ e₀ ⟨ eⁿ ⟩ ∶ τ₀ ⊣ Γₙ₊₁
  ⊢app-ω : ∀{Γ₀ Γ₁ Γₙ₊₁ e₀ τ₀ n eⁿ q∙x∶τⁿ} →
    Γ₀ ⊢ ε ∙ e₀ ∶ n × q∙x∶τⁿ ⟶ τ₀ ⊣ Γ₁ →
    Γ₁ ⊩ n × quantities q∙x∶τⁿ ∙ eⁿ ∶ types q∙x∶τⁿ ⊣ Γₙ₊₁ →
    -------------------------------------------------------
    Γ₀ ⊢ ω ∙ e₀ ⟨ eⁿ ⟩ ∶ τ₀ ⊣ Γₙ₊₁
  ---- Datatypes ----
  ⊢con : ∀{Δ Γ₁ Γₙ₊₁ n q C eⁿ q∙x∶τⁿ τ₀} →
    Δ ∋ C ∶ n × q∙x∶τⁿ ⟶ τ₀ →
    Γ₁ ⊩ n × (Vec.replicate n q) ∙ eⁿ ∶ types q∙x∶τⁿ ⊣ Γₙ₊₁ →
    ---------------------------------------------------------
    Γ₁ ⊢ q ∙ C ⟪ eⁿ ⟫ ∶ τ₀ ⊣ Γₙ₊₁
  ⊢mat : ∀{Δ Γ₀ Γ₀′ Γ₁ Γₘ₊₁ n m q C q₀ e₀ eⁿ C⟪xⁿ⟫↦eᵐ q∙x∶τⁿ τ τ₀} →
     Γ₀ ⊢ q₀ ∙ e₀ ∶ τ₀ ⊣ Γ₀′ →
     Γ₀′ ⊩→ m × q ∙ q₀ of C⟪xⁿ⟫↦eᵐ as τ₀ ∶ τ ⊣ Γₘ₊₁ →
     -----------------------------------------------
     Γ₀ ⊢ q ∙ match q₀ ∙ e₀ [ C⟪xⁿ⟫↦eᵐ ] ∶ τ ⊣ Γₘ₊₁
  -- ⊢mat : ∀{Δ Γ₀ Γ₁ Γₘ₊₁ n q C e₀ eⁿ C⟪xⁿ⟫↦eᵐ q∙x∶τⁿ τ τ₀} →
  --   Δ ∋ C ∶ n × q∙x∶τⁿ ⟶ τ₀ →
  --   Γ₁ ⊩ n × (Vec.replicate n q) ∙ eⁿ ∶ types q∙x∶τⁿ ⊣ Γₘ₊₁ →
  --   -----------------------------------------------
  --   Γ₀ ⊢ q ∙ match q ∙ e₀ [ C⟪xⁿ⟫↦eᵐ ] ∶ τ ⊣ Γₘ₊₁

data _⊩_×_∙_∶_⊣_ where
  ⊩empty : ∀{Γ₀} →
    -------------------------
    Γ₀ ⊩ 0 × [] ∙ [] ∶ [] ⊣ Γ₀
  ⊩rest : ∀{Γ₀ Γ₁ Γₙ₊₁ n q₀ e₀ τ₀ τ₀' qⁿ eⁿ τⁿ} →
    Γ₀ ⊢ q₀ ∙ e₀ ∶ τ₀' ⊣ Γ₁ →
    τ₀' ≡ τ₀ →
    Γ₀ ∩ Γ₁ ⊩ n × qⁿ ∙ eⁿ ∶ τⁿ ⊣ Γₙ₊₁ →
    -----------------------------------------------
    Γ₀ ⊩ suc n × q₀ ∷ qⁿ ∙ e₀ ∷ eⁿ ∶ τ₀ ∷ τⁿ ⊣ Γₙ₊₁

combine : {n : ℕ} → Quantity → Name ^ n → Parameter ^ n → Parameter ^ n
combine {0} q₀ [] [] = []
combine {suc n} q₀ (x₀ ∷ xⁿ) (_ ∙ _ ∶ τ₀ ∷ _∙_∶τⁿ) = q₀ ∙ x₀ ∶ τ₀ ∷ combine q₀ xⁿ _∙_∶τⁿ

data _⊩→_×_∙_of_as_∶_⊣_ where
  ⊩→empty : ∀{Γ₀ q q₀ τ₀ τ} →
    --------------------------
    Γ₀ ⊩→ 0 × q ∙ q₀ of [] as τ₀ ∶ τ ⊣ Γ₀
  ⊩→rest : ∀{Δ Γ₀ Γ₁ Γₘ₊₁ m n q q₀ C₀ e₀ τ₀ xⁿ τⁿ C⟪xⁿ⟫↦eᵐ τ} →
    Δ ∋ C₀ ∶ n × τⁿ ⟶ τ₀ →
    Γ₀ ∪ⁿ n × combine q₀ xⁿ τⁿ ⊢ q ∙ e₀ ∶ τ ⊣ Γ₁ →
    Γ₀ ⊩→ m × q ∙ q₀ of C⟪xⁿ⟫↦eᵐ as τ₀ ∶ τ ⊣ Γₘ₊₁ → -- Note: we're using the same Γ₀ and q₀ here!
    -------------------------------------------------------------------------
    Γ₀ ⊩→ suc m × q ∙ q₀ of C₀ ⟪ n × xⁿ ⟫↦ e₀ ∷ C⟪xⁿ⟫↦eᵐ as τ₀ ∶ τ ⊣ Γ₁ ∩ Γₘ₊₁ -- Todo: is ∩ enough here?
```
