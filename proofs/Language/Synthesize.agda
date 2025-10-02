module Language.Synthesize where

open import Prelude

open import Language.Judgement

-- Note: all `yes` cases below prove soundness, all `no` cases completeness

synthesize? :
  (Γ : Context) → (q : Quantity) → (e : Expression) →
  ---------------------------------------------------
  Dec (∃[ τ ] ∃[ Γ′ ] Γ ⊢ q ∙ e ∶ τ ⊣ Γ′)
synthesizeˢ? :
  (Γ : Context) → (n : ℕ) → (qⁿ : Quantity ^ n) → (eⁿ : Expression ^ n) → (τⁿ : Type ^ n) →
  ------------------------------------------------------------------------------------------
  Dec (∃[ Γ′ ] Γ ⊩ n × qⁿ ∙ eⁿ ∶ τⁿ ⊣ Γ′)
synthesizeᵇ? :
  (Γ₀ : Context) → (m : ℕ) → (q : Quantity) → (q₀ : Quantity) → (C⟪xⁿ⟫↦eᵐ : Branch ^ m) → (τ₀ : Type) →
  -----------------------------------------------------------------------------------------------------
  Dec (∃[ τ ] ∃[ Γₘ₊₁ ] Γ₀ ⊩→ m × q ∙ q₀ of C⟪xⁿ⟫↦eᵐ as τ₀ ∶ τ ⊣ Γₘ₊₁)

synthesize? Γ q (` x) with lookup? Γ q x
... | yes (τ , Γ′ , ∋x) = yes (τ , Γ′ , ⊢var ∋x)
... | no ¬∋x = no λ where (τ , Γ′ , ⊢var ∋x) → ¬∋x (τ , Γ′ , ∋x)
synthesize? Γ q (val q₀ ∙ x₀ ＝ e₀ ⨾ e₁) = {!   !}
synthesize? Γ q ([ x* ∣ e₀ ]) = {!   !}
synthesize? Γ q (fn⟨ q∙x∶τⁿ ⟩ e₀) = {!   !}
synthesize? Γ q (e₀ ⟨ eⁿ ⟩ ) = {!   !}
synthesize? Γ q (C ⟪ eⁿ ⟫) = {!   !}
synthesize? Γ q (match q₀ ∙ e₀ [ C⟪xⁿ⟫↦eᵐ ]) = {!   !}

synthesizeˢ? Γ₀ 0 [] [] [] = yes (Γ₀ , ⊩empty)
synthesizeˢ? Γ₀ (suc n) (q₀ ∷ qⁿ) (e₀ ∷ eⁿ) (τ₀ ∷ τⁿ) with synthesize? Γ₀ q₀ e₀
... | yes (τ₀′ , Γ₁ , ⊢q₀∙e₀∶τ₀) with τ₀ Type.≟ τ₀′
...   | yes refl = {!   !}
...   | no ¬τ₀≡τ₀′ = {!   !}
... | no ¬p =  {!   !}

synthesizeᵇ? Γ₀ m q q₀ C⟪xⁿ⟫↦eᵐ τ₀ = {!   !}

synthesize : (Γ : Context) → (q : Quantity) → (e : Expression) → String ∨ Type
synthesize Γ q e with synthesize? Γ q e
... | yes (τ , _) = right τ
... | no _ = wrong "Type error"