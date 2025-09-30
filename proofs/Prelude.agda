module Prelude where

---- Opened -----

open import Data.Bool.Base using (true; false; T; not; if_then_else_) renaming (Bool to 𝔹) public
open import Data.Empty using (⊥; ⊥-elim) public
open import Data.Integer.Base using (ℤ)
open import Data.Sum.Base using () renaming (_⊎_ to _∨_; inj₁ to left; inj₂ to right) public
open import Data.Irrelevant using (Irrelevant) public
open import Data.List.Base using (_∷_; []) renaming (List to _*) public
open import Data.List.NonEmpty.Base using (_∷_) renaming (List⁺ to _+)
open import Data.Maybe using (Maybe; just; nothing) public
open import Data.Nat.Base using (ℕ; zero; suc; _≤ᵇ_; _+_) public
open import Data.Product.Base using (Σ-syntax; ∃-syntax; _,_) renaming (_×_ to _∧_; proj₁ to fst; proj₂ to snd) public
open import Data.String using (String) public
open import Data.Unit.Base using (⊤) renaming (tt to ⟨⟩) public
open import Data.Vec.Base using (_∷_; []) renaming (Vec to _^_) public

open import Function.Base using (_∘_; _|>_; case_of_) public

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong) public
open import Relation.Nullary.Decidable.Core using (Dec; yes; no; True; False; ¬?) renaming (⌊_⌋ to ∥_∥) public
open import Relation.Nullary.Negation using (¬_; contradiction) public

---- Qualified ----

import Data.List
module List = Data.List
import Data.Vec
module Vec = Data.Vec

--

open import Level using (_⊔_)

-- Our own definition of quotients/refinements
-- to use reuse common constructor `_,_` of Σ-types.
-- (Otherwise e get "Cannot split on argument of unresolved type" errors
--  on pattern matching `with`-blocks...)
-- TODO: make issue?
_//_ : ∀ {ℓ₁ ℓ₂} → (A : Set ℓ₁) → (P : A → Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
A // P = Σ[ x ∈ A ] (Irrelevant (P x))

{-
  left≢right : ∀ {ℓ} {A B : Set ℓ} {x : A} {y : B} → left x ≢ right y
  left≢right ()

  data IsRight {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} : A ⊎ B → Set (ℓ₁ ⊔ ℓ₂) where
    is-right : ∀ {x} →
      --------------------
      IsRight (right x)

  is-it-right? : ∀ {ℓ} {A B : Set ℓ} → (v : A ⊎ B) → Dec (IsRight v)
  is-it-right? (right _) = yes is-right
  is-it-right? (left  _) = no λ ()

-}
