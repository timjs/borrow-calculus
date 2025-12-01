module Prelude where


---- Opened -----

open import Data.Bool using (true; false; T; not; if_then_else_) renaming (Bool to 𝔹) public
open import Data.Empty using (⊥; ⊥-elim) public
open import Data.Integer using (ℤ)
open import Data.Sum using () renaming (_⊎_ to _∨_; inj₁ to wrong; inj₂ to right) public
open import Data.Irrelevant using (Irrelevant) public
open import Data.List using (_∷_; []) renaming (List to _*) public
open import Data.List.NonEmpty using (_∷_) renaming (List⁺ to _+)
open import Data.Maybe using (Maybe; just; nothing) public
open import Data.Nat using (ℕ; zero; suc; _≤ᵇ_; _+_) public
open import Data.Product using (Σ-syntax; ∃-syntax; _,_) renaming (_×_ to _∧_; proj₁ to fst; proj₂ to snd) public
open import Data.String using (String) public
open import Data.Unit using (⊤) renaming (tt to ⟨⟩) public
open import Data.Vec using (_∷_; []) renaming (Vec to _^_) public

open import Function using (_∘_; _|>_; case_of_) public

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong) public
open import Relation.Binary.PropositionalEquality.Properties using (isDecEquivalence) public
open import Relation.Nullary.Decidable using (Dec; yes; no; True; False; ¬?) renaming (⌊_⌋ to ∥_∥) public
open import Relation.Nullary.Negation using (¬_; contradiction) public


---- Qualified ----

-- Note that this only works because `String` is not a datatype but a postulate
-- and we renamed `List` to `_*`, `NonEmpty` to `_+` and `Vec` to `_^_`
-- so that we don't have clashing names on the module plane.
module String = Data.String
module List = Data.List
module NonEmpty = Data.List.NonEmpty
module Vec = Data.Vec
module Int = Data.Integer
module Nat = Data.Nat


--- Instanced ----

open import Relation.Binary.Definitions using (Decidable)
open import Relation.Binary.Structures using (IsDecEquivalence; IsDecTotalOrder)
open import Relation.Binary.TypeClasses public

open import Data.Bool.Instances public
open import Data.Char.Instances public
open import Data.Float.Instances public
open import Data.Integer.Instances public
open import Data.List.Instances public
open import Data.List.NonEmpty.Instances public
open import Data.Maybe.Instances public
open import Data.Nat.Instances public
open import Data.Product.Instances public
open import Data.String.Instances public
open import Data.Sum.Instances public
open import Data.Unit.Instances public
open import Data.Vec.Instances public


---- Additional ----

open import Level using (_⊔_)

infixr 12  _×_

-- Just normal `Vec`tors, but with an explicit length
_×_ : ∀{a} → {A : Set a} → (n : ℕ) → A ^ n → A ^ n
n × xⁿ = xⁿ

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
