module Experiments where

open import Prelude

_⊕_ : {n : ℕ} → ℕ → ℕ → ℕ
_⊕_ {n} a b = a + b + n -- ok!
-- a ⊕ b = a + b + n -- n not in scope

-- use-⊕ : _⊕_ {1} 2 3 ≡ 6 -- ok!
use-⊕ : 2 (_⊕_ {1}) 3  ≡ 6
use-⊕ = refl
