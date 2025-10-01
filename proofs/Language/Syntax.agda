module Language.Syntax where

open import Language.Syntax.Name public
open import Language.Syntax.Quantity public
open import Language.Syntax.Type public
open import Language.Syntax.Expression public

-- Note that this doesn't work, because we have a type `Quantity` defined
-- which is also a module...
-- import Language.Syntax.Quantity; module Quantity = Language.Syntax.Qualified
