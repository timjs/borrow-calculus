module Algorithmic

import Data.SortedMap

%default total

Name : Type
Name = String

data Quant
  = Zero
  | Epsilon
  | One
  | Omega

data Ctor
  = L
  | R

data Typ
  = (:->) Typ Quant  Typ
  | (:*) Typ Typ
  | (:+) Typ Typ

data Exp
  = Var Name
  | Fun Name Quant Typ Exp
  | App Exp Exp
  | Pair Exp Exp
  | Split Quant Exp Name Name Exp
  | Inject Ctor Exp
  | Match Quant Exp Exp Exp

Context : Type
Context = SortedMap Name Typ

data Error
  =

synthesise : Context -> Exp -> Quant -> Either Error (Typ, Context)
synthesise g (Var str) Zero = ?synthesise_rhs_7
synthesise g (Var str) Epsilon = ?synthesise_rhs_8
synthesise g (Var str) One = ?synthesise_rhs_9
synthesise g (Var str) Omega = ?synthesise_rhs_10synthesise g (Fun str x y z) q = ?synthesise_rhs_1
synthesise g (App x y) q = ?synthesise_rhs_2
synthesise g (Pair x y) q = ?synthesise_rhs_3
synthesise g (Split x y str str1 z) q = ?synthesise_rhs_4
synthesise g (Inject x y) q = ?synthesise_rhs_5
synthesise g (Match x y z w) q = ?synthesise_rhs_6