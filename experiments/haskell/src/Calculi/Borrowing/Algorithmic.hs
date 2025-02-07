module Calculi.Borrowing.Algorithmic where

import Data.Map.Strict qualified as Map
import Data.Text qualified as Text

type Name = Text

data Exp
  = Var Name
  | Borrow Name Exp
  | Abs Name Quant Typ Exp
  | App Exp Exp
  | Pair Exp Exp
  | Split Quant Exp Name Name Exp
  | Inject Ctor Exp
  | Match Quant Exp Exp Exp
  deriving (Eq, Ord, Debug)

data Ctor
  = L
  | R
  deriving (Eq, Ord, Debug)

data Quant
  = Zero
  | Epsilon
  | One
  | Omega
  deriving (Eq, Ord, Debug)

data Typ
  = (:->) (Typ, Quant) Typ
  | (:*) Typ Typ
  | (:+) Typ Typ
  | Base
  deriving (Eq, Ord, Debug)

type Context = Map Name (Quant, Typ)

data Error
  = VarDoesntExist Name
  | VarMismatch Quant Quant Name
  | FunNeeded Typ
  | ArgMismatch Typ Typ
  | NoWeakening
  deriving (Eq, Ord, Debug)

instance Display Typ where
  display = \case
    (t, q) :-> r -> mconcat [display t, "^", display q, " -> ", display r]
    t1 :* t2 -> unwords [display t1, "*", display t2]
    t1 :+ t2 -> unwords [display t1, "+", display t2]
    Base -> "B"

instance Display Quant where
  display = \case
    Zero -> "gone"
    Epsilon -> "borrowed"
    One -> "linear"
    Omega -> "unrestricted"

instance Display Error where
  display = \case
    VarDoesntExist x -> unwords ["variable", x, "does not exist"]
    VarMismatch q_asked q_provided x -> unwords ["variable", x, "is asked for", display q_asked, "but it is", display q_provided]
    FunNeeded t -> unwords ["type", show t, "is not a function type"]
    ArgMismatch t_asked t_provided -> unwords ["argument needs to be of type", debug t_asked, "but", debug t_provided, "is given"]
    NoWeakening -> "cannot apply weakening"

-- = VarGone Name
-- \| VarLinear Name
-- \| VarBorrowed Name
-- \| VarUnrestricted Name

synthesize :: Context -> Exp -> Quant -> Either Error (Typ, Context)
synthesize = go
  where
    -- synthesize g_ e_ q_ =case go g_ e_ q_ of
    --   Right r -> Right r
    --   Wrong _ -> case weaken g_ e_ q_ of
    --     Right r -> Right r
    --     Wrong _ -> case borrow g_ e_ q_ of
    --       Right r -> Right r
    --       Wrong x -> Wrong x
    ---- Variables ----
    go :: Context -> Exp -> Quant -> Either Error (Typ, Context)
    go _ (Var n) Zero = Wrong <| VarMismatch Zero One n
    go g (Var n) Epsilon =
      case Map.lookup n g of
        Nothing -> Wrong <| VarDoesntExist n
        Just (Epsilon, t) -> Right <| (t, g)
        Just (q, _) -> Wrong <| VarMismatch Epsilon q n
    -- Just (Zero, t) -> Wrong <| VarGone n
    -- Just (One, t) -> Wrong <| VarLinear n
    -- Just (Omega, t) -> Wrong <| VarUnrestricted n
    go g (Var n) One =
      case Map.lookup n g of
        Nothing -> Wrong <| VarDoesntExist n
        Just (One, t) -> Right <| (t, Map.insert n (Zero, t) g)
        Just (Omega, t) -> Right <| (t, g) -- FIXME: built-in weakening
        Just (q, _) -> Wrong <| VarMismatch One q n
    -- Just (Zero, t) -> Wrong <| VarGone n
    -- Just (Epsilon, t) -> Wrong <| VarBorrowed n
    go g (Var n) Omega =
      case Map.lookup n g of
        Nothing -> Wrong <| VarDoesntExist n
        Just (Omega, t) -> Right <| (t, g)
        Just (q, _) -> Wrong <| VarMismatch Omega q n
    -- Just (Zero, t) -> Wrong <| VarGone n
    -- Just (Epsilon, t) -> Wrong <| VarBorrowed n
    -- Just (One, t) -> Wrong <| VarLinear n
    go g (Borrow n e) q =
      case go (Map.adjust (\(_, t) -> (Epsilon, t)) n g) e q of
        Right (t, _) -> Right (t, g) -- NOTE: Continue with old context
        Wrong x -> Wrong x
    ---- Functions ----
    go g (Abs x1 q1 t1 e) _ =
      go (Map.insert x1 (q1, t1) g) e One -- FIXME: remove x1!
    go g (App e0 e1) q =
      case go g e0 q of -- FIXME: ok to pass on q?
        Right ((t1, q1) :-> t0, g') ->
          case go g' e1 q1 of
            Right (t1', g'') ->
              if t1 == t1'
                then Right (t0, g'')
                else Wrong <| ArgMismatch t1 t1'
            Wrong x -> Wrong x
        Right (t', _) -> Wrong <| FunNeeded t'
        Wrong x -> Wrong x
    ---- Products ----
    go g (Pair e1 e2) _ =
      case go g e1 One of
        Wrong x -> Wrong x
        Right (t1, g') -> case go g' e2 One of
          Wrong x -> Wrong x
          Right (t2, g'') -> Right (t1 :* t2, g'')
    ---- Sums ----
    go _ _ _ = error "todo"

    ---- Weakening ----
    weaken :: Context -> Exp -> Quant -> Either Error (Typ, Context)
    weaken g e One = go g e Omega
    weaken _ _ _ = Wrong <| NoWeakening

    ---- Borrowing ----
    borrow :: Context -> Exp -> Quant -> Either Error (Typ, Context)
    borrow g e q = case go (Map.map (\(_, t) -> (Epsilon, t)) g) e q of -- FIXME: to harsh...
      Right (t, _) -> Right (t, g) -- NOTE: Continue with old context
      Wrong x -> Wrong x

run :: Exp -> Either Error (Typ, Context)
run e =
  synthesize Map.empty e One

id_ :: Quant -> Exp
id_ q = Abs "x" q Base <| Var "x"

dup_ :: Quant -> Exp
dup_ q = Abs "x" q Base <| Pair (Var "x") (Var "x")

call_ :: Quant -> Quant -> Exp
call_ q0 q1 = Abs "g" Omega ((Base, q1) :-> Base) <| Abs "x" q0 Base <| App (Var "g") (Var "x")

callE_ :: Quant -> Exp
callE_ q0 = Abs "g" Omega ((Base, Epsilon) :-> Base) <| Abs "x" q0 Base <| App (Var "g") (Borrow "x" (Var "x"))

escape_ :: Exp
escape_ = Abs "x" Epsilon Base <| Abs "y" One Base <| Pair (Var "x") (Var "y")

{-
let
go n (q, t) = _
(mqt, g') = Map.updateLookupWithKey go x g
in case mqt of
  Just (_, t) -> Right $ (t, g')
  Nothing -> Err $
-}

---- Helpers -------------------------------------------------------------------

type Debug = Show

debug :: (Debug a) => a -> Text
debug = show

-- intercalate :: (Foldable f, Monoid m) => m -> f m -> m
-- intercalate sep = foldl' go (True, neutral) >> snd
--   where
--     go (True, _) x = (False, x)
--     go (st, acc) x = (st, acc ++ sep ++ x)
-- {-# INLINE intercalate #-}

class Display a where
  display :: a -> Text

between :: Char -> Char -> Text -> Text
between a b t = a `Text.cons` t `Text.snoc` b

instance Display () where
  display () = "()"

instance Display Bool where
  display = debug

instance Display Nat where
  display = debug

instance Display Int where
  display n
    | n >= 0 = "+" <> debug n
    | otherwise = debug n

instance Display Double where
  display = debug

instance Display Char where
  display = Text.singleton

instance Display Text where
  display = identity

instance (Display a) => Display (Maybe a) where
  display = \case
    Nothing -> ""
    Just v -> display v

instance (Display e, Display a) => Display (Either e a) where
  display = \case
    Left e -> "Error: " <> display e
    Right a -> display a

instance (Display a, Display b) => Display (a, b) where
  display (a, b) = display a <> ", " <> display b |> between '(' ')'

instance (Display a) => Display [a] where
  display = fmap display .> intersperse "," .> unwords .> between '[' ']'

instance (Display k, Display v) => Display (Map k v) where
  display = Map.toList .> fmap (\(k, v) -> display k <> ": " <> display v) .> intersperse "," .> unwords .> between '{' '}'

{-# COMPLETE Right, Wrong #-}

pattern Wrong :: a -> Either a b
pattern Wrong e = Left e

infixr 0 <|

infixl 1 |>

infixr 9 <.

infixr 9 .>

(<.) :: (b -> c) -> (a -> b) -> a -> c
f <. g = \x -> f (g x)

(<|) :: (a -> b) -> a -> b
f <| x = f x

(.>) :: (a -> b) -> (b -> c) -> a -> c
f .> g = \x -> g (f x)

(|>) :: a -> (a -> b) -> b
x |> f = f x