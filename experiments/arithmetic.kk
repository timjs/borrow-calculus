module calculi/borrowing/arithmetic

pub alias name = string

pub type expression
  Var(name: name)
  Fun(parameter: name, quantity: quantity, type_: type_, body: expression)
  App(applicant: expression, argument: expression)
  Pair(first: expression, second: expression)
  Split(scrutiny: expression, quantity: quantity, fst: name, snd: name, body: expression)
  Inject(constructor: constructor, body: expression)
  Match(scrutiny: expression, quantity: quantity, left: expression, right: expression)

pub type constructor
  Left
  Right

pub type quantity
  Zero
  Epsilon
  One
  Omega

pub type type_
  Arrow(parameter: type_, quantity: quantity, result: type_)
  Product(first: type_, second: type_)
  Sum(left: type_, right: type_)
